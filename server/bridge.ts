// The bridge: every command runs twice, once on the proven Bend model and
// once on the real TigerBeetle, and the two answers are compared. The Bend
// side decides *what* to do (the chain of transfers, via boxoffice.bend);
// this file only translates that chain into TigerBeetle's wire format.
//
// Nothing in this file is proven. It is the "trusted shell": the id
// encoding, the flag translation and the status mapping below are exactly
// the kind of code the laws cannot see, which is why the cross-check exists.

import {
  AccountFlags,
  amount_max,
  createClient,
  TransferFlags,
  type Account,
  type Client,
  type Transfer,
} from "tigerbeetle-node";

import L from "../core/ledger.bend";
import B from "../core/boxoffice.bend";

// Bend values in JS
// =================
// A constructor is {$: "Name", ...fields}, Nat is BigInt, Bool is boolean.

export type Bend = { $: string; [k: string]: any };

export const list = <T>(xs: T[]): Bend =>
  xs.reduceRight<Bend>((t, h) => ({ $: "Con", head: h, tail: t }), { $: "Nil" });

export const arr = (l: Bend): any[] => {
  const out: any[] = [];
  while (l.$ === "Con") {
    out.push(l.head);
    l = l.tail;
  }
  return out;
};

// Ids
// ===
// The model's accounts are typed (Seat{k}, Wallet{u}, ...). TigerBeetle's
// are u128s. The encoding puts a tag in the upper bits; it is injective by
// inspection, not by proof.

const TAG = 1n << 32n;

export function enc(id: Bend): bigint {
  switch (id.$) {
    case "Bank": return 1n;
    case "Venue": return 2n;
    case "Issuer": return 3n;
    case "Seat": return 1n * TAG + id.k;
    case "Wallet": return 2n * TAG + id.u;
    case "Tickets": return 3n * TAG + id.u;
  }
  throw new Error(`unknown account ${id.$}`);
}

export function idName(id: Bend): string {
  switch (id.$) {
    case "Seat": return `Seat{${id.k}}`;
    case "Wallet": return `Wallet{${id.u}}`;
    case "Tickets": return `Tickets{${id.u}}`;
    default: return id.$;
  }
}

function account(id: Bend): Account {
  return {
    id: enc(id),
    debits_pending: 0n,
    debits_posted: 0n,
    credits_pending: 0n,
    credits_posted: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    reserved: 0,
    ledger: Number(L.ledger_of(id)),
    code: 1,
    flags: L.guarded(id) ? AccountFlags.debits_must_not_exceed_credits : 0,
    timestamp: 0n,
  };
}

// Transfers
// =========

export type Options = { holdTimeout: number };

function transfer(op: Bend, linked: boolean, opts: Options): Transfer {
  const base = {
    id: op.id as bigint,
    debit_account_id: 0n,
    credit_account_id: 0n,
    amount: 0n,
    pending_id: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    timeout: 0,
    ledger: 0,
    code: 0,
    flags: linked ? TransferFlags.linked : 0,
    timestamp: 0n,
  };
  switch (op.$) {
    case "Create":
      return {
        ...base,
        debit_account_id: enc(op.dr),
        credit_account_id: enc(op.cr),
        amount: op.amt,
        ledger: Number(L.ledger_of(op.dr)),
        code: 1,
        timeout: op.pending ? opts.holdTimeout : 0,
        flags: base.flags | (op.pending ? TransferFlags.pending : 0),
      };
    case "Post":
      return { ...base, pending_id: op.pid, amount: amount_max, flags: base.flags | TransferFlags.post_pending_transfer };
    case "Void":
      return { ...base, pending_id: op.pid, flags: base.flags | TransferFlags.void_pending_transfer };
  }
  throw new Error(`unknown op ${op.$}`);
}

export function describe(op: Bend): string {
  switch (op.$) {
    case "Create":
      return `#${op.id} ${idName(op.dr)} → ${idName(op.cr)} ${op.amt}${op.pending ? " pending" : ""}`;
    case "Post":
      return `#${op.id} post #${op.pid}`;
    case "Void":
      return `#${op.id} void #${op.pid}`;
  }
  return op.$;
}

// TigerBeetle result codes, named as the model names them. Codes the
// model has no counterpart for keep their TigerBeetle name, so they show
// up as disagreements.
const STATUS: Record<number, string> = {
  4294967295: "Ok",
  1: "LinkedFailed",
  12: "SameAccounts",
  21: "DebitNotFound",
  22: "CreditNotFound",
  23: "LedgerMismatch",
  46: "Exists",
  36: "Exists", 37: "Exists", 38: "Exists", 39: "Exists", 40: "Exists",
  44: "Exists", 45: "Exists", 67: "Exists",
  54: "ExceedsCredits",
  25: "PendingNotFound",
  26: "NotPending",
  33: "AlreadyPosted",
  34: "AlreadyVoided",
  35: "pending_transfer_expired",
  68: "id_already_failed",
};

const statusName = (code: number) => STATUS[code] ?? `tigerbeetle_status_${code}`;

// The engine
// ==========

export type Outcome = {
  ops: string[];
  model: string[];
  tb: string[];
  agree: boolean;
  balances: string[]; // accounts whose balances disagree after the command
};

export class Engine {
  model: Bend = L.empty();
  tb: Client;
  opts: Options;
  commands = 0;
  agreed = 0;
  disagreements: { what: string; outcome: Outcome }[] = [];
  lastOps: Bend[] = [];
  private queue: Promise<unknown> = Promise.resolve();

  constructor(address: string, opts: Options) {
    this.tb = createClient({ cluster_id: 0n, replica_addresses: [address] });
    this.opts = opts;
  }

  // one command at a time, so the model and the database see one order
  private serial<T>(f: () => Promise<T>): Promise<T> {
    const p = this.queue.then(f, f);
    this.queue = p.catch(() => {});
    return p;
  }

  async init(): Promise<Outcome> {
    const found = await this.tb.lookupAccounts([enc({ $: "Bank" })]);
    if (found.length > 0) {
      throw new Error(
        "TigerBeetle already holds data from an earlier run. The model starts from opening day, " +
        "so it needs a fresh data file: stop everything and run ./scripts/dev.sh again (it reformats).",
      );
    }
    const house = B.house();
    await this.openAccounts(arr(L.accts(house)));
    const ops = arr(B.issue(B.seat_count()));
    const r = L.chain(house, list(ops));
    return this.serial(() => this.apply(ops, r, "opening day"));
  }

  private async openAccounts(ids: Bend[]) {
    if (ids.length === 0) return;
    const res = await this.tb.createAccounts(ids.map(account));
    for (const r of res) {
      if (r.status !== 4294967295 && r.status !== 21 /* exists */) {
        throw new Error(`createAccounts failed with status ${r.status}`);
      }
    }
  }

  // run a box-office command on both sides
  run(cmd: Bend, what: string, opts?: Partial<Options>): Promise<Outcome> {
    return this.serial(async () => {
      const opened = B.opens(this.model, cmd);
      const fresh = arr(L.accts(opened)).filter(
        (a) => !arr(L.accts(this.model)).some((b) => L["Id.eq"](a, b)),
      );
      await this.openAccounts(fresh);
      const ops = arr(B.plan(opened, cmd));
      return this.apply(ops, B.step(this.model, cmd), what, opts);
    });
  }

  // resend the last chain, same ids and all
  retry(what: string): Promise<Outcome> {
    return this.serial(async () => {
      const ops = this.lastOps;
      return this.apply(ops, L.chain(this.model, list(ops)), what);
    });
  }

  private async apply(ops: Bend[], stepped: Bend, what: string, over?: Partial<Options>): Promise<Outcome> {
    const opts = { ...this.opts, ...over };
    this.model = stepped.fst;
    const model = arr(stepped.snd).map((s: Bend) => s.$);
    let tb: string[] = [];
    if (ops.length > 0) {
      const res = await this.tb.createTransfers(ops.map((op, i) => transfer(op, i < ops.length - 1, opts)));
      tb = res.map((r) => statusName(r.status));
    }
    if (ops.length > 0) this.lastOps = ops;
    const balances = await this.compareBalances();
    const agree = model.length === tb.length && model.every((s, i) => s === tb[i]) && balances.length === 0;
    const outcome = { ops: ops.map(describe), model, tb, agree, balances };
    this.commands++;
    if (agree) this.agreed++;
    else this.disagreements.unshift({ what, outcome });
    return outcome;
  }

  // every account's four balances, model against database
  private async compareBalances(): Promise<string[]> {
    const ids = arr(L.accts(this.model));
    const rows = await this.tb.lookupAccounts(ids.map(enc));
    const byId = new Map(rows.map((r) => [r.id, r]));
    const log = L.log(this.model);
    const bad: string[] = [];
    for (const id of ids) {
      const t = byId.get(enc(id));
      if (!t) {
        bad.push(`${idName(id)}: missing in TigerBeetle`);
        continue;
      }
      const m = {
        debits: L.debits(id, log) as bigint,
        dposted: L.dposted(id, log) as bigint,
        cposted: L.cposted(id, log) as bigint,
        cpending: L.cpending(id, log) as bigint,
      };
      if (
        t.debits_pending + t.debits_posted !== m.debits ||
        t.debits_posted !== m.dposted ||
        t.credits_posted !== m.cposted ||
        t.credits_pending !== m.cpending
      ) {
        bad.push(
          `${idName(id)}: model dr ${m.debits} (posted ${m.dposted}) cr ${m.cposted} (+${m.cpending} pending); ` +
          `TigerBeetle dr ${t.debits_pending + t.debits_posted} (posted ${t.debits_posted}) cr ${t.credits_posted} (+${t.credits_pending} pending)`,
        );
      }
    }
    return bad;
  }
}
