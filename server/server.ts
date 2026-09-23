// The HTTP shell: sessions, Datastar's SSE stream, and the hold timers.
// Decisions (what a command does, whether it is allowed) and every piece
// of HTML that shows a visitor's name come from the Bend core.

import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join } from "node:path";

import B from "../core/boxoffice.bend";
import V from "../core/view.bend";
import H from "../core/html.bend";
import { arr, list, Engine, type Bend, type Outcome } from "./bridge.ts";

const ROOT = join(import.meta.dir, "..");
const PORT = Number(process.env.PORT ?? 3000);
const TB_ADDRESS = process.env.TB_ADDRESS ?? "3001";
const HOLD_SECS = Number(process.env.HOLD_SECS ?? 60);
const BEND = process.env.BEND_MAIN ?? join(ROOT, ".tools/bend/bend2/main.ts");

// Proofs, checked at boot
// =======================
// The server re-runs the checker on the laws it ships with, and shows the
// result on the page. The laws are read from LAWS.bend itself.

type Law = { name: string; says: string };

function readLaws(): Law[] {
  const src = readFileSync(join(ROOT, "core/LAWS.bend"), "utf8").split("\n");
  const laws: Law[] = [];
  let says: string[] = [];
  for (const line of src) {
    const m = line.match(/^law (\w+):/);
    if (m) {
      laws.push({ name: m[1], says: says.join(" ").replace(/^LAW:\s*/, "") });
      says = [];
    } else if (line.startsWith("# ")) {
      says.push(line.slice(2));
    } else if (line.trim() === "") {
      says = [];
    }
  }
  return laws;
}

function checkProofs() {
  const t0 = performance.now();
  const r = spawnSync("bun", [BEND, join(ROOT, "core/PROOF.bend")], { encoding: "utf8" });
  const ms = Math.round(performance.now() - t0);
  const out = (r.stdout + r.stderr).trim();
  return { ok: r.status === 0 && out.includes("All terms check."), ms, out };
}

const laws = readLaws();
const proof = checkProofs();
console.log(`proofs: ${proof.ok ? "all laws hold" : "FAILED"} (${proof.ms} ms)`);
if (!proof.ok) console.log(proof.out);

// State
// =====

const engine = new Engine(TB_ADDRESS, { holdTimeout: HOLD_SECS + 30 });

type Session = { u: bigint; name: string };
type Hold = { u: bigint; k: bigint; t2: bigint; deadline: number; manual: boolean };
type Client = { u: bigint; send: (chunk: string) => void };
type FeedItem = { time: string; who: string; what: string; outcome?: Outcome; note?: string };

const sessions = new Map<string, Session>();
const holds = new Map<bigint, Hold>(); // by the seat leg's transfer id
const clients = new Set<Client>();
const feed: FeedItem[] = [];
let nextUser = 1n;
let nextId = 1000n; // opening day uses 1..12
const fresh = () => nextId++;

const nameOf = (u: bigint) => [...sessions.values()].find((s) => s.u === u)?.name ?? `Guest ${u}`;
const names = () => list([...sessions.values()].map((s) => ({ $: "Named", u: s.u, name: s.name })));
const clock = () => new Date().toLocaleTimeString("en-GB", { hour12: false });

function log(who: string, what: string, outcome?: Outcome, note?: string) {
  feed.unshift({ time: clock(), who, what, outcome, note });
  feed.length = Math.min(feed.length, 14);
}

// Rendering
// =========
// Seats, wallet and holds are rendered by view.bend. The panels below are
// rendered here, and every visitor name in them goes through H.text, the
// escaper LAWS.bend proves clean. Nothing *forces* this file to call it:
// that is one of the limits the page lists.

const esc = (s: string): string => H.text(s);

function statusChips(xs: string[]) {
  if (xs.length === 0) return `<span class="chip none">no transfers</span>`;
  return xs.map((s) => `<span class="chip ${s === "Ok" ? "ok" : "no"}">${esc(s)}</span>`).join("");
}

function feedHtml() {
  const rows = feed.map((f) => {
    const o = f.outcome;
    const verdict = !o ? "" : o.agree
      ? `<span class="agree" title="model and TigerBeetle agree">✓ agree</span>`
      : `<span class="disagree" title="model and TigerBeetle disagree">✗ disagree</span>`;
    const detail = !o ? "" : `
      <div class="detail">
        ${o.ops.length ? `<div class="ops">${o.ops.map((x) => `<code>${esc(x)}</code>`).join("")}</div>` : ""}
        <div class="pair"><span class="side">Bend model</span>${statusChips(o.model)}</div>
        <div class="pair"><span class="side">TigerBeetle</span>${statusChips(o.tb)}</div>
        ${o.balances.length ? `<div class="bal-diff">${o.balances.map((b) => `<div>${esc(b)}</div>`).join("")}</div>` : ""}
      </div>`;
    return `<li class="${o && !o.agree ? "bad" : ""}"><div class="line"><time>${f.time}</time> <b>${esc(f.who)}</b> ${esc(f.what)} ${verdict}</div>
      ${f.note ? `<div class="note">${esc(f.note)}</div>` : ""}${detail}</li>`;
  });
  return `<ol id="feed">${rows.join("") || `<li class="empty">Nothing yet.</li>`}</ol>`;
}

function checkHtml() {
  const bad = engine.commands - engine.agreed;
  return `<div id="check" class="${bad ? "bad" : "good"}">
    <div class="big">${engine.agreed}<small>/${engine.commands}</small></div>
    <div>commands where the proven model and the real TigerBeetle gave the same answers and the same balances${
      bad ? `. <b>${bad} disagreed</b>: from here on the proofs describe a ledger that is not the real one.` : "."
    }</div></div>`;
}

function lawsHtml() {
  const head = proof.ok
    ? `<p class="proof-ok">✓ <b>All ${laws.length} laws hold.</b> <code>bend core/PROOF.bend</code> re-checked them when this server started (${proof.ms} ms).</p>`
    : `<p class="proof-bad">✗ <b>The proofs do not check.</b> The server started anyway so you can see what happens.<br><code>${esc(proof.out.slice(0, 400))}</code></p>`;
  const items = laws.map((l) => `<li><code>${l.name}</code><span>${esc(l.says)}</span></li>`).join("");
  return `<div id="laws">${head}<ul>${items}</ul></div>`;
}

function duesFor(u: bigint) {
  const now = Date.now();
  const mine = [...holds.entries()].filter(([, h]) => h.u === u);
  return list(mine.map(([t1, h]) => ({
    $: "Due",
    k: h.k,
    t1,
    secs: BigInt(Math.max(0, Math.ceil((h.deadline - now) / 1000))),
  })));
}

function frame(u: bigint): string {
  const m = engine.model;
  const n = names();
  const parts = [
    V.seats(m, u, n),
    V.wallet(m, u, n),
    V.holds(duesFor(u)),
    feedHtml(),
    checkHtml(),
  ];
  const data = parts.join("").split("\n").map((l) => `data: elements ${l}`).join("\n");
  return `event: datastar-patch-elements\n${data}\n\n`;
}

function broadcast() {
  for (const c of clients) c.send(frame(c.u));
}

// Commands
// ========

async function welcome(s: Session) {
  const o = await engine.run({ $: "Join", u: s.u, fund: fresh() }, "join");
  log(s.name, `joined and got a $${Number(B.stipend()) / 100} wallet`, o);
}

async function hold(s: Session, k: bigint, manual = false) {
  const t1 = fresh(), t2 = fresh();
  const timeout = manual ? 2 : HOLD_SECS + 30;
  const o = await engine.run({ $: "Hold", u: s.u, k, t1, t2 }, "hold", { holdTimeout: timeout });
  if (o.model.every((x) => x === "Ok") && o.model.length > 0) {
    holds.set(t1, { u: s.u, k, t2, deadline: Date.now() + (manual ? 2000 : HOLD_SECS * 1000), manual });
  }
  log(s.name, `held seat ${label(k)}${manual ? " with a 2-second TigerBeetle timeout and no sweeper" : ""}`, o);
  return o;
}

async function settle(s: Session, t1: bigint, pay: boolean, via = "") {
  const h = holds.get(t1);
  // an unknown hold still goes to the core, which refuses what u does not own
  const t2 = h?.t2 ?? t1 + 1n;
  const cmd = { $: pay ? "Pay" : "Release", u: s.u, t1, t2, p1: fresh(), p2: fresh() };
  const o = await engine.run(cmd, pay ? "pay" : "release");
  const seat = h ? ` seat ${label(h.k)}` : ` hold #${t1}`;
  if (o.ops.length === 0) {
    log(s.name, `tried to ${pay ? "pay for" : "release"}${seat}`, o, "Refused by the core before reaching TigerBeetle: this hold is not theirs (law only_holder_" + (pay ? "pays" : "releases") + ").");
  } else {
    if (o.model.every((x) => x === "Ok")) holds.delete(t1);
    log(s.name, `${pay ? "paid for" : "released"}${seat}${via}`, o);
  }
  return o;
}

const label = (k: bigint) => String.fromCharCode(65 + Number(k / 4n)) + String(Number(k % 4n) + 1);

// the sweeper: release holds whose time is up (a timer, not a proof)
setInterval(async () => {
  const now = Date.now();
  for (const [t1, h] of holds) {
    if (!h.manual && h.deadline <= now) {
      holds.delete(t1);
      const s = { u: h.u, name: nameOf(h.u) };
      await settle(s, t1, false, " (time ran out)").catch(() => {});
    }
  }
  broadcast();
}, 1000);

// Try to break it
// ===============

async function attack(s: Session, kind: string) {
  const seats = arr(B.seat_map(engine.model));
  switch (kind) {
    case "double": {
      // two holds on the same free seat, sent at the same time
      const k = BigInt(Math.max(0, seats.findIndex((x: Bend) => x.$ === "Free")));
      const [a, b] = await Promise.all([hold(s, k), hold(s, k)]);
      log(s.name, `sent two holds for seat ${label(k)} at once`, undefined,
        `One won, one was refused (${a.tb.join(", ")} / ${b.tb.join(", ")}). Law seat_never_oversold.`);
      break;
    }
    case "steal": {
      const theirs = [...holds.entries()].find(([, h]) => h.u !== s.u);
      if (!theirs) {
        log(s.name, "looked for someone else's hold to pay for", undefined, "There is none right now. Open a second browser (or a private window), hold a seat there, then try again.");
        break;
      }
      await settle(s, theirs[0], true);
      break;
    }
    case "retry": {
      if (engine.lastOps.length === 0) break;
      const o = await engine.retry("retry");
      log(s.name, "resent the last chain of transfers with the same ids", o, "Law retry_is_harmless: the second attempt must change nothing.");
      break;
    }
    case "broke": {
      // spend the wallet down, then ask for one more seat
      const k = BigInt(Math.max(0, seats.findIndex((x: Bend) => x.$ === "Free")));
      const o = await hold(s, k);
      if (o.model[0] === "Ok") log(s.name, "tried to overspend", undefined, "That hold fit the wallet. Keep holding seats: the one that doesn't fit is refused by both sides (law wallet_never_overdrawn).");
      break;
    }
    case "expire": {
      // the model has no clock: let TigerBeetle expire a hold on its own.
      // Seats get cheaper toward the back, so take the last free one.
      const k = seats.map((x: Bend) => x.$).lastIndexOf("Free");
      if (k < 0) {
        log(s.name, "wanted to set a trap", undefined, "No free seat left.");
        break;
      }
      const o = await hold(s, BigInt(k), true);
      if (o.model[0] !== "Ok") {
        log(s.name, "wanted to set a trap", undefined, "The hold did not go through (the wallet is too low?), so there is nothing to expire. Release a hold and try again.");
        break;
      }
      log(s.name, "set a trap", undefined, "In 3 seconds this hold is paid for. By then TigerBeetle has expired it; the model has no clock and still thinks it is pending. Watch the cross-check.");
      setTimeout(async () => {
        const t1 = [...holds.entries()].find(([, h]) => h.manual && h.u === s.u)?.[0];
        if (t1 !== undefined) await settle(s, t1, true, " after TigerBeetle expired it");
        broadcast();
      }, 3000);
      break;
    }
  }
}

// HTTP
// ====

const page = () => readFileSync(join(import.meta.dir, "public/index.html"), "utf8")
  .replace("<!--LAWS-->", lawsHtml());
const datastar = readFileSync(join(import.meta.dir, "public/datastar.js"));
const css = readFileSync(join(import.meta.dir, "public/style.css"));

function session(req: Request): { sid: string; s?: Session } {
  const sid = req.headers.get("cookie")?.match(/sid=([\w-]+)/)?.[1] ?? "";
  return { sid, s: sessions.get(sid) };
}

async function signals(req: Request): Promise<Record<string, unknown>> {
  try {
    return await req.json();
  } catch {
    return {};
  }
}

const done = () => new Response(null, { status: 204 });

async function route(req: Request): Promise<Response> {
  const url = new URL(req.url);
  const path = url.pathname;

  if (path === "/datastar.js") return new Response(datastar, { headers: { "content-type": "text/javascript" } });
  if (path === "/style.css") return new Response(css, { headers: { "content-type": "text/css" } });

  if (path === "/") {
    let { sid, s } = session(req);
    const headers: Record<string, string> = { "content-type": "text/html; charset=utf-8" };
    if (!s) {
      sid = crypto.randomUUID();
      s = { u: nextUser++, name: "" };
      s.name = `Guest ${s.u}`;
      sessions.set(sid, s);
      headers["set-cookie"] = `sid=${sid}; Path=/; HttpOnly; SameSite=Lax`;
      await welcome(s);
      broadcast();
    }
    return new Response(page(), { headers });
  }

  const { s } = session(req);
  if (!s) return new Response("no session: reload the page", { status: 401 });

  if (path === "/events") {
    let client: Client;
    const stream = new ReadableStream<string>({
      start(ctl) {
        client = { u: s.u, send: (chunk) => ctl.enqueue(chunk) };
        clients.add(client);
        ctl.enqueue(`event: datastar-patch-signals\ndata: signals ${JSON.stringify({ name: s.name })}\n\n`);
        ctl.enqueue(frame(s.u));
      },
      cancel() {
        clients.delete(client);
      },
    });
    req.signal.addEventListener("abort", () => clients.delete(client));
    return new Response(stream, {
      headers: { "content-type": "text/event-stream", "cache-control": "no-cache", connection: "keep-alive" },
    });
  }

  if (req.method !== "POST") return new Response("not found", { status: 404 });

  let m: RegExpMatchArray | null;
  if ((m = path.match(/^\/hold\/(\d+)$/))) {
    await hold(s, BigInt(m[1]));
  } else if ((m = path.match(/^\/pay\/(\d+)$/))) {
    await settle(s, BigInt(m[1]), true);
  } else if ((m = path.match(/^\/release\/(\d+)$/))) {
    await settle(s, BigInt(m[1]), false);
  } else if ((m = path.match(/^\/break\/(\w+)$/))) {
    await attack(s, m[1]);
  } else if (path === "/name") {
    const name = String((await signals(req)).name ?? "").slice(0, 60).trim();
    if (name) {
      const old = s.name;
      s.name = name;
      log(old, `is now called ${name}`);
    }
  } else {
    return new Response("not found", { status: 404 });
  }
  broadcast();
  return done();
}

// Boot
// ====

try {
  const o = await engine.init();
  log("The venue", "opened: 12 seats issued", o);
} catch (e) {
  console.error(String(e instanceof Error ? e.message : e));
  process.exit(1);
}

Bun.serve({
  port: PORT,
  idleTimeout: 0,
  fetch: (req) => route(req).catch((e) => {
    console.error(e);
    return new Response(String(e), { status: 500 });
  }),
});
console.log(`Proof Tickets on http://localhost:${PORT}`);
