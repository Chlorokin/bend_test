# ledger.bend: a model of the slice of TigerBeetle this app uses.
#
# TigerBeetle stores balances as four counters per account. The model
# stores the *log* instead, one Entry per transfer with its current state,
# and derives every counter by summing the log. That choice is what makes
# the laws provable without subtraction: posting a pending transfer moves an
# entry from Pending to Settled, which moves its amount from one sum to
# another, instead of decrementing one counter and incrementing another.
#
# Ids are typed (Id) rather than raw u128s; the server encodes them.
# The checks run in the order TigerBeetle runs them, so the status codes
# can be compared one for one against the real database (the server does
# that on every batch: see server/bridge.ts).

import Base
import ./kit.bend as K

# Accounts
# --------

type Id is Data:
  Bank{}
  Venue{}
  Issuer{}
  Seat{k: Nat}
  Wallet{u: Nat}
  Tickets{u: Nat}

def Id.eq(a: Id, b: Id) -> Bool:
  match a b:
    case Bank{} Bank{}:
      True{}
    case Venue{} Venue{}:
      True{}
    case Issuer{} Issuer{}:
      True{}
    case Seat{x} Seat{y}:
      Nat.is_eq(x, y)
    case Wallet{x} Wallet{y}:
      Nat.is_eq(x, y)
    case Tickets{x} Tickets{y}:
      Nat.is_eq(x, y)
    case _ _:
      False{}

# ledger 1 is money (cents), ledger 2 is seats (tickets)
def ledger_of(a: Id) -> Nat:
  match a:
    case Bank{}:
      1n
    case Venue{}:
      1n
    case Wallet{u}:
      1n
    case Issuer{}:
      2n
    case Seat{k}:
      2n
    case Tickets{u}:
      2n

# the accounts opened with TigerBeetle's debits_must_not_exceed_credits
def guarded(a: Id) -> Bool:
  match a:
    case Seat{k}:
      True{}
    case Wallet{u}:
      True{}
    case _:
      False{}

# Transfers
# ---------

# Posted: created posted. Pending: created pending, not yet resolved.
# Settled: created pending, then posted. Voided: created pending, then voided.
type St is Data:
  Posted{}
  Pending{}
  Settled{}
  Voided{}

type Entry is Data:
  Entry{id: Nat, dr: Id, cr: Id, amt: Nat, st: St}

type Op is Data:
  Create{id: Nat, dr: Id, cr: Id, amt: Nat, pending: Bool}
  Post{id: Nat, pid: Nat}
  Void{id: Nat, pid: Nat}

type Status is Data:
  Ok{}
  LinkedFailed{}
  SameAccounts{}
  DebitNotFound{}
  CreditNotFound{}
  LedgerMismatch{}
  Exists{}
  ExceedsCredits{}
  PendingNotFound{}
  NotPending{}
  AlreadyPosted{}
  AlreadyVoided{}

type Ledger is Data:
  Ledger{accts: List<&2, Id>, log: List<&2, Entry>, ids: List<&2, Nat>}

def empty() -> Ledger:
  Ledger{[], [], []}

def accts(L: Ledger) -> List<&2, Id>:
  Ledger{accts, log, ids} = L
  accts

def log(L: Ledger) -> List<&2, Entry>:
  Ledger{accts, log, ids} = L
  log

def ids(L: Ledger) -> List<&2, Nat>:
  Ledger{accts, log, ids} = L
  ids

def op_id(op: Op) -> Nat:
  match op:
    case Create{id, dr, cr, amt, pending}:
      id
    case Post{id, pid}:
      id
    case Void{id, pid}:
      id

# Derived balances
# ----------------

# whether an entry in state st counts toward debits_pending + debits_posted
def live(st: St) -> Bool:
  match st:
    case Posted{}:
      True{}
    case Pending{}:
      True{}
    case Settled{}:
      True{}
    case Voided{}:
      False{}

# whether an entry in state st counts toward credits_posted
def posted(st: St) -> Bool:
  match st:
    case Posted{}:
      True{}
    case Pending{}:
      False{}
    case Settled{}:
      True{}
    case Voided{}:
      False{}

def pending(st: St) -> Bool:
  match st:
    case Pending{}:
      True{}
    case _:
      False{}

# debits_pending + debits_posted of account a
def debits(+a: Id, log: List<&2, Entry>) -> Nat:
  match log:
    case Nil{}:
      0n
    case Entry{id, dr, cr, amt, st} <> rest:
      Nat.add(K.when(live(st) && Id.eq(dr, a), amt), debits(a, rest))

# credits_posted of account a
def cposted(+a: Id, log: List<&2, Entry>) -> Nat:
  match log:
    case Nil{}:
      0n
    case Entry{id, dr, cr, amt, st} <> rest:
      Nat.add(K.when(posted(st) && Id.eq(cr, a), amt), cposted(a, rest))

# credits_pending of account a
def cpending(+a: Id, log: List<&2, Entry>) -> Nat:
  match log:
    case Nil{}:
      0n
    case Entry{id, dr, cr, amt, st} <> rest:
      Nat.add(K.when(pending(st) && Id.eq(cr, a), amt), cpending(a, rest))

# debits_posted of account a
def dposted(+a: Id, log: List<&2, Entry>) -> Nat:
  match log:
    case Nil{}:
      0n
    case Entry{id, dr, cr, amt, st} <> rest:
      Nat.add(K.when(posted(st) && Id.eq(dr, a), amt), dposted(a, rest))

# every credit ever made to a, whatever became of it (an upper bound)
def credits_any(+a: Id, log: List<&2, Entry>) -> Nat:
  match log:
    case Nil{}:
      0n
    case Entry{id, dr, cr, amt, st} <> rest:
      Nat.add(K.when(Id.eq(cr, a), amt), credits_any(a, rest))

# Lookups
# -------

def has_acct(+a: Id, xs: List<&2, Id>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Id.eq(h, a) || has_acct(a, t)

def has_id(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Nat.is_eq(h, x) || has_id(x, t)

def find.pick(b: Bool, st: St, rest: Maybe<&2, St>) -> Maybe<&2, St>:
  match b:
    case True{}:
      Some{st}
    case False{}:
      rest

# the state of transfer pid, if it exists
def find(+pid: Nat, log: List<&2, Entry>) -> Maybe<&2, St>:
  match log:
    case Nil{}:
      None{}
    case Entry{id, dr, cr, amt, st} <> rest:
      find.pick(Nat.is_eq(id, pid), st, find(pid, rest))

# Resolving a pending transfer
# ----------------------------

# Pending moves to Settled (post) or Voided (void); anything else stays
def resolve(st: St, post: Bool) -> St:
  match st:
    case Pending{}:
      match post:
        case True{}:
          Settled{}
        case False{}:
          Voided{}
    case Posted{}:
      Posted{}
    case Settled{}:
      Settled{}
    case Voided{}:
      Voided{}

def settle.one(b: Bool, st: St, post: Bool) -> St:
  match b:
    case True{}:
      resolve(st, post)
    case False{}:
      st

def settle(+pid: Nat, +post: Bool, log: List<&2, Entry>) -> List<&2, Entry>:
  match log:
    case Nil{}:
      Nil{}
    case Entry{id, dr, cr, amt, st} <> rest:
      +i = id
      Entry{i, dr, cr, amt, settle.one(Nat.is_eq(i, pid), st, post)} <> settle(pid, post, rest)

# Applying one transfer
# ---------------------
# One helper per check, in TigerBeetle's order. Each takes the verdict of
# its check as a parameter (a computed value cannot be matched in place),
# which is also what lets a proof follow the same branch.

def state(pending: Bool) -> St:
  match pending:
    case True{}:
      Pending{}
    case False{}:
      Posted{}

def commit(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool) -> Ledger & Status:
  (Ledger{accts(L), Entry{id, dr, cr, amt, state(p)} <> log(L), id <> ids(L)}, Ok{})

def create.g(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, -a: Nat, -b: Nat, c: Or(K.LE(a, b), K.LE(1n+b, a))) -> Ledger & Status:
  match c:
    case Inl{e}:
      commit(L, id, dr, cr, amt, p)
    case Inr{e}:
      (L, ExceedsCredits{})

# the guard: debits_pending + debits_posted + amount <= credits_posted
def create.f(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, g: Bool) -> Ledger & Status:
  match g:
    case False{}:
      commit(L, id, dr, cr, amt, p)
    case True{}:
      +x = Nat.add(amt, debits(dr, log(L)))
      +y = cposted(dr, log(L))
      create.g(L, id, dr, cr, amt, p, x, y, K.le_case(x, y))

def create.e(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, ex: Bool) -> Ledger & Status:
  match ex:
    case True{}:
      (L, Exists{})
    case False{}:
      create.f(L, id, dr, cr, amt, p, guarded(dr))

def create.d(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, same_ledger: Bool) -> Ledger & Status:
  match same_ledger:
    case False{}:
      (L, LedgerMismatch{})
    case True{}:
      create.e(L, id, dr, cr, amt, p, has_id(id, ids(L)))

def create.c(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, found: Bool) -> Ledger & Status:
  match found:
    case False{}:
      (L, CreditNotFound{})
    case True{}:
      create.d(L, id, dr, cr, amt, p, Nat.is_eq(ledger_of(dr), ledger_of(cr)))

def create.b(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, found: Bool) -> Ledger & Status:
  match found:
    case False{}:
      (L, DebitNotFound{})
    case True{}:
      create.c(L, id, dr, cr, amt, p, has_acct(cr, accts(L)))

def create.a(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool, same: Bool) -> Ledger & Status:
  match same:
    case True{}:
      (L, SameAccounts{})
    case False{}:
      create.b(L, id, dr, cr, amt, p, has_acct(dr, accts(L)))

def create(+L: Ledger, +id: Nat, +dr: Id, +cr: Id, +amt: Nat, +p: Bool) -> Ledger & Status:
  create.a(L, id, dr, cr, amt, p, Id.eq(dr, cr))

# post (post = True) or void (post = False) the pending transfer pid
def finish(+L: Ledger, +id: Nat, +pid: Nat, +post: Bool) -> Ledger & Status:
  (Ledger{accts(L), settle(pid, post, log(L)), id <> ids(L)}, Ok{})

def resolve.c(+L: Ledger, +id: Nat, +pid: Nat, +post: Bool, st: St) -> Ledger & Status:
  match st:
    case Pending{}:
      finish(L, id, pid, post)
    case Settled{}:
      (L, AlreadyPosted{})
    case Voided{}:
      (L, AlreadyVoided{})
    case Posted{}:
      (L, NotPending{})

def resolve.b(+L: Ledger, +id: Nat, +pid: Nat, +post: Bool, st: St, ex: Bool) -> Ledger & Status:
  match ex:
    case True{}:
      (L, Exists{})
    case False{}:
      resolve.c(L, id, pid, post, st)

def resolve.a(+L: Ledger, +id: Nat, +pid: Nat, +post: Bool, found: Maybe<&2, St>) -> Ledger & Status:
  match found:
    case None{}:
      (L, PendingNotFound{})
    case Some{st}:
      match st:
        case Posted{}:
          (L, NotPending{})
        case Pending{}:
          resolve.b(L, id, pid, post, Pending{}, has_id(id, ids(L)))
        case Settled{}:
          resolve.b(L, id, pid, post, Settled{}, has_id(id, ids(L)))
        case Voided{}:
          resolve.b(L, id, pid, post, Voided{}, has_id(id, ids(L)))

def apply(+L: Ledger, op: Op) -> Ledger & Status:
  match op:
    case Create{id, dr, cr, amt, pending}:
      create(L, id, dr, cr, amt, pending)
    case Post{id, +pid}:
      resolve.a(L, id, pid, True{}, find(pid, log(L)))
    case Void{id, +pid}:
      resolve.a(L, id, pid, False{}, find(pid, log(L)))

# the ledger and the status after one transfer
def after(+L: Ledger, +op: Op) -> Ledger:
  Pair.fst(Ledger, Status, apply(L, op))

def status(+L: Ledger, +op: Op) -> Status:
  Pair.snd(Ledger, Status, apply(L, op))

# Linked chains
# -------------
# TigerBeetle applies a linked chain all or nothing: when one transfer
# fails, it reports that failure and linked_event_failed for every other
# transfer of the chain, and no transfer of the chain takes effect.

type Out is Data:
  Committed{L: Ledger}
  Aborted{at: Nat, why: Status}

def is_ok(s: Status) -> Bool:
  match s:
    case Ok{}:
      True{}
    case _:
      False{}

def run.pick(ok: Bool, why: Status, rec: Out) -> Out:
  match ok:
    case True{}:
      match rec:
        case Committed{L}:
          Committed{L}
        case Aborted{at, w}:
          Aborted{1n+at, w}
    case False{}:
      Aborted{0n, why}

def run(ops: List<&2, Op>, +L: Ledger) -> Out:
  match ops:
    case Nil{}:
      Committed{L}
    case op <> rest:
      +o = op
      run.pick(is_ok(status(L, o)), status(L, o), run(rest, after(L, o)))

def oks(n: Nat) -> List<&2, Status>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Ok{} <> oks(p)

# linked_event_failed everywhere, except `why` at position `at`
def fails(n: Nat, +i: Nat, +at: Nat, +why: Status) -> List<&2, Status>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Bool.pick(Status, Nat.is_eq(i, at), why, LinkedFailed{}) <> fails(p, 1n+i, at, why)

def chain.fin(+L: Ledger, n: Nat, out: Out) -> Ledger & List<&2, Status>:
  match out:
    case Committed{L1}:
      (L1, oks(n))
    case Aborted{at, why}:
      (L, fails(n, 0n, at, why))

def chain(+L: Ledger, +ops: List<&2, Op>) -> Ledger & List<&2, Status>:
  chain.fin(L, List.length(&2, Op, ops), run(ops, L))

# Accounts
# --------

# open account a (idempotent: an existing account is left as it is)
def open.pick(+L: Ledger, +a: Id, exists: Bool) -> Ledger:
  match exists:
    case True{}:
      L
    case False{}:
      Ledger{a <> accts(L), log(L), ids(L)}

def open(+L: Ledger, +a: Id) -> Ledger:
  open.pick(L, a, has_acct(a, accts(L)))
