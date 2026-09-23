# boxoffice.bend: the business. A small venue sells seats; a visitor
# joins (and gets a $100 wallet), holds a seat for a few minutes, then pays
# or releases it. Every command becomes one linked chain of TigerBeetle
# transfers, so a hold moves the seat and the money together or not at all.
#
#   seat:    Issuer  -> Seat{k}      1 unit, posted at opening (genesis)
#   hold:    Seat{k} -> Tickets{u}   1 unit, pending   } one linked chain
#            Wallet{u} -> Venue      price, pending    }
#   pay:     post both pending transfers               (linked)
#   release: void both pending transfers               (linked)
#
# Seat and wallet accounts are opened with debits_must_not_exceed_credits,
# so the database itself refuses a second hold on a seat (the seat has one
# credit) and refuses a hold the wallet cannot cover.

import Base
import ./kit.bend as K
import ./ledger.bend as L

# Venue
# -----

def seat_count() -> Nat:
  12n

# what a new visitor's wallet is funded with, in cents
def stipend() -> Nat:
  10000n

# rows of four: front $45, middle $30, back $15
def price(+k: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(k, 4n), 4500n, Bool.pick(Nat, Nat.is_lt(k, 8n), 3000n, 1500n))

# Commands
# --------
# Transfer ids come from the server; the laws hold whatever they are.

type Cmd is Data:
  Join{u: Nat, fund: Nat}
  Hold{u: Nat, k: Nat, t1: Nat, t2: Nat}
  Pay{u: Nat, t1: Nat, t2: Nat, p1: Nat, p2: Nat}
  Release{u: Nat, t1: Nat, t2: Nat, p1: Nat, p2: Nat}

# the debit or credit side of transfer id, if it exists
def side.pick(b: Bool, x: L.Id, rest: Maybe<&2, L.Id>) -> Maybe<&2, L.Id>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      rest

def credited(+id: Nat, log: List<&2, L.Entry>) -> Maybe<&2, L.Id>:
  match log:
    case Nil{}:
      None{}
    case L.Entry{i, dr, cr, amt, st} <> rest:
      side.pick(Nat.is_eq(i, id), cr, credited(id, rest))

def debited(+id: Nat, log: List<&2, L.Entry>) -> Maybe<&2, L.Id>:
  match log:
    case Nil{}:
      None{}
    case L.Entry{i, dr, cr, amt, st} <> rest:
      side.pick(Nat.is_eq(i, id), dr, debited(id, rest))

def is_id(+a: L.Id, m: Maybe<&2, L.Id>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      L.Id.eq(x, a)

# a hold (t1, t2) belongs to u when its seat leg went to u's tickets and
# its money leg came from u's wallet
def owns(+Lg: L.Ledger, +u: Nat, +t1: Nat, +t2: Nat) -> Bool:
  is_id(L.Tickets{u}, credited(t1, L.log(Lg))) && is_id(L.Wallet{u}, debited(t2, L.log(Lg)))

def guard_ops(b: Bool, ops: List<&2, L.Op>) -> List<&2, L.Op>:
  match b:
    case True{}:
      ops
    case False{}:
      Nil{}

# the chain of transfers a command asks for (none when it is not allowed)
def plan(+Lg: L.Ledger, cmd: Cmd) -> List<&2, L.Op>:
  match cmd:
    case Join{u, fund}:
      [L.Create{fund, L.Bank{}, L.Wallet{u}, stipend(), False{}}]
    case Hold{+u, +k, t1, t2}:
      [L.Create{t1, L.Seat{k}, L.Tickets{u}, 1n, True{}}, L.Create{t2, L.Wallet{u}, L.Venue{}, price(k), True{}}]
    case Pay{+u, +t1, +t2, p1, p2}:
      guard_ops(owns(Lg, u, t1, t2), [L.Post{p1, t1}, L.Post{p2, t2}])
    case Release{+u, +t1, +t2, p1, p2}:
      guard_ops(owns(Lg, u, t1, t2), [L.Void{p1, t1}, L.Void{p2, t2}])

# the accounts a command opens before its chain runs
def opens(+Lg: L.Ledger, cmd: Cmd) -> L.Ledger:
  match cmd:
    case Join{+u, fund}:
      L.open(L.open(Lg, L.Wallet{u}), L.Tickets{u})
    case _:
      Lg

# run one command: open its accounts, then apply its chain
def step(+Lg: L.Ledger, +cmd: Cmd) -> L.Ledger & List<&2, L.Status>:
  +Lo = opens(Lg, cmd)
  L.chain(Lo, plan(Lo, cmd))

def next(+Lg: L.Ledger, +cmd: Cmd) -> L.Ledger:
  Pair.fst(L.Ledger, List<&2, L.Status>, step(Lg, cmd))

def replay(cmds: List<&2, Cmd>, +Lg: L.Ledger) -> L.Ledger:
  match cmds:
    case Nil{}:
      Lg
    case c <> rest:
      replay(rest, next(Lg, c))

# Opening day
# -----------
# The house accounts, one account per seat, and one unit issued to each
# seat. Seat k is issued by transfer id 1+k; the server's ids start above.

def seat_accts(n: Nat, +Lg: L.Ledger) -> L.Ledger:
  match n:
    case 0n:
      Lg
    case 1n+p:
      +q = p
      seat_accts(q, L.open(Lg, L.Seat{q}))

def issue(n: Nat) -> List<&2, L.Op>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +q = p
      L.Create{1n+q, L.Issuer{}, L.Seat{q}, 1n, False{}} <> issue(q)

def house() -> L.Ledger:
  seat_accts(seat_count(), L.open(L.open(L.open(L.empty(), L.Bank{}), L.Venue{}), L.Issuer{}))

def genesis() -> L.Ledger:
  +h = house()
  Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(h, issue(seat_count())))

# Seat map
# --------

type Seat is Data:
  Free{}
  Held{u: Nat, t1: Nat}
  Sold{u: Nat}

def seat.of(to: L.Id, id: Nat, st: L.St) -> Seat:
  match to:
    case L.Tickets{u}:
      match st:
        case L.Pending{}:
          Held{u, id}
        case L.Settled{}:
          Sold{u}
        case L.Posted{}:
          Sold{u}
        case L.Voided{}:
          Free{}
    case _:
      Free{}

def seat.pick(b: Bool, s: Seat, rest: Seat) -> Seat:
  match b:
    case True{}:
      s
    case False{}:
      rest

def is_free(s: Seat) -> Bool:
  match s:
    case Free{}:
      True{}
    case _:
      False{}

# the newest live transfer out of Seat{k} decides who has it
def seat_state(+k: Nat, log: List<&2, L.Entry>) -> Seat:
  match log:
    case Nil{}:
      Free{}
    case L.Entry{id, dr, cr, amt, +st} <> rest:
      +s = seat.of(cr, id, st)
      seat.pick(L.Id.eq(dr, L.Seat{k}) && L.live(st), s, seat_state(k, rest))

# the seat map, seat 0 first
def seat_map.go(n: Nat, +i: Nat, +log: List<&2, L.Entry>) -> List<&2, Seat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      seat_state(i, log) <> seat_map.go(p, 1n+i, log)

def seat_map(+Lg: L.Ledger) -> List<&2, Seat>:
  seat_map.go(seat_count(), 0n, L.log(Lg))

# a wallet's spendable balance: credits_posted - debits_posted - debits_pending
def balance(+Lg: L.Ledger, +u: Nat) -> Nat:
  Nat.sub(L.cposted(L.Wallet{u}, L.log(Lg)), L.debits(L.Wallet{u}, L.log(Lg)))
