# LAWS.bend: what must always be true. The human's file: it states the
# rules and proves nothing. PROOF.bend must prove every law here, and
# `bend core/PROOF.bend` fails while any of them is open or false.

import Base
import ./kit.bend as K
import ./ledger.bend as L
import ./boxoffice.bend as B
import ./html.bend as H
import ./view.bend as V

# Vocabulary
# ----------

# SafeIf(g, x, y): when g holds, x <= y
def SafeIf(g: Bool, x: Nat, y: Nat) -> Data:
  match g:
    case True{}:
      K.LE(x, y)
    case False{}:
      Unit

# A guarded account (a seat, a wallet) never owes: its debits, pending and
# posted, never exceed its posted credits. This is TigerBeetle's
# debits_must_not_exceed_credits flag, stated over the model.
def Safe(+a: L.Id, +Lg: L.Ledger) -> Data:
  SafeIf(L.guarded(a), L.debits(a, L.log(Lg)), L.cposted(a, L.log(Lg)))

# The ledger model
# ----------------

# LAW: no transfer, of any kind, can overdraw a guarded account.
law no_overdraft:
  for +a: L.Id
  for +Lg: L.Ledger
  for +op: L.Op
  for s: Safe(a, Lg)
  Safe(a, L.after(Lg, op))

# LAW: a linked chain never overdraws a guarded account either.
law chain_no_overdraft:
  for +a: L.Id
  for +Lg: L.Ledger
  for +ops: List<&2, L.Op>
  for +s: Safe(a, Lg)
  Safe(a, Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(Lg, ops)))

def all_ok(xs: List<&2, L.Status>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case s <> rest:
      L.is_ok(s) && all_ok(rest)

# LAW: all or nothing. Either every transfer of a chain succeeded, or the
# ledger is exactly as it was.
law all_or_nothing:
  for +Lg: L.Ledger
  for +ops: List<&2, L.Op>
  Or({Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(Lg, ops)) == Lg : L.Ledger},
     {all_ok(Pair.snd(L.Ledger, List<&2, L.Status>, L.chain(Lg, ops))) == True{} : Bool})

# LAW: retrying a transfer (same id) is harmless: the second attempt
# changes nothing, whatever the first one did.
law retry_is_harmless:
  for +Lg: L.Ledger
  for +op: L.Op
  {L.after(L.after(Lg, op), op) == L.after(Lg, op) : L.Ledger}

# The box office
# --------------

# LAW: no sequence of visitor commands, of any length, in any order, with
# any ids, ever overdraws a wallet.
law wallet_never_overdrawn:
  for +u: Nat
  for cmds: List<&2, B.Cmd>
  Safe(L.Wallet{u}, B.replay(cmds, B.genesis()))

# LAW: no sequence of visitor commands ever sells or holds a seat twice:
# every seat's debits (holds plus sales) stay at most 1.
law seat_never_oversold:
  for +k: Nat
  for +cmds: List<&2, B.Cmd>
  K.LE(L.debits(L.Seat{k}, L.log(B.replay(cmds, B.genesis()))), 1n)

# LAW: only the visitor who holds a seat can pay for it...
law only_holder_pays:
  for +Lg: L.Ledger
  for +u: Nat
  for +t1: Nat
  for +t2: Nat
  for +p1: Nat
  for +p2: Nat
  for e: {B.owns(Lg, u, t1, t2) == False{} : Bool}
  {B.next(Lg, B.Pay{u, t1, t2, p1, p2}) == Lg : L.Ledger}

# LAW: ...or release it.
law only_holder_releases:
  for +Lg: L.Ledger
  for +u: Nat
  for +t1: Nat
  for +t2: Nat
  for +p1: Nat
  for +p2: Nat
  for e: {B.owns(Lg, u, t1, t2) == False{} : Bool}
  {B.next(Lg, B.Release{u, t1, t2, p1, p2}) == Lg : L.Ledger}

# The page
# --------

# LAW: escaped visitor text never contains < > " or ', whatever it was.
law text_is_clean:
  for s: String
  {H.clean(H.text(s)) == True{} : Bool}

# LAW: a seat's cell has the same tag structure whatever its holder calls
# themselves: no display name can add or remove an element.
law names_cannot_inject:
  for +k: Nat
  for +s: B.Seat
  for +viewer: Nat
  for +who1: String
  for +who2: String
  {H.tags(V.seat_cell(k, s, viewer, who1)) == H.tags(V.seat_cell(k, s, viewer, who2)) : Nat}
