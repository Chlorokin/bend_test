# PROOF.bend: the proofs. Everything here exists to fill the laws of
# LAWS.bend; `bend core/PROOF.bend` is the whole verification.

import Base
import ./kit.bend as K
import ./ledger.bend as L
import ./boxoffice.bend as B
import ./LAWS.bend as Laws

# Proof kit
# =========

# False is not True
def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : K.T(Bool.not(_))
  Unit{}

def sym(-A: Type, -a: A, -b: A, e: {a == b : A}) -> {b == a : A}:
  %e : {_ == a : A}
  {==}

# split on a Bool, remembering which way it went
def bool_case(+b: Bool, -P: Bool -> Type, t: {True{} == b : Bool} -> P(True{}), f: {False{} == b : Bool} -> P(False{})) -> P(b):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

# Order
# -----

def le_refl(n: Nat) -> K.LE(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_refl(p)

def le_trans(a: Nat, b: Nat, c: Nat) -> K.LE(a, b) -> K.LE(b, c) -> K.LE(a, c):
  match a b c:
    case 0n _ _:
      ab => bc => Unit{}
    case 1n+a1 0n _:
      ab => bc => Empty.absurd(K.LE(1n+a1, c), ab)
    case 1n+a1 1n+b1 0n:
      ab => bc => Empty.absurd(K.LE(1n+a1, 0n), bc)
    case 1n+a1 1n+b1 1n+c1:
      le_trans(a1, b1, c1)

def le_succ(n: Nat) -> K.LE(n, 1n+n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      le_succ(p)

# y <= x + y
def le_add_l(+x: Nat, +y: Nat) -> K.LE(y, Nat.add(x, y)):
  match x:
    case 0n:
      le_refl(y)
    case 1n+p:
      le_trans(y, Nat.add(p, y), 1n+Nat.add(p, y), le_add_l(p, y), le_succ(Nat.add(p, y)))

# x <= y gives k + x <= k + y
def le_add_mono_r(k: Nat, -x: Nat, -y: Nat, h: K.LE(x, y)) -> K.LE(Nat.add(k, x), Nat.add(k, y)):
  match k:
    case 0n:
      h
    case 1n+p:
      le_add_mono_r(p, x, y, h)

# x <= y gives x + k <= y + k
def le_add_mono_l(x: Nat, y: Nat, +k: Nat) -> K.LE(x, y) -> K.LE(Nat.add(x, k), Nat.add(y, k)):
  match x y:
    case 0n _:
      h => le_add_l(y, k)
    case 1n+x1 0n:
      h => Empty.absurd(K.LE(Nat.add(1n+x1, k), Nat.add(0n, k)), h)
    case 1n+x1 1n+y1:
      le_add_mono_l(x1, y1, k)

# a <= b and c <= d give a + c <= b + d
def le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: K.LE(a, b), cd: K.LE(c, d)) -> K.LE(Nat.add(a, c), Nat.add(b, d)):
  le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), le_add_mono_r(a, c, d, cd), le_add_mono_l(a, b, d, ab))

# Equality tests
# --------------

def nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def nat_eq_sound(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == True{} : Bool} -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      e => {==}
    case 0n 1n+b1:
      e => Empty.absurd({0n == 1n+b1 : Nat}, false_true(e))
    case 1n+a1 0n:
      e => Empty.absurd({1n+a1 == 0n : Nat}, false_true(e))
    case 1n+a1 1n+b1:
      e => Equal.cong(Nat, Nat, n => 1n+n, a1, b1, nat_eq_sound(a1, b1, e))

def id_eq_refl(a: L.Id) -> {L.Id.eq(a, a) == True{} : Bool}:
  match a:
    case L.Bank{}:
      {==}
    case L.Venue{}:
      {==}
    case L.Issuer{}:
      {==}
    case L.Seat{k}:
      nat_eq_refl(k)
    case L.Wallet{u}:
      nat_eq_refl(u)
    case L.Tickets{u}:
      nat_eq_refl(u)

# Id.eq(a, b) is True exactly when a and b are the same account
def id_eq_sound(a: L.Id, b: L.Id) -> {L.Id.eq(a, b) == True{} : Bool} -> {a == b : L.Id}:
  match a b:
    case L.Bank{} L.Bank{}:
      e => {==}
    case L.Bank{} L.Venue{}:
      e => Empty.absurd({L.Bank{} == L.Venue{} : L.Id}, false_true(e))
    case L.Bank{} L.Issuer{}:
      e => Empty.absurd({L.Bank{} == L.Issuer{} : L.Id}, false_true(e))
    case L.Bank{} L.Seat{y}:
      e => Empty.absurd({L.Bank{} == L.Seat{y} : L.Id}, false_true(e))
    case L.Bank{} L.Wallet{y}:
      e => Empty.absurd({L.Bank{} == L.Wallet{y} : L.Id}, false_true(e))
    case L.Bank{} L.Tickets{y}:
      e => Empty.absurd({L.Bank{} == L.Tickets{y} : L.Id}, false_true(e))
    case L.Venue{} L.Bank{}:
      e => Empty.absurd({L.Venue{} == L.Bank{} : L.Id}, false_true(e))
    case L.Venue{} L.Venue{}:
      e => {==}
    case L.Venue{} L.Issuer{}:
      e => Empty.absurd({L.Venue{} == L.Issuer{} : L.Id}, false_true(e))
    case L.Venue{} L.Seat{y}:
      e => Empty.absurd({L.Venue{} == L.Seat{y} : L.Id}, false_true(e))
    case L.Venue{} L.Wallet{y}:
      e => Empty.absurd({L.Venue{} == L.Wallet{y} : L.Id}, false_true(e))
    case L.Venue{} L.Tickets{y}:
      e => Empty.absurd({L.Venue{} == L.Tickets{y} : L.Id}, false_true(e))
    case L.Issuer{} L.Bank{}:
      e => Empty.absurd({L.Issuer{} == L.Bank{} : L.Id}, false_true(e))
    case L.Issuer{} L.Venue{}:
      e => Empty.absurd({L.Issuer{} == L.Venue{} : L.Id}, false_true(e))
    case L.Issuer{} L.Issuer{}:
      e => {==}
    case L.Issuer{} L.Seat{y}:
      e => Empty.absurd({L.Issuer{} == L.Seat{y} : L.Id}, false_true(e))
    case L.Issuer{} L.Wallet{y}:
      e => Empty.absurd({L.Issuer{} == L.Wallet{y} : L.Id}, false_true(e))
    case L.Issuer{} L.Tickets{y}:
      e => Empty.absurd({L.Issuer{} == L.Tickets{y} : L.Id}, false_true(e))
    case L.Seat{x} L.Bank{}:
      e => Empty.absurd({L.Seat{x} == L.Bank{} : L.Id}, false_true(e))
    case L.Seat{x} L.Venue{}:
      e => Empty.absurd({L.Seat{x} == L.Venue{} : L.Id}, false_true(e))
    case L.Seat{x} L.Issuer{}:
      e => Empty.absurd({L.Seat{x} == L.Issuer{} : L.Id}, false_true(e))
    case L.Seat{x} L.Seat{y}:
      e => Equal.cong(Nat, L.Id, n => L.Seat{n}, x, y, nat_eq_sound(x, y, e))
    case L.Seat{x} L.Wallet{y}:
      e => Empty.absurd({L.Seat{x} == L.Wallet{y} : L.Id}, false_true(e))
    case L.Seat{x} L.Tickets{y}:
      e => Empty.absurd({L.Seat{x} == L.Tickets{y} : L.Id}, false_true(e))
    case L.Wallet{x} L.Bank{}:
      e => Empty.absurd({L.Wallet{x} == L.Bank{} : L.Id}, false_true(e))
    case L.Wallet{x} L.Venue{}:
      e => Empty.absurd({L.Wallet{x} == L.Venue{} : L.Id}, false_true(e))
    case L.Wallet{x} L.Issuer{}:
      e => Empty.absurd({L.Wallet{x} == L.Issuer{} : L.Id}, false_true(e))
    case L.Wallet{x} L.Seat{y}:
      e => Empty.absurd({L.Wallet{x} == L.Seat{y} : L.Id}, false_true(e))
    case L.Wallet{x} L.Wallet{y}:
      e => Equal.cong(Nat, L.Id, n => L.Wallet{n}, x, y, nat_eq_sound(x, y, e))
    case L.Wallet{x} L.Tickets{y}:
      e => Empty.absurd({L.Wallet{x} == L.Tickets{y} : L.Id}, false_true(e))
    case L.Tickets{x} L.Bank{}:
      e => Empty.absurd({L.Tickets{x} == L.Bank{} : L.Id}, false_true(e))
    case L.Tickets{x} L.Venue{}:
      e => Empty.absurd({L.Tickets{x} == L.Venue{} : L.Id}, false_true(e))
    case L.Tickets{x} L.Issuer{}:
      e => Empty.absurd({L.Tickets{x} == L.Issuer{} : L.Id}, false_true(e))
    case L.Tickets{x} L.Seat{y}:
      e => Empty.absurd({L.Tickets{x} == L.Seat{y} : L.Id}, false_true(e))
    case L.Tickets{x} L.Wallet{y}:
      e => Empty.absurd({L.Tickets{x} == L.Wallet{y} : L.Id}, false_true(e))
    case L.Tickets{x} L.Tickets{y}:
      e => Equal.cong(Nat, L.Id, n => L.Tickets{n}, x, y, nat_eq_sound(x, y, e))

# SafeIf is monotone: fewer debits, more credits
def safeif_mono(g: Bool, +x1: Nat, +x: Nat, +y: Nat, +y1: Nat, hx: K.LE(x1, x), s: Laws.SafeIf(g, x, y), hy: K.LE(y, y1)) -> Laws.SafeIf(g, x1, y1):
  match g:
    case True{}:
      le_trans(x1, y, y1, le_trans(x1, x, y, hx, s), hy)
    case False{}:
      Unit{}

# No overdraft
# ============

# Committing a new entry
# ----------------------
# The new entry adds its amount to dr's debits and, if posted, to cr's
# credits. For a != dr the debits are unchanged and the credits can only
# grow; for a == dr the guard check the ledger ran is exactly what is needed.

# a == dr: the guard the ledger checked for dr is the claim for a
def commit_safe.hit(+a: L.Id, +Lg: L.Ledger, +dr: L.Id, +cr: L.Id, +amt: Nat, +st: L.St, eq: {dr == a : L.Id},
  gd: Laws.SafeIf(L.guarded(dr), Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg))))
  -> Laws.SafeIf(L.guarded(a), Nat.add(amt, L.debits(a, L.log(Lg))), Nat.add(K.when(L.posted(st) && L.Id.eq(cr, a), amt), L.cposted(a, L.log(Lg)))):
  %eq : Laws.SafeIf(L.guarded(_), Nat.add(amt, L.debits(_, L.log(Lg))), Nat.add(K.when(L.posted(st) && L.Id.eq(cr, _), amt), L.cposted(_, L.log(Lg))))
  +X = Nat.add(amt, L.debits(dr, L.log(Lg)))
  +Y = L.cposted(dr, L.log(Lg))
  +w = K.when(L.posted(st) && L.Id.eq(cr, dr), amt)
  safeif_mono(L.guarded(dr), X, X, Y, Nat.add(w, Y), le_refl(X), gd, le_add_l(w, Y))

def commit_safe.go(+a: L.Id, +Lg: L.Ledger, +dr: L.Id, +cr: L.Id, +amt: Nat, +st: L.St,
  s: Laws.Safe(a, Lg),
  gd: Laws.SafeIf(L.guarded(dr), Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg))))
  -> Laws.SafeIf(L.guarded(a), Nat.add(K.when(True{} && L.Id.eq(dr, a), amt), L.debits(a, L.log(Lg))), Nat.add(K.when(L.posted(st) && L.Id.eq(cr, a), amt), L.cposted(a, L.log(Lg)))):
  +D = L.debits(a, L.log(Lg))
  +C = L.cposted(a, L.log(Lg))
  +w = K.when(L.posted(st) && L.Id.eq(cr, a), amt)
  bool_case(L.Id.eq(dr, a), b => Laws.SafeIf(L.guarded(a), Nat.add(K.when(b, amt), D), Nat.add(w, C)),
    e => commit_safe.hit(a, Lg, dr, cr, amt, st, id_eq_sound(dr, a, sym(Bool, True{}, L.Id.eq(dr, a), e)), gd),
    e => safeif_mono(L.guarded(a), D, D, C, Nat.add(w, C), le_refl(D), s, le_add_l(w, C)))

def commit_safe(+a: L.Id, +Lg: L.Ledger, -id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, p: Bool,
  s: Laws.Safe(a, Lg),
  gd: Laws.SafeIf(L.guarded(dr), Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg))))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.commit(Lg, id, dr, cr, amt, p))):
  match p:
    case True{}:
      commit_safe.go(a, Lg, dr, cr, amt, L.Pending{}, s, gd)
    case False{}:
      commit_safe.go(a, Lg, dr, cr, amt, L.Posted{}, s, gd)

# Walking create's checks
# -----------------------
# One lemma per helper of L.create: every rejection returns the ledger as
# it was, so Safe carries over; the two paths that commit hand commit_safe
# the guard, either vacuous (dr unguarded) or the evidence le_case produced.

def sif_true(-g: Bool, -x: Nat, -y: Nat, eg: {g == True{} : Bool}, h: K.LE(x, y)) -> Laws.SafeIf(g, x, y):
  %sym(Bool, g, True{}, eg) : Laws.SafeIf(_, x, y)
  h

def sif_false(-g: Bool, -x: Nat, -y: Nat, eg: {g == False{} : Bool}) -> Laws.SafeIf(g, x, y):
  %sym(Bool, g, False{}, eg) : Laws.SafeIf(_, x, y)
  Unit{}

def safe_g(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool,
  c: Or(K.LE(Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg))), K.LE(1n+L.cposted(dr, L.log(Lg)), Nat.add(amt, L.debits(dr, L.log(Lg))))))
  -> {L.guarded(dr) == True{} : Bool} -> Laws.Safe(a, Lg)
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.g(Lg, id, dr, cr, amt, p, Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg)), c))):
  match c:
    case Inl{h}:
      eg => s => commit_safe(a, Lg, id, dr, cr, amt, p, s, sif_true(L.guarded(dr), Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg)), eg, h))
    case Inr{h}:
      eg => s => s

def safe_f(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, g: Bool)
  -> {L.guarded(dr) == g : Bool} -> Laws.Safe(a, Lg)
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.f(Lg, id, dr, cr, amt, p, g))):
  match g:
    case False{}:
      eg => s => commit_safe(a, Lg, id, dr, cr, amt, p, s, sif_false(L.guarded(dr), Nat.add(amt, L.debits(dr, L.log(Lg))), L.cposted(dr, L.log(Lg)), eg))
    case True{}:
      +x = Nat.add(amt, L.debits(dr, L.log(Lg)))
      +y = L.cposted(dr, L.log(Lg))
      safe_g(a, Lg, id, dr, cr, amt, p, K.le_case(x, y))

def safe_e(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, ex: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.e(Lg, id, dr, cr, amt, p, ex))):
  match ex:
    case True{}:
      s
    case False{}:
      safe_f(a, Lg, id, dr, cr, amt, p, L.guarded(dr), {==}, s)

def safe_d(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, sl: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.d(Lg, id, dr, cr, amt, p, sl))):
  match sl:
    case False{}:
      s
    case True{}:
      safe_e(a, Lg, id, dr, cr, amt, p, L.has_id(id, L.ids(Lg)), s)

def safe_c(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.c(Lg, id, dr, cr, amt, p, found))):
  match found:
    case False{}:
      s
    case True{}:
      safe_d(a, Lg, id, dr, cr, amt, p, Nat.is_eq(L.ledger_of(dr), L.ledger_of(cr)), s)

def safe_b(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.b(Lg, id, dr, cr, amt, p, found))):
  match found:
    case False{}:
      s
    case True{}:
      safe_c(a, Lg, id, dr, cr, amt, p, L.has_acct(cr, L.accts(Lg)), s)

def safe_a(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, same: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.create.a(Lg, id, dr, cr, amt, p, same))):
  match same:
    case True{}:
      s
    case False{}:
      safe_b(a, Lg, id, dr, cr, amt, p, L.has_acct(dr, L.accts(Lg)), s)

# Posting and voiding
# -------------------
# Resolving a pending entry never adds debits (Pending -> Settled keeps
# them, Pending -> Voided drops them) and never removes posted credits
# (Pending -> Settled adds them, Pending -> Voided keeps them).

def settle_d1(b: Bool, st: L.St, post: Bool, +E: Bool, +amt: Nat)
  -> K.LE(K.when(L.live(L.settle.one(b, st, post)) && E, amt), K.when(L.live(st) && E, amt)):
  match b:
    case False{}:
      le_refl(K.when(L.live(st) && E, amt))
    case True{}:
      match st:
        case L.Pending{}:
          match post:
            case True{}:
              le_refl(K.when(E, amt))
            case False{}:
              Unit{}
        case L.Posted{}:
          le_refl(K.when(E, amt))
        case L.Settled{}:
          le_refl(K.when(E, amt))
        case L.Voided{}:
          Unit{}

def settle_c1(b: Bool, st: L.St, post: Bool, +E: Bool, +amt: Nat)
  -> K.LE(K.when(L.posted(st) && E, amt), K.when(L.posted(L.settle.one(b, st, post)) && E, amt)):
  match b:
    case False{}:
      le_refl(K.when(L.posted(st) && E, amt))
    case True{}:
      match st:
        case L.Pending{}:
          Unit{}
        case L.Posted{}:
          le_refl(K.when(E, amt))
        case L.Settled{}:
          le_refl(K.when(E, amt))
        case L.Voided{}:
          Unit{}

def settle_debits(+log: List<&2, L.Entry>, +a: L.Id, +pid: Nat, +post: Bool)
  -> K.LE(L.debits(a, L.settle(pid, post, log)), L.debits(a, log)):
  match log:
    case Nil{}:
      Unit{}
    case L.Entry{+i, +dr, +cr, +amt, +st} <> rest:
      +E = L.Id.eq(dr, a)
      le_add_both(K.when(L.live(L.settle.one(Nat.is_eq(i, pid), st, post)) && E, amt), K.when(L.live(st) && E, amt),
        L.debits(a, L.settle(pid, post, rest)), L.debits(a, rest),
        settle_d1(Nat.is_eq(i, pid), st, post, E, amt), settle_debits(rest, a, pid, post))

def settle_cposted(+log: List<&2, L.Entry>, +a: L.Id, +pid: Nat, +post: Bool)
  -> K.LE(L.cposted(a, log), L.cposted(a, L.settle(pid, post, log))):
  match log:
    case Nil{}:
      Unit{}
    case L.Entry{+i, +dr, +cr, +amt, +st} <> rest:
      +E = L.Id.eq(cr, a)
      le_add_both(K.when(L.posted(st) && E, amt), K.when(L.posted(L.settle.one(Nat.is_eq(i, pid), st, post)) && E, amt),
        L.cposted(a, rest), L.cposted(a, L.settle(pid, post, rest)),
        settle_c1(Nat.is_eq(i, pid), st, post, E, amt), settle_cposted(rest, a, pid, post))

def finish_safe(+a: L.Id, +Lg: L.Ledger, -id: Nat, +pid: Nat, +post: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.finish(Lg, id, pid, post))):
  +log = L.log(Lg)
  safeif_mono(L.guarded(a), L.debits(a, L.settle(pid, post, log)), L.debits(a, log), L.cposted(a, log), L.cposted(a, L.settle(pid, post, log)),
    settle_debits(log, a, pid, post), s, settle_cposted(log, a, pid, post))

def safe_rc(+a: L.Id, +Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, st: L.St, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.resolve.c(Lg, id, pid, post, st))):
  match st:
    case L.Pending{}:
      finish_safe(a, Lg, id, pid, post, s)
    case L.Settled{}:
      s
    case L.Voided{}:
      s
    case L.Posted{}:
      s

def safe_rb(+a: L.Id, +Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, +st: L.St, ex: Bool, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.resolve.b(Lg, id, pid, post, st, ex))):
  match ex:
    case True{}:
      s
    case False{}:
      safe_rc(a, Lg, id, pid, post, st, s)

def safe_ra(+a: L.Id, +Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, found: Maybe<&2, L.St>, s: Laws.Safe(a, Lg))
  -> Laws.Safe(a, Pair.fst(L.Ledger, L.Status, L.resolve.a(Lg, id, pid, post, found))):
  match found:
    case None{}:
      s
    case Some{st}:
      match st:
        case L.Posted{}:
          s
        case L.Pending{}:
          safe_rb(a, Lg, id, pid, post, L.Pending{}, L.has_id(id, L.ids(Lg)), s)
        case L.Settled{}:
          safe_rb(a, Lg, id, pid, post, L.Settled{}, L.has_id(id, L.ids(Lg)), s)
        case L.Voided{}:
          safe_rb(a, Lg, id, pid, post, L.Voided{}, L.has_id(id, L.ids(Lg)), s)

# LAW no_overdraft
def Laws.no_overdraft(a, Lg, op, s):
  match op:
    case L.Create{+id, +dr, +cr, +amt, +pending}:
      safe_a(a, Lg, id, dr, cr, amt, pending, L.Id.eq(dr, cr), s)
    case L.Post{+id, +pid}:
      safe_ra(a, Lg, id, pid, True{}, L.find(pid, L.log(Lg)), s)
    case L.Void{+id, +pid}:
      safe_ra(a, Lg, id, pid, False{}, L.find(pid, L.log(Lg)), s)

# Chains
# ======

# what a chain's run leaves behind is safe (an abort leaves nothing)
def SafeOut(+a: L.Id, out: L.Out) -> Data:
  match out:
    case L.Committed{L1}:
      Laws.Safe(a, L1)
    case L.Aborted{at, why}:
      Unit

def pick_safe(+a: L.Id, ok: Bool, -why: L.Status, rec: L.Out, h: SafeOut(a, rec)) -> SafeOut(a, L.run.pick(ok, why, rec)):
  match ok:
    case True{}:
      match rec:
        case L.Committed{L1}:
          h
        case L.Aborted{at, w}:
          Unit{}
    case False{}:
      Unit{}

def run_safe(+ops: List<&2, L.Op>, +a: L.Id, +Lg: L.Ledger, s: Laws.Safe(a, Lg)) -> SafeOut(a, L.run(ops, Lg)):
  match ops:
    case Nil{}:
      s
    case op <> rest:
      +o = op
      pick_safe(a, L.is_ok(L.status(Lg, o)), L.status(Lg, o), L.run(rest, L.after(Lg, o)),
        run_safe(rest, a, L.after(Lg, o), Laws.no_overdraft(a, Lg, o, s)))

def fin_safe(+a: L.Id, +Lg: L.Ledger, -n: Nat, out: L.Out, s: Laws.Safe(a, Lg), h: SafeOut(a, out))
  -> Laws.Safe(a, Pair.fst(L.Ledger, List<&2, L.Status>, L.chain.fin(Lg, n, out))):
  match out:
    case L.Committed{L1}:
      h
    case L.Aborted{at, why}:
      s

# LAW chain_no_overdraft
def Laws.chain_no_overdraft(a, Lg, ops, s):
  fin_safe(a, Lg, List.length(&2, L.Op, ops), L.run(ops, Lg), s, run_safe(ops, a, Lg, s))

# All or nothing
# --------------

def oks_ok(n: Nat) -> {Laws.all_ok(L.oks(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      oks_ok(p)

def fin_aon(+Lg: L.Ledger, +n: Nat, out: L.Out)
  -> Or({Pair.fst(L.Ledger, List<&2, L.Status>, L.chain.fin(Lg, n, out)) == Lg : L.Ledger},
        {Laws.all_ok(Pair.snd(L.Ledger, List<&2, L.Status>, L.chain.fin(Lg, n, out))) == True{} : Bool}):
  match out:
    case L.Committed{L1}:
      Inr{oks_ok(n)}
    case L.Aborted{at, why}:
      Inl{{==}}

# LAW all_or_nothing
def Laws.all_or_nothing(Lg, ops):
  fin_aon(Lg, List.length(&2, L.Op, ops), L.run(ops, Lg))

# Only the holder
# ---------------

# LAW only_holder_pays: a hold u does not own plans no transfers at all
def Laws.only_holder_pays(Lg, u, t1, t2, p1, p2, e):
  %sym(Bool, B.owns(Lg, u, t1, t2), False{}, e) : {Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(Lg, B.guard_ops(_, [L.Post{p1, t1}, L.Post{p2, t2}]))) == Lg : L.Ledger}
  {==}

# LAW only_holder_releases
def Laws.only_holder_releases(Lg, u, t1, t2, p1, p2, e):
  %sym(Bool, B.owns(Lg, u, t1, t2), False{}, e) : {Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(Lg, B.guard_ops(_, [L.Void{p1, t1}, L.Void{p2, t2}]))) == Lg : L.Ledger}
  {==}

# The box office
# ==============

# Opening accounts touches no balance
# -----------------------------------

def open_pick_safe(+a: L.Id, +Lg: L.Ledger, +x: L.Id, ex: Bool, s: Laws.Safe(a, Lg)) -> Laws.Safe(a, L.open.pick(Lg, x, ex)):
  match ex:
    case True{}:
      s
    case False{}:
      s

def open_safe(+a: L.Id, +Lg: L.Ledger, +x: L.Id, s: Laws.Safe(a, Lg)) -> Laws.Safe(a, L.open(Lg, x)):
  open_pick_safe(a, Lg, x, L.has_acct(x, L.accts(Lg)), s)

def opens_safe(+a: L.Id, +Lg: L.Ledger, cmd: B.Cmd, s: Laws.Safe(a, Lg)) -> Laws.Safe(a, B.opens(Lg, cmd)):
  match cmd:
    case B.Join{+u, fund}:
      open_safe(a, L.open(Lg, L.Wallet{u}), L.Tickets{u}, open_safe(a, Lg, L.Wallet{u}, s))
    case B.Hold{u, k, t1, t2}:
      s
    case B.Pay{u, t1, t2, p1, p2}:
      s
    case B.Release{u, t1, t2, p1, p2}:
      s

def next_safe(+a: L.Id, +Lg: L.Ledger, +cmd: B.Cmd, s: Laws.Safe(a, Lg)) -> Laws.Safe(a, B.next(Lg, cmd)):
  +Lo = B.opens(Lg, cmd)
  Laws.chain_no_overdraft(a, Lo, B.plan(Lo, cmd), opens_safe(a, Lg, cmd, s))

def replay_safe(+cmds: List<&2, B.Cmd>, +a: L.Id, +Lg: L.Ledger, s: Laws.Safe(a, Lg)) -> Laws.Safe(a, B.replay(cmds, Lg)):
  match cmds:
    case Nil{}:
      s
    case c <> rest:
      replay_safe(rest, a, B.next(Lg, c), next_safe(a, Lg, c, s))

# LAW wallet_never_overdrawn: opening day owes nothing, and every command
# keeps it so
def Laws.wallet_never_overdrawn(u, cmds):
  replay_safe(cmds, L.Wallet{u}, B.genesis(), Unit{})

# Credits a seat can ever receive
# -------------------------------
# credits_any(a) counts every credit to a, whatever its state. It bounds
# credits_posted, and only a Create that credits a can raise it.

def cp_le_ca1(st: L.St, +E: Bool, +amt: Nat) -> K.LE(K.when(L.posted(st) && E, amt), K.when(E, amt)):
  match st:
    case L.Posted{}:
      le_refl(K.when(E, amt))
    case L.Pending{}:
      Unit{}
    case L.Settled{}:
      le_refl(K.when(E, amt))
    case L.Voided{}:
      Unit{}

def cp_le_ca(+log: List<&2, L.Entry>, +a: L.Id) -> K.LE(L.cposted(a, log), L.credits_any(a, log)):
  match log:
    case Nil{}:
      Unit{}
    case L.Entry{+i, +dr, +cr, +amt, +st} <> rest:
      +E = L.Id.eq(cr, a)
      le_add_both(K.when(L.posted(st) && E, amt), K.when(E, amt), L.cposted(a, rest), L.credits_any(a, rest),
        cp_le_ca1(st, E, amt), cp_le_ca(rest, a))

def settle_ca(+log: List<&2, L.Entry>, +a: L.Id, +pid: Nat, +post: Bool)
  -> {L.credits_any(a, L.settle(pid, post, log)) == L.credits_any(a, log) : Nat}:
  match log:
    case Nil{}:
      {==}
    case L.Entry{+i, +dr, +cr, +amt, +st} <> rest:
      +w = K.when(L.Id.eq(cr, a), amt)
      %settle_ca(rest, a, pid, post) : {Nat.add(w, L.credits_any(a, L.settle(pid, post, rest))) == Nat.add(w, _) : Nat}
      {==}

# the credit an operation can add to a
def op_credit(+a: L.Id, op: L.Op) -> Nat:
  match op:
    case L.Create{id, dr, cr, amt, p}:
      K.when(L.Id.eq(cr, a), amt)
    case L.Post{id, pid}:
      0n
    case L.Void{id, pid}:
      0n

# The shape of one transfer
# -------------------------
# Whatever its checks decide, a transfer either leaves the ledger as it was
# or commits exactly one new entry (create) or resolves one (post, void).

def CShape(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, -r: L.Ledger & L.Status) -> Type:
  Or({Pair.fst(L.Ledger, L.Status, r) == Lg : L.Ledger},
     {Pair.fst(L.Ledger, L.Status, r) == Pair.fst(L.Ledger, L.Status, L.commit(Lg, id, dr, cr, amt, p)) : L.Ledger})

def RShape(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, -r: L.Ledger & L.Status) -> Type:
  Or({Pair.fst(L.Ledger, L.Status, r) == Lg : L.Ledger},
     {Pair.fst(L.Ledger, L.Status, r) == Pair.fst(L.Ledger, L.Status, L.finish(Lg, id, pid, post)) : L.Ledger})

def shape_g(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, +x: Nat, +y: Nat, c: Or(K.LE(x, y), K.LE(1n+y, x)))
  -> CShape(Lg, id, dr, cr, amt, p, L.create.g(Lg, id, dr, cr, amt, p, x, y, c)):
  match c:
    case Inl{h}:
      Inr{{==}}
    case Inr{h}:
      Inl{{==}}

def shape_f(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, g: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.f(Lg, id, dr, cr, amt, p, g)):
  match g:
    case False{}:
      Inr{{==}}
    case True{}:
      +x = Nat.add(amt, L.debits(dr, L.log(Lg)))
      +y = L.cposted(dr, L.log(Lg))
      shape_g(Lg, id, dr, cr, amt, p, x, y, K.le_case(x, y))

def shape_e(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, ex: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.e(Lg, id, dr, cr, amt, p, ex)):
  match ex:
    case True{}:
      Inl{{==}}
    case False{}:
      shape_f(Lg, id, dr, cr, amt, p, L.guarded(dr))

def shape_d(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, sl: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.d(Lg, id, dr, cr, amt, p, sl)):
  match sl:
    case False{}:
      Inl{{==}}
    case True{}:
      shape_e(Lg, id, dr, cr, amt, p, L.has_id(id, L.ids(Lg)))

def shape_c(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.c(Lg, id, dr, cr, amt, p, found)):
  match found:
    case False{}:
      Inl{{==}}
    case True{}:
      shape_d(Lg, id, dr, cr, amt, p, Nat.is_eq(L.ledger_of(dr), L.ledger_of(cr)))

def shape_b(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.b(Lg, id, dr, cr, amt, p, found)):
  match found:
    case False{}:
      Inl{{==}}
    case True{}:
      shape_c(Lg, id, dr, cr, amt, p, L.has_acct(cr, L.accts(Lg)))

def shape_a(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, same: Bool)
  -> CShape(Lg, id, dr, cr, amt, p, L.create.a(Lg, id, dr, cr, amt, p, same)):
  match same:
    case True{}:
      Inl{{==}}
    case False{}:
      shape_b(Lg, id, dr, cr, amt, p, L.has_acct(dr, L.accts(Lg)))

def shape_rc(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, st: L.St)
  -> RShape(Lg, id, pid, post, L.resolve.c(Lg, id, pid, post, st)):
  match st:
    case L.Pending{}:
      Inr{{==}}
    case L.Settled{}:
      Inl{{==}}
    case L.Voided{}:
      Inl{{==}}
    case L.Posted{}:
      Inl{{==}}

def shape_rb(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, +st: L.St, ex: Bool)
  -> RShape(Lg, id, pid, post, L.resolve.b(Lg, id, pid, post, st, ex)):
  match ex:
    case True{}:
      Inl{{==}}
    case False{}:
      shape_rc(Lg, id, pid, post, st)

def shape_ra(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, found: Maybe<&2, L.St>)
  -> RShape(Lg, id, pid, post, L.resolve.a(Lg, id, pid, post, found)):
  match found:
    case None{}:
      Inl{{==}}
    case Some{st}:
      match st:
        case L.Posted{}:
          Inl{{==}}
        case L.Pending{}:
          shape_rb(Lg, id, pid, post, L.Pending{}, L.has_id(id, L.ids(Lg)))
        case L.Settled{}:
          shape_rb(Lg, id, pid, post, L.Settled{}, L.has_id(id, L.ids(Lg)))
        case L.Voided{}:
          shape_rb(Lg, id, pid, post, L.Voided{}, L.has_id(id, L.ids(Lg)))

# One transfer raises credits_any(a) by at most op_credit(a)
# ----------------------------------------------------------

def credit_create(+a: L.Id, +Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, -r: L.Ledger & L.Status, sh: CShape(Lg, id, dr, cr, amt, p, r))
  -> K.LE(L.credits_any(a, L.log(Pair.fst(L.Ledger, L.Status, r))), Nat.add(K.when(L.Id.eq(cr, a), amt), L.credits_any(a, L.log(Lg)))):
  match sh:
    case Inl{e}:
      +w = K.when(L.Id.eq(cr, a), amt)
      +C = L.credits_any(a, L.log(Lg))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), Lg, e) : K.LE(L.credits_any(a, L.log(_)), Nat.add(w, C))
      le_add_l(w, C)
    case Inr{e}:
      +w = K.when(L.Id.eq(cr, a), amt)
      +C = L.credits_any(a, L.log(Lg))
      +c = Pair.fst(L.Ledger, L.Status, L.commit(Lg, id, dr, cr, amt, p))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), c, e) : K.LE(L.credits_any(a, L.log(_)), Nat.add(w, C))
      le_refl(Nat.add(w, C))

def credit_resolve(+a: L.Id, +Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, -r: L.Ledger & L.Status, sh: RShape(Lg, id, pid, post, r))
  -> K.LE(L.credits_any(a, L.log(Pair.fst(L.Ledger, L.Status, r))), L.credits_any(a, L.log(Lg))):
  match sh:
    case Inl{e}:
      +C = L.credits_any(a, L.log(Lg))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), Lg, e) : K.LE(L.credits_any(a, L.log(_)), C)
      le_refl(C)
    case Inr{e}:
      +C = L.credits_any(a, L.log(Lg))
      +f = Pair.fst(L.Ledger, L.Status, L.finish(Lg, id, pid, post))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), f, e) : K.LE(L.credits_any(a, L.log(_)), C)
      %sym(Nat, L.credits_any(a, L.settle(pid, post, L.log(Lg))), C, settle_ca(L.log(Lg), a, pid, post)) : K.LE(_, C)
      le_refl(C)

def credit_step(+a: L.Id, +Lg: L.Ledger, +op: L.Op)
  -> K.LE(L.credits_any(a, L.log(L.after(Lg, op))), Nat.add(op_credit(a, op), L.credits_any(a, L.log(Lg)))):
  match op:
    case L.Create{+id, +dr, +cr, +amt, +p}:
      credit_create(a, Lg, id, dr, cr, amt, p, L.create.a(Lg, id, dr, cr, amt, p, L.Id.eq(dr, cr)), shape_a(Lg, id, dr, cr, amt, p, L.Id.eq(dr, cr)))
    case L.Post{+id, +pid}:
      credit_resolve(a, Lg, id, pid, True{}, L.resolve.a(Lg, id, pid, True{}, L.find(pid, L.log(Lg))), shape_ra(Lg, id, pid, True{}, L.find(pid, L.log(Lg))))
    case L.Void{+id, +pid}:
      credit_resolve(a, Lg, id, pid, False{}, L.resolve.a(Lg, id, pid, False{}, L.find(pid, L.log(Lg))), shape_ra(Lg, id, pid, False{}, L.find(pid, L.log(Lg))))

# Through chains and commands
# ---------------------------

# ZC(a, ops): no operation of the chain credits a
def ZC(+a: L.Id, ops: List<&2, L.Op>) -> Type:
  match ops:
    case Nil{}:
      Unit
    case op <> rest:
      (K.LE(op_credit(a, op), 0n) & ZC(a, rest))

def BoundOut(+a: L.Id, +n: Nat, out: L.Out) -> Data:
  match out:
    case L.Committed{L1}:
      K.LE(L.credits_any(a, L.log(L1)), n)
    case L.Aborted{at, why}:
      Unit

# c <= 0 means c + y is just y
def drop_zero(c: Nat, +y: Nat, z: K.LE(c, 0n)) -> K.LE(Nat.add(c, y), y):
  match c:
    case 0n:
      le_refl(y)
    case 1n+c1:
      Empty.absurd(K.LE(Nat.add(1n+c1, y), y), z)

def pick_bound(+a: L.Id, +n: Nat, ok: Bool, -why: L.Status, rec: L.Out, h: BoundOut(a, n, rec)) -> BoundOut(a, n, L.run.pick(ok, why, rec)):
  match ok:
    case True{}:
      match rec:
        case L.Committed{L1}:
          h
        case L.Aborted{at, w}:
          Unit{}
    case False{}:
      Unit{}

def run_bound(+ops: List<&2, L.Op>, +a: L.Id, +n: Nat, +Lg: L.Ledger, b: K.LE(L.credits_any(a, L.log(Lg)), n), z: ZC(a, ops))
  -> BoundOut(a, n, L.run(ops, Lg)):
  match ops:
    case Nil{}:
      b
    case op <> rest:
      (z1, zr) = z
      +o = op
      +C = L.credits_any(a, L.log(Lg))
      +oc = op_credit(a, o)
      +C1 = L.credits_any(a, L.log(L.after(Lg, o)))
      b1 = le_trans(C1, Nat.add(oc, C), n, credit_step(a, Lg, o), le_trans(Nat.add(oc, C), C, n, drop_zero(oc, C, z1), b))
      pick_bound(a, n, L.is_ok(L.status(Lg, o)), L.status(Lg, o), L.run(rest, L.after(Lg, o)),
        run_bound(rest, a, n, L.after(Lg, o), b1, zr))

def fin_bound(+a: L.Id, +n: Nat, +Lg: L.Ledger, -len: Nat, out: L.Out, b: K.LE(L.credits_any(a, L.log(Lg)), n), h: BoundOut(a, n, out))
  -> K.LE(L.credits_any(a, L.log(Pair.fst(L.Ledger, List<&2, L.Status>, L.chain.fin(Lg, len, out)))), n):
  match out:
    case L.Committed{L1}:
      h
    case L.Aborted{at, why}:
      b

def chain_bound(+a: L.Id, +n: Nat, +Lg: L.Ledger, +ops: List<&2, L.Op>, +b: K.LE(L.credits_any(a, L.log(Lg)), n), z: ZC(a, ops))
  -> K.LE(L.credits_any(a, L.log(Pair.fst(L.Ledger, List<&2, L.Status>, L.chain(Lg, ops)))), n):
  fin_bound(a, n, Lg, List.length(&2, L.Op, ops), L.run(ops, Lg), b, run_bound(ops, a, n, Lg, b, z))

# no command's chain credits a seat
def zc_guard(+a: L.Id, b: Bool, -ops: List<&2, L.Op>, z: ZC(a, ops)) -> ZC(a, B.guard_ops(b, ops)):
  match b:
    case True{}:
      z
    case False{}:
      Unit{}

def zc_plan(+k: Nat, +Lg: L.Ledger, cmd: B.Cmd) -> ZC(L.Seat{k}, B.plan(Lg, cmd)):
  match cmd:
    case B.Join{u, fund}:
      (Unit{}, Unit{})
    case B.Hold{u, j, t1, t2}:
      (Unit{}, (Unit{}, Unit{}))
    case B.Pay{+u, +t1, +t2, p1, p2}:
      zc_guard(L.Seat{k}, B.owns(Lg, u, t1, t2), [L.Post{p1, t1}, L.Post{p2, t2}], (Unit{}, (Unit{}, Unit{})))
    case B.Release{+u, +t1, +t2, p1, p2}:
      zc_guard(L.Seat{k}, B.owns(Lg, u, t1, t2), [L.Void{p1, t1}, L.Void{p2, t2}], (Unit{}, (Unit{}, Unit{})))

# opening accounts leaves the log alone
def open_pick_bound(+a: L.Id, +n: Nat, +Lg: L.Ledger, +x: L.Id, ex: Bool, b: K.LE(L.credits_any(a, L.log(Lg)), n))
  -> K.LE(L.credits_any(a, L.log(L.open.pick(Lg, x, ex))), n):
  match ex:
    case True{}:
      b
    case False{}:
      b

def open_bound(+a: L.Id, +n: Nat, +Lg: L.Ledger, +x: L.Id, b: K.LE(L.credits_any(a, L.log(Lg)), n))
  -> K.LE(L.credits_any(a, L.log(L.open(Lg, x))), n):
  open_pick_bound(a, n, Lg, x, L.has_acct(x, L.accts(Lg)), b)

def opens_bound(+a: L.Id, +n: Nat, +Lg: L.Ledger, cmd: B.Cmd, b: K.LE(L.credits_any(a, L.log(Lg)), n))
  -> K.LE(L.credits_any(a, L.log(B.opens(Lg, cmd))), n):
  match cmd:
    case B.Join{+u, fund}:
      open_bound(a, n, L.open(Lg, L.Wallet{u}), L.Tickets{u}, open_bound(a, n, Lg, L.Wallet{u}, b))
    case B.Hold{u, k, t1, t2}:
      b
    case B.Pay{u, t1, t2, p1, p2}:
      b
    case B.Release{u, t1, t2, p1, p2}:
      b

def next_bound(+k: Nat, +Lg: L.Ledger, +cmd: B.Cmd, b: K.LE(L.credits_any(L.Seat{k}, L.log(Lg)), 1n))
  -> K.LE(L.credits_any(L.Seat{k}, L.log(B.next(Lg, cmd))), 1n):
  +Lo = B.opens(Lg, cmd)
  chain_bound(L.Seat{k}, 1n, Lo, B.plan(Lo, cmd), opens_bound(L.Seat{k}, 1n, Lg, cmd, b), zc_plan(k, Lo, cmd))

def replay_bound(+cmds: List<&2, B.Cmd>, +k: Nat, +Lg: L.Ledger, b: K.LE(L.credits_any(L.Seat{k}, L.log(Lg)), 1n))
  -> K.LE(L.credits_any(L.Seat{k}, L.log(B.replay(cmds, Lg))), 1n):
  match cmds:
    case Nil{}:
      b
    case c <> rest:
      replay_bound(rest, k, B.next(Lg, c), next_bound(k, Lg, c, b))

# Opening day
# -----------
# Opening day credits each of the twelve seats exactly once. For an open
# k the sum does not compute, so the proof peels k twelve times: in every
# branch the issue entries' Nat.is_eq tests become concrete.

def genesis_bound(k: Nat) -> K.LE(L.credits_any(L.Seat{k}, L.log(B.genesis())), 1n):
  match k:
    case 0n:
      Unit{}
    case 1n+k1:
      match k1:
        case 0n:
          Unit{}
        case 1n+k2:
          match k2:
            case 0n:
              Unit{}
            case 1n+k3:
              match k3:
                case 0n:
                  Unit{}
                case 1n+k4:
                  match k4:
                    case 0n:
                      Unit{}
                    case 1n+k5:
                      match k5:
                        case 0n:
                          Unit{}
                        case 1n+k6:
                          match k6:
                            case 0n:
                              Unit{}
                            case 1n+k7:
                              match k7:
                                case 0n:
                                  Unit{}
                                case 1n+k8:
                                  match k8:
                                    case 0n:
                                      Unit{}
                                    case 1n+k9:
                                      match k9:
                                        case 0n:
                                          Unit{}
                                        case 1n+k10:
                                          match k10:
                                            case 0n:
                                              Unit{}
                                            case 1n+k11:
                                              match k11:
                                                case 0n:
                                                  Unit{}
                                                case 1n+k12:
                                                  Unit{}

# LAW seat_never_oversold: debits <= credits_posted (the guard, kept by
# every command) <= every credit ever made (1, kept by every command)
def Laws.seat_never_oversold(k, cmds):
  +R = B.replay(cmds, B.genesis())
  +a = {L.Seat{k} : L.Id}
  +D = L.debits(a, L.log(R))
  +P = L.cposted(a, L.log(R))
  +A = L.credits_any(a, L.log(R))
  le_trans(D, P, 1n, replay_safe(cmds, a, B.genesis(), Unit{}),
    le_trans(P, A, 1n, cp_le_ca(L.log(R), a), replay_bound(cmds, k, B.genesis(), genesis_bound(k))))

# Retries
# =======

def has_own(+id: Nat, +ids: List<&2, Nat>) -> {L.has_id(id, id <> ids) == True{} : Bool}:
  %sym(Bool, Nat.is_eq(id, id), True{}, nat_eq_refl(id)) : {_ || L.has_id(id, ids) == True{} : Bool}
  {==}

# after one attempt, the ledger is either untouched or remembers the id
def Mark(+Lg: L.Ledger, +id: Nat, -r: L.Ledger & L.Status) -> Type:
  Or({Pair.fst(L.Ledger, L.Status, r) == Lg : L.Ledger},
     {L.has_id(id, L.ids(Pair.fst(L.Ledger, L.Status, r))) == True{} : Bool})

def mark_create(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, -r: L.Ledger & L.Status, sh: CShape(Lg, id, dr, cr, amt, p, r))
  -> Mark(Lg, id, r):
  match sh:
    case Inl{e}:
      Inl{e}
    case Inr{e}:
      +c = Pair.fst(L.Ledger, L.Status, L.commit(Lg, id, dr, cr, amt, p))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), c, e) : Or({_ == Lg : L.Ledger}, {L.has_id(id, L.ids(_)) == True{} : Bool})
      Inr{has_own(id, L.ids(Lg))}

def mark_resolve(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, -r: L.Ledger & L.Status, sh: RShape(Lg, id, pid, post, r))
  -> Mark(Lg, id, r):
  match sh:
    case Inl{e}:
      Inl{e}
    case Inr{e}:
      +f = Pair.fst(L.Ledger, L.Status, L.finish(Lg, id, pid, post))
      %sym(L.Ledger, Pair.fst(L.Ledger, L.Status, r), f, e) : Or({_ == Lg : L.Ledger}, {L.has_id(id, L.ids(_)) == True{} : Bool})
      Inr{has_own(id, L.ids(Lg))}

def mark(+Lg: L.Ledger, op: L.Op) -> Or({L.after(Lg, op) == Lg : L.Ledger}, {L.has_id(L.op_id(op), L.ids(L.after(Lg, op))) == True{} : Bool}):
  match op:
    case L.Create{+id, +dr, +cr, +amt, +p}:
      mark_create(Lg, id, dr, cr, amt, p, L.create.a(Lg, id, dr, cr, amt, p, L.Id.eq(dr, cr)), shape_a(Lg, id, dr, cr, amt, p, L.Id.eq(dr, cr)))
    case L.Post{+id, +pid}:
      mark_resolve(Lg, id, pid, True{}, L.resolve.a(Lg, id, pid, True{}, L.find(pid, L.log(Lg))), shape_ra(Lg, id, pid, True{}, L.find(pid, L.log(Lg))))
    case L.Void{+id, +pid}:
      mark_resolve(Lg, id, pid, False{}, L.resolve.a(Lg, id, pid, False{}, L.find(pid, L.log(Lg))), shape_ra(Lg, id, pid, False{}, L.find(pid, L.log(Lg))))

# a remembered id is refused before anything is written
def Same(+Lg: L.Ledger, -r: L.Ledger & L.Status) -> Type:
  {Pair.fst(L.Ledger, L.Status, r) == Lg : L.Ledger}

def seen_e(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, ex: Bool)
  -> {ex == True{} : Bool} -> Same(Lg, L.create.e(Lg, id, dr, cr, amt, p, ex)):
  match ex:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd(Same(Lg, L.create.e(Lg, id, dr, cr, amt, p, False{})), false_true(h))

def seen_d(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, sl: Bool, h: {L.has_id(id, L.ids(Lg)) == True{} : Bool})
  -> Same(Lg, L.create.d(Lg, id, dr, cr, amt, p, sl)):
  match sl:
    case False{}:
      {==}
    case True{}:
      seen_e(Lg, id, dr, cr, amt, p, L.has_id(id, L.ids(Lg)), h)

def seen_c(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool, h: {L.has_id(id, L.ids(Lg)) == True{} : Bool})
  -> Same(Lg, L.create.c(Lg, id, dr, cr, amt, p, found)):
  match found:
    case False{}:
      {==}
    case True{}:
      seen_d(Lg, id, dr, cr, amt, p, Nat.is_eq(L.ledger_of(dr), L.ledger_of(cr)), h)

def seen_b(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, found: Bool, h: {L.has_id(id, L.ids(Lg)) == True{} : Bool})
  -> Same(Lg, L.create.b(Lg, id, dr, cr, amt, p, found)):
  match found:
    case False{}:
      {==}
    case True{}:
      seen_c(Lg, id, dr, cr, amt, p, L.has_acct(cr, L.accts(Lg)), h)

def seen_a(+Lg: L.Ledger, +id: Nat, +dr: L.Id, +cr: L.Id, +amt: Nat, +p: Bool, same: Bool, h: {L.has_id(id, L.ids(Lg)) == True{} : Bool})
  -> Same(Lg, L.create.a(Lg, id, dr, cr, amt, p, same)):
  match same:
    case True{}:
      {==}
    case False{}:
      seen_b(Lg, id, dr, cr, amt, p, L.has_acct(dr, L.accts(Lg)), h)

def seen_rb(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, +st: L.St, ex: Bool)
  -> {ex == True{} : Bool} -> Same(Lg, L.resolve.b(Lg, id, pid, post, st, ex)):
  match ex:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd(Same(Lg, L.resolve.b(Lg, id, pid, post, st, False{})), false_true(h))

def seen_ra(+Lg: L.Ledger, +id: Nat, +pid: Nat, +post: Bool, found: Maybe<&2, L.St>, h: {L.has_id(id, L.ids(Lg)) == True{} : Bool})
  -> Same(Lg, L.resolve.a(Lg, id, pid, post, found)):
  match found:
    case None{}:
      {==}
    case Some{st}:
      match st:
        case L.Posted{}:
          {==}
        case L.Pending{}:
          seen_rb(Lg, id, pid, post, L.Pending{}, L.has_id(id, L.ids(Lg)), h)
        case L.Settled{}:
          seen_rb(Lg, id, pid, post, L.Settled{}, L.has_id(id, L.ids(Lg)), h)
        case L.Voided{}:
          seen_rb(Lg, id, pid, post, L.Voided{}, L.has_id(id, L.ids(Lg)), h)

def seen(+Lg: L.Ledger, op: L.Op) -> {L.has_id(L.op_id(op), L.ids(Lg)) == True{} : Bool} -> {L.after(Lg, op) == Lg : L.Ledger}:
  match op:
    case L.Create{+id, +dr, +cr, +amt, +p}:
      h => seen_a(Lg, id, dr, cr, amt, p, L.Id.eq(dr, cr), h)
    case L.Post{+id, +pid}:
      h => seen_ra(Lg, id, pid, True{}, L.find(pid, L.log(Lg)), h)
    case L.Void{+id, +pid}:
      h => seen_ra(Lg, id, pid, False{}, L.find(pid, L.log(Lg)), h)

def retry.fin(+Lg: L.Ledger, +op: L.Op, m: Or({L.after(Lg, op) == Lg : L.Ledger}, {L.has_id(L.op_id(op), L.ids(L.after(Lg, op))) == True{} : Bool}))
  -> {L.after(L.after(Lg, op), op) == L.after(Lg, op) : L.Ledger}:
  match m:
    case Inl{e}:
      %sym(L.Ledger, L.after(Lg, op), Lg, e) : {L.after(_, op) == L.after(Lg, op) : L.Ledger}
      {==}
    case Inr{h}:
      seen(L.after(Lg, op), op, h)

# LAW retry_is_harmless: the first attempt either did nothing (so the
# second does the same nothing) or remembered the id (so the second is
# refused as Exists before it writes)
def Laws.retry_is_harmless(Lg, op):
  retry.fin(Lg, op, mark(Lg, op))
