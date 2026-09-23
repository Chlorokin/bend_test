# view.bend: the HTML fragments Datastar patches into the page. Each
# fragment carries the id it replaces. Visitor names reach the page only
# through H.text, and a seat's cell is written as pre ++ text ++ post so
# LAWS.bend can show that no name changes the cell's tag structure.

import Base
import ./kit.bend as K
import ./ledger.bend as L
import ./boxoffice.bend as B
import ./html.bend as H

# Inputs from the server
# ----------------------

# a visitor's chosen display name
type Named is Data:
  Named{u: Nat, name: String}

# one of the viewer's holds: its seat, its transfer, seconds left
type Due is Data:
  Due{k: Nat, t1: Nat, secs: Nat}

def name.pick(b: Bool, name: String, rest: String) -> String:
  match b:
    case True{}:
      name
    case False{}:
      rest

def name_of(+u: Nat, names: List<&2, Named>) -> String:
  match names:
    case Nil{}:
      "Guest " ++ Nat.show(u)
    case Named{v, name} <> rest:
      name.pick(Nat.is_eq(v, u), name, name_of(u, rest))

# Formatting
# ----------

def two(+n: Nat) -> String:
  Bool.pick(String, Nat.is_lt(n, 10n), "0" ++ Nat.show(n), Nat.show(n))

def money(+cents: Nat) -> String:
  "$" ++ Nat.show(Nat.div(cents, 100n)) ++ "." ++ two(Nat.mod(cents, 100n))

# seats read A1..A4, B1..B4, C1..C4
def label(+k: Nat) -> String:
  SCon{Chr{U32.from_nat(Nat.add(65n, Nat.div(k, 4n)))}, Nat.show(Nat.add(Nat.mod(k, 4n), 1n))}

# Seats
# -----

def seat_class(s: B.Seat, +viewer: Nat) -> String:
  match s:
    case B.Free{}:
      "seat free"
    case B.Held{u, t1}:
      Bool.pick(String, Nat.is_eq(u, viewer), "seat held mine", "seat held")
    case B.Sold{u}:
      Bool.pick(String, Nat.is_eq(u, viewer), "seat sold mine", "seat sold")

def seat_verb(s: B.Seat) -> String:
  match s:
    case B.Free{}:
      ""
    case B.Held{u, t1}:
      "held by "
    case B.Sold{u}:
      "sold to "

def seat_action(s: B.Seat, +k: Nat) -> String:
  match s:
    case B.Free{}:
      " data-on:click=\"@post('/hold/" ++ Nat.show(k) ++ "')\""
    case B.Held{u, t1}:
      " disabled"
    case B.Sold{u}:
      " disabled"

# what the cell shows of the holder: nothing for a free seat
def shown(s: B.Seat, who: String) -> String:
  match s:
    case B.Free{}:
      ""
    case B.Held{u, t1}:
      who
    case B.Sold{u}:
      who

def seat_pre(+k: Nat, +s: B.Seat, +viewer: Nat) -> String:
  "<button id=\"seat-" ++ Nat.show(k) ++ "\" class=\"" ++ seat_class(s, viewer) ++ "\"" ++ seat_action(s, k) ++ "><b>" ++ label(k) ++ "</b><small>" ++ money(B.price(k)) ++ "</small><i>" ++ seat_verb(s)

def seat_post() -> String:
  "</i></button>"

# one seat's cell: fixed markup around the holder's escaped name
def seat_cell(+k: Nat, +s: B.Seat, +viewer: Nat, who: String) -> String:
  seat_pre(k, s, viewer) ++ (H.text(shown(s, who)) ++ seat_post())

def seat_who(s: B.Seat, +names: List<&2, Named>) -> String:
  match s:
    case B.Free{}:
      ""
    case B.Held{u, t1}:
      name_of(u, names)
    case B.Sold{u}:
      name_of(u, names)

def cells(seats: List<&2, B.Seat>, +k: Nat, +viewer: Nat, +names: List<&2, Named>) -> String:
  match seats:
    case Nil{}:
      ""
    case +s <> rest:
      seat_cell(k, s, viewer, seat_who(s, names)) ++ cells(rest, 1n+k, viewer, names)

def seats(+Lg: L.Ledger, +viewer: Nat, +names: List<&2, Named>) -> String:
  "<div id=\"seats\" class=\"grid\">" ++ cells(B.seat_map(Lg), 0n, viewer, names) ++ "</div>"

# The viewer's wallet
# -------------------

def count_mine.one(s: B.Seat, +viewer: Nat) -> Nat:
  match s:
    case B.Sold{u}:
      Bool.pick(Nat, Nat.is_eq(u, viewer), 1n, 0n)
    case _:
      0n

def count_mine(seats: List<&2, B.Seat>, +viewer: Nat) -> Nat:
  match seats:
    case Nil{}:
      0n
    case s <> rest:
      Nat.add(count_mine.one(s, viewer), count_mine(rest, viewer))

def wallet(+Lg: L.Ledger, +viewer: Nat, +names: List<&2, Named>) -> String:
  "<div id=\"wallet\"><span class=\"who\">" ++ H.text(name_of(viewer, names)) ++ "</span>"
    ++ "<span class=\"bal\">" ++ money(B.balance(Lg, viewer)) ++ " <small>available</small></span>"
    ++ "<span class=\"tix\">" ++ Nat.show(count_mine(B.seat_map(Lg), viewer)) ++ " <small>tickets</small></span></div>"

# The viewer's holds
# ------------------

def hold_row(d: Due) -> String:
  match d:
    case Due{+k, +t1, secs}:
      "<li><b>" ++ label(k) ++ "</b> " ++ money(B.price(k)) ++ " <span class=\"secs\">" ++ Nat.show(secs) ++ "s</span>"
        ++ "<button class=\"pay\" data-on:click=\"@post('/pay/" ++ Nat.show(t1) ++ "')\">Pay</button>"
        ++ "<button class=\"rel\" data-on:click=\"@post('/release/" ++ Nat.show(t1) ++ "')\">Release</button></li>"

def hold_rows(ds: List<&2, Due>) -> String:
  match ds:
    case Nil{}:
      ""
    case d <> rest:
      hold_row(d) ++ hold_rows(rest)

def holds.body(b: Bool, ds: List<&2, Due>) -> String:
  match b:
    case True{}:
      "<p class=\"empty\">No holds. Pick a free seat.</p>"
    case False{}:
      "<ul>" ++ hold_rows(ds) ++ "</ul>"

def holds(+ds: List<&2, Due>) -> String:
  "<div id=\"holds\">" ++ holds.body(List.is_empty(&2, Due, ds), ds) ++ "</div>"
