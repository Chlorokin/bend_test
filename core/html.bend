# html.bend: turning visitor text into HTML text. `text` is the only way
# the views put a visitor-chosen string on the page; LAWS.bend proves that
# its output never contains a character that could open a tag or close an
# attribute (< > " '), whatever the input.

import Base

# Classifying characters
# ----------------------

type CharKind is Data:
  Lt{}
  Gt{}
  Amp{}
  Quot{}
  Apos{}
  Plain{}

def kind.code(+x: U32) -> CharKind:
  Bool.pick(CharKind, U32.is_eq(x, 60), Lt{},
    Bool.pick(CharKind, U32.is_eq(x, 62), Gt{},
      Bool.pick(CharKind, U32.is_eq(x, 38), Amp{},
        Bool.pick(CharKind, U32.is_eq(x, 34), Quot{},
          Bool.pick(CharKind, U32.is_eq(x, 39), Apos{}, Plain{})))))

def kind(c: Char) -> CharKind:
  match c:
    case Chr{+x}:
      kind.code(x)

def danger_k(k: CharKind) -> Bool:
  match k:
    case Lt{}:
      True{}
    case Gt{}:
      True{}
    case Quot{}:
      True{}
    case Apos{}:
      True{}
    case Amp{}:
      False{}
    case Plain{}:
      False{}

# < > " ' : the characters that end text or an attribute value
def danger(c: Char) -> Bool:
  danger_k(kind(c))

# no dangerous character anywhere in s
def clean(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.not(danger(c)) && clean(t)

# Escaping
# --------

def esc(c: Char, k: CharKind, rest: String) -> String:
  match k:
    case Lt{}:
      "&lt;" ++ rest
    case Gt{}:
      "&gt;" ++ rest
    case Amp{}:
      "&amp;" ++ rest
    case Quot{}:
      "&quot;" ++ rest
    case Apos{}:
      "&#39;" ++ rest
    case Plain{}:
      SCon{c, rest}

# visitor text, made safe for HTML text and attribute values
def text(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      esc(c, kind(c), text(t))

def tags.k(k: CharKind) -> Nat:
  match k:
    case Lt{}:
      1n
    case _:
      0n

# how many tags a string opens (its '<' characters)
def tags(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      Nat.add(tags.k(kind(c)), tags(t))

