# kit.bend: the small order and truth vocabulary shared by the code and
# the proofs. LE(a, b) is the *type* of evidence that a <= b: Unit when it
# holds, Empty when it fails. le_case compares two numbers and hands back
# that evidence, so a program that branches on a comparison also hands its
# proofs the fact it branched on.

import Base

# a <= b, as a type
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b0:
      Unit
    case 1n+a1 0n:
      Empty
    case 1n+a1 1n+b1:
      LE(a1, b1)

# the verdict of a <= b, with its evidence either way (b < a is 1+b <= a)
def le_case(+a: Nat, +b: Nat) -> Or(LE(a, b), LE(1n+b, a)):
  match a b:
    case 0n b0:
      Inl{Unit{}}
    case 1n+a1 0n:
      Inr{Unit{}}
    case 1n+a1 1n+b1:
      le_case(a1, b1)

# T(b): the truth of a Bool, as a type
def T(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# b ? n : 0
def when(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      n
    case False{}:
      0n
