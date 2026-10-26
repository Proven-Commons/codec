/-
  Hexadecimal: each byte as two digits, the high half first.

  `encode` writes lowercase digits, as Python's `bytes.hex()` does.
  `decode` reads digits in either case and fails on anything else.
-/

namespace Codec.Hex

/-- The sixteen digits, lowercase. -/
def digits : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- The digit for a value below 16. -/
def digit (n : Nat) : Char :=
  digits.getD n '0'

/-- Encode bytes as hex digits. -/
def encode : List UInt8 → List Char
  | [] => []
  | b :: bs => digit (b.toNat / 16) :: digit (b.toNat % 16) :: encode bs

/-- The value of one hex digit, in either case. -/
def value (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Decode hex digits. Fails on an odd number of digits or on any other
    character. -/
def decode : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest =>
    match value hi, value lo, decode rest with
    | some h, some l, some tail => some ((h * 16 + l).toUInt8 :: tail)
    | _, _, _ => none

end Codec.Hex
