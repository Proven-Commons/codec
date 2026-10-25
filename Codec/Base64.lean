/-
  Base 64 as RFC 4648 section 4 defines it: the standard alphabet, with
  padding.

  `decode` is strict. It accepts exactly the text `encode` produces: no
  missing or extra padding, no padding before the end, no characters
  outside the alphabet, no line breaks, and the unused bits before the
  padding must be zero.
-/

namespace Codec.Base64

/-- The 64 characters, in order. -/
def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

/-- The character for a value below 64. -/
def char (n : Nat) : Char :=
  alphabet.getD n 'A'

/-- Encode bytes, three at a time into four characters. -/
def encode : List UInt8 → List Char
  | a :: b :: c :: rest =>
    let n := a.toNat * 65536 + b.toNat * 256 + c.toNat
    char (n / 262144) :: char (n / 4096 % 64) :: char (n / 64 % 64) :: char (n % 64) ::
      encode rest
  | [a, b] =>
    let n := a.toNat * 65536 + b.toNat * 256
    [char (n / 262144), char (n / 4096 % 64), char (n / 64 % 64), '=']
  | [a] =>
    let n := a.toNat * 65536
    [char (n / 262144), char (n / 4096 % 64), '=', '=']
  | [] => []

/-- The value of one character of the alphabet. -/
def value (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 71)
  else if '0' ≤ c ∧ c ≤ '9' then some (c.toNat + 4)
  else if c = '+' then some 62
  else if c = '/' then some 63
  else none

/-- Decode, four characters at a time into three bytes. Padding may
    only end the text. -/
def decode : List Char → Option (List UInt8)
  | [] => some []
  | [c0, c1, '=', '='] =>
    match value c0, value c1 with
    | some v0, some v1 =>
      if v1 % 16 = 0 then some [(v0 * 4 + v1 / 16).toUInt8] else none
    | _, _ => none
  | [c0, c1, c2, '='] =>
    match value c0, value c1, value c2 with
    | some v0, some v1, some v2 =>
      if v2 % 4 = 0 then
        some [(v0 * 4 + v1 / 16).toUInt8, (v1 % 16 * 16 + v2 / 4).toUInt8]
      else none
    | _, _, _ => none
  | c0 :: c1 :: c2 :: c3 :: rest =>
    match value c0, value c1, value c2, value c3, decode rest with
    | some v0, some v1, some v2, some v3, some tail =>
      some ((v0 * 4 + v1 / 16).toUInt8 :: (v1 % 16 * 16 + v2 / 4).toUInt8 ::
        (v2 % 4 * 64 + v3).toUInt8 :: tail)
    | _, _, _, _, _ => none
  | _ => none

end Codec.Base64
