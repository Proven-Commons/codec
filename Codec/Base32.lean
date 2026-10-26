/-
  Base 32 as RFC 4648 section 6 defines it: the standard alphabet,
  with padding.

  `decode` is strict. It accepts exactly the text `encode` produces: no
  missing or extra padding, no padding before the end, no characters
  outside the alphabet, no line breaks, and the unused bits before the
  padding must be zero.
-/

namespace Codec.Base32

/-- The 32 characters, in order. -/
def alphabet : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567".toList

/-- The character for a value below 32. -/
def char (n : Nat) : Char :=
  alphabet.getD n 'A'

/-- Encode bytes, five at a time into eight characters. -/
def encode : List UInt8 → List Char
  | a :: b :: c :: d :: e :: rest =>
    let n := a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 +
      d.toNat * 256 + e.toNat
    char (n / 34359738368) :: char (n / 1073741824 % 32) ::
      char (n / 33554432 % 32) :: char (n / 1048576 % 32) ::
      char (n / 32768 % 32) :: char (n / 1024 % 32) ::
      char (n / 32 % 32) :: char (n % 32) :: encode rest
  | [a, b, c, d] =>
    let n := a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536 +
      d.toNat * 256
    [char (n / 34359738368), char (n / 1073741824 % 32),
     char (n / 33554432 % 32), char (n / 1048576 % 32),
     char (n / 32768 % 32), char (n / 1024 % 32),
     char (n / 32 % 32), '=']
  | [a, b, c] =>
    let n := a.toNat * 4294967296 + b.toNat * 16777216 + c.toNat * 65536
    [char (n / 34359738368), char (n / 1073741824 % 32),
     char (n / 33554432 % 32), char (n / 1048576 % 32),
     char (n / 32768 % 32), '=', '=', '=']
  | [a, b] =>
    let n := a.toNat * 4294967296 + b.toNat * 16777216
    [char (n / 34359738368), char (n / 1073741824 % 32),
     char (n / 33554432 % 32), char (n / 1048576 % 32),
     '=', '=', '=', '=']
  | [a] =>
    let n := a.toNat * 4294967296
    [char (n / 34359738368), char (n / 1073741824 % 32),
     '=', '=', '=', '=', '=', '=']
  | [] => []

/-- The value of one character of the alphabet. -/
def value (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 65)
  else if '2' ≤ c ∧ c ≤ '7' then some (c.toNat - 24)
  else none

/-- Decode, eight characters at a time into five bytes. Padding may
    only end the text. -/
def decode : List Char → Option (List UInt8)
  | [] => some []
  | [c0, c1, '=', '=', '=', '=', '=', '='] =>
    match value c0, value c1 with
    | some v0, some v1 =>
      if v1 % 4 = 0 then some [(v0 * 8 + v1 / 4).toUInt8] else none
    | _, _ => none
  | [c0, c1, c2, c3, '=', '=', '=', '='] =>
    match value c0, value c1, value c2, value c3 with
    | some v0, some v1, some v2, some v3 =>
      if v3 % 16 = 0 then
        some [(v0 * 8 + v1 / 4).toUInt8,
          (v1 % 4 * 64 + v2 * 2 + v3 / 16).toUInt8]
      else none
    | _, _, _, _ => none
  | [c0, c1, c2, c3, c4, '=', '=', '='] =>
    match value c0, value c1, value c2, value c3, value c4 with
    | some v0, some v1, some v2, some v3, some v4 =>
      if v4 % 2 = 0 then
        some [(v0 * 8 + v1 / 4).toUInt8,
          (v1 % 4 * 64 + v2 * 2 + v3 / 16).toUInt8,
          (v3 % 16 * 16 + v4 / 2).toUInt8]
      else none
    | _, _, _, _, _ => none
  | [c0, c1, c2, c3, c4, c5, c6, '='] =>
    match value c0, value c1, value c2, value c3, value c4, value c5,
        value c6 with
    | some v0, some v1, some v2, some v3, some v4, some v5, some v6 =>
      if v6 % 8 = 0 then
        some [(v0 * 8 + v1 / 4).toUInt8,
          (v1 % 4 * 64 + v2 * 2 + v3 / 16).toUInt8,
          (v3 % 16 * 16 + v4 / 2).toUInt8,
          (v4 % 2 * 128 + v5 * 4 + v6 / 8).toUInt8]
      else none
    | _, _, _, _, _, _, _ => none
  | c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: rest =>
    match value c0, value c1, value c2, value c3, value c4, value c5,
        value c6, value c7, decode rest with
    | some v0, some v1, some v2, some v3, some v4, some v5, some v6,
        some v7, some tail =>
      some ((v0 * 8 + v1 / 4).toUInt8 ::
        (v1 % 4 * 64 + v2 * 2 + v3 / 16).toUInt8 ::
        (v3 % 16 * 16 + v4 / 2).toUInt8 ::
        (v4 % 2 * 128 + v5 * 4 + v6 / 8).toUInt8 ::
        (v6 % 8 * 32 + v7).toUInt8 :: tail)
    | _, _, _, _, _, _, _, _, _ => none
  | _ => none

end Codec.Base32
