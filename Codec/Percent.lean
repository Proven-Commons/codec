/-
  Percent-encoding, RFC 3986, section 2.1: a byte as `%` and two hex
  digits.

  `encode` keeps the unreserved characters of section 2.3 as they are
  and writes every other byte as `%` and two uppercase digits, as
  section 2.1 recommends. `decode` reads `%` and two digits, in either
  case, as one byte, and any other ASCII character but `%` as its own
  code. It fails on a `%` that two digits do not follow, and on any
  character outside ASCII. It decodes once: what it gives back is never
  read again.
-/

import Codec.Hex

namespace Codec.Percent

/-- The digit for a value below 16, uppercase. -/
def upper (n : Nat) : Char :=
  "0123456789ABCDEF".toList.getD n '0'

/-- Section 2.3: `A` to `Z`, `a` to `z`, `0` to `9`, `-`, `.`, `_` and
    `~`. -/
def unreserved (b : UInt8) : Bool :=
  let n := b.toNat
  (0x41 ≤ n && n ≤ 0x5A) || (0x61 ≤ n && n ≤ 0x7A) || (0x30 ≤ n && n ≤ 0x39) ||
    n == 0x2D || n == 0x2E || n == 0x5F || n == 0x7E

/-- Encode bytes: unreserved ones as their characters, the rest as `%`
    and two uppercase digits. -/
def encode : List UInt8 → List Char
  | [] => []
  | b :: bs =>
    if unreserved b then Char.ofNat b.toNat :: encode bs
    else '%' :: upper (b.toNat / 16) :: upper (b.toNat % 16) :: encode bs

/-- Decode percent-encoded text. Fails on a `%` without two hex digits
    after it, and on a character outside ASCII. -/
def decode : List Char → Option (List UInt8)
  | [] => some []
  | '%' :: hi :: lo :: rest =>
    match Hex.value hi, Hex.value lo, decode rest with
    | some h, some l, some tail => some ((h * 16 + l).toUInt8 :: tail)
    | _, _, _ => none
  | '%' :: _ => none
  | c :: rest =>
    if c.toNat < 0x80 then (decode rest).map (c.toNat.toUInt8 :: ·) else none

end Codec.Percent
