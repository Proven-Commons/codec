/-
  The definitions the specification uses, written from the standards,
  independently of the code in `Codec/`. Part of the approved
  specification, with `Spec.lean`.

  Both the challenge file and the proofs import this file, so each
  statement means the same thing on both sides. The `example`s pin each
  table character by character, by code point, and check the
  definitions against the examples of RFC 4648, section 9, and the
  CRC-32 check value. A mistake in either fails the build. The test
  vectors of RFC 4648, section 10, are theorems in `Spec.lean`.
-/

import Codec

open Codec

/-! ## Shared -/

/-- The bytes of an ASCII string, for test vectors. -/
def Spec.ascii (s : String) : List UInt8 :=
  s.toList.map fun c => c.toNat.toUInt8

/-- ASCII lowercase: `A` to `Z` become `a` to `z`; nothing else changes. -/
def Spec.asciiLower (c : Char) : Char :=
  if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

example : "AZaz09@[`{".toList.map Spec.asciiLower = "azaz09@[`{".toList := by decide

/-! ## Hex

Each byte becomes two digits from `0123456789abcdef`, the high half
first. Decoding reads digits in either case and accepts nothing else. -/

/-- The hex digits, lowercase, as Python's `bytes.hex()` writes them. -/
def Spec.hexDigits : List Char := "0123456789abcdef".toList

def Spec.hexDigit (n : Nat) : Char := Spec.hexDigits.getD n '?'

-- Digits 0 to 9, then a to f, by code point.
example : Spec.hexDigits.map Char.toNat =
    (List.range 10).map (· + 48) ++ (List.range 6).map (· + 97) := by decide

/-! ## Base 64

RFC 4648, section 4. -/

/-- RFC 4648, Table 1: the base 64 alphabet, values 0 to 63. -/
def Spec.base64Table : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

def Spec.base64Char (n : Nat) : Char := Spec.base64Table.getD n '?'

/-- RFC 4648, section 4: a 24-bit group, high bit first, read as four
    6-bit values, each written as its character in Table 1. -/
def Spec.base64Group (n : Nat) : List Char :=
  [Spec.base64Char (n / 2 ^ 18 % 64), Spec.base64Char (n / 2 ^ 12 % 64),
   Spec.base64Char (n / 2 ^ 6 % 64), Spec.base64Char (n % 64)]

-- RFC 4648, Table 1, by code point: A to Z, a to z, 0 to 9, then + and /.
example : Spec.base64Table.map Char.toNat =
    (List.range 26).map (· + 65) ++ (List.range 26).map (· + 97) ++
      (List.range 10).map (· + 48) ++ [43, 47] := by decide

-- RFC 4648, section 9: the bytes 14 fb 9c 03 d9 7e are "FPucA9l+",
-- 14 fb 9c 03 d9 are "FPucA9k=", and 14 fb 9c 03 are "FPucAw==".
example : Spec.base64Group 0x14fb9c ++ Spec.base64Group 0x03d97e = "FPucA9l+".toList := by
  decide
example : Spec.base64Group 0x14fb9c ++ (Spec.base64Group 0x03d900).take 3 ++ ['='] =
    "FPucA9k=".toList := by decide
example : Spec.base64Group 0x14fb9c ++ (Spec.base64Group 0x030000).take 2 ++ ['=', '='] =
    "FPucAw==".toList := by decide

/-! ## CRC-32

The CRC-32 of ISO 3309, ITU-T V.42, and RFC 1952 (gzip), defined one bit
at a time. -/

/-- One bit: if the low bit is one, shift right and xor in the reflected
    polynomial 0xEDB88320; otherwise just shift right. -/
def Spec.crcBit (c : UInt32) : UInt32 :=
  if c % 2 = 1 then c / 2 ^^^ 0xEDB88320 else c / 2

/-- One byte: xor it into the low end of the register, then eight bits. -/
def Spec.crcByte (c : UInt32) (b : UInt8) : UInt32 :=
  Nat.repeat Spec.crcBit 8 (c ^^^ b.toUInt32)

/-- The register starts as all ones, takes each byte in order, and is
    inverted at the end. -/
def Spec.crc32 (bs : List UInt8) : UInt32 :=
  bs.foldl Spec.crcByte 0xFFFFFFFF ^^^ 0xFFFFFFFF

-- The standard check value: the CRC-32 of "123456789" is 0xCBF43926.
example : Spec.crc32 (Spec.ascii "123456789") = 0xCBF43926 := by decide +kernel

/-- Four bytes, low byte first, as gzip stores its CRC. -/
def Spec.le32 (x : UInt32) : List UInt8 :=
  [(x.toNat % 2 ^ 8).toUInt8, (x.toNat / 2 ^ 8 % 2 ^ 8).toUInt8,
   (x.toNat / 2 ^ 16 % 2 ^ 8).toUInt8, (x.toNat / 2 ^ 24).toUInt8]

example : Spec.le32 0xCBF43926 = [0x26, 0x39, 0xF4, 0xCB] := by decide

/-! ## Percent-encoding

RFC 3986, section 2.1:

```
pct-encoded = "%" HEXDIG HEXDIG
```

"The uppercase hexadecimal digits 'A' through 'F' are equivalent to the
lowercase digits 'a' through 'f', respectively. ... For consistency, URI
producers and normalizers should use uppercase hexadecimal digits for
all percent-encodings."

Section 2.3:

```
unreserved  = ALPHA / DIGIT / "-" / "." / "_" / "~"
```

"For consistency, percent-encoded octets in the ranges of ALPHA (%41-%5A
and %61-%7A), DIGIT (%30-%39), hyphen (%2D), period (%2E), underscore
(%5F), or tilde (%7E) should not be created by URI producers".

Section 2.4: "Implementations must not percent-encode or decode the same
string more than once". -/

/-- The unreserved characters of section 2.3. -/
def Spec.unreservedChars : List Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~".toList

-- `A` to `Z`, `a` to `z`, `0` to `9`, then `-`, `.`, `_` and `~`, by code point.
example : Spec.unreservedChars.map Char.toNat =
    (List.range 26).map (· + 65) ++ (List.range 26).map (· + 97) ++
      (List.range 10).map (· + 48) ++ [45, 46, 95, 126] := by decide

/-- The hex digits, uppercase, as section 2.1 recommends producers write
    them. -/
def Spec.upperHexDigits : List Char := "0123456789ABCDEF".toList

-- Digits 0 to 9, then A to F, by code point.
example : Spec.upperHexDigits.map Char.toNat =
    (List.range 10).map (· + 48) ++ (List.range 6).map (· + 65) := by decide

/-- How a producer writes one byte: an unreserved character as itself,
    and any other byte as `%` and two uppercase digits, the high half
    first. -/
def Spec.pctByte (b : UInt8) : List Char :=
  if Char.ofNat b.toNat ∈ Spec.unreservedChars then [Char.ofNat b.toNat]
  else ['%', Spec.upperHexDigits.getD (b.toNat / 16) '?',
    Spec.upperHexDigits.getD (b.toNat % 16) '?']

/-- The percent-encoding of a byte string, byte by byte. -/
def Spec.pctEncode (bs : List UInt8) : List Char :=
  (bs.map Spec.pctByte).flatten

-- The examples of sections 2.1 and 2.5: the space, "A", LATIN CAPITAL
-- LETTER A WITH GRAVE (C3 80 in UTF-8) and KATAKANA LETTER A (E3 82 A2).
example : Spec.pctEncode [0x20] = "%20".toList := by decide
example : Spec.pctEncode (Spec.ascii "A") = "A".toList := by decide
example : Spec.pctEncode [0xC3, 0x80] = "%C3%80".toList := by decide
example : Spec.pctEncode [0xE3, 0x82, 0xA2] = "%E3%82%A2".toList := by decide

/-- How percent-encoded text reads: `Spec.PctReads cs bs` says the text
    `cs` reads as the bytes `bs`. A `%` and two hex digits, in either
    case, read as the byte they spell, the high half first. Any other
    US-ASCII character but `%` reads as its own code. Nothing else
    reads: not a `%` without two hex digits after it, and not a
    character outside US-ASCII. What a `%` and its digits spell is never
    read again. -/
inductive Spec.PctReads : List Char → List UInt8 → Prop where
  | nil : Spec.PctReads [] []
  | escape {hi lo : Char} {b : UInt8} {rest : List Char} {bs : List UInt8} :
      Spec.asciiLower hi = Spec.hexDigit (b.toNat / 16) →
      Spec.asciiLower lo = Spec.hexDigit (b.toNat % 16) →
      Spec.PctReads rest bs → Spec.PctReads ('%' :: hi :: lo :: rest) (b :: bs)
  | char {c : Char} {rest : List Char} {bs : List UInt8} :
      c ≠ '%' → c.toNat < 0x80 →
      Spec.PctReads rest bs → Spec.PctReads (c :: rest) (c.toNat.toUInt8 :: bs)
