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
