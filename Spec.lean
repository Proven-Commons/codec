/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry` below is expected in this file
  only.

  The definitions the statements use, written from the standards, are in
  `Spec/Defs.lean`, which is part of the specification too.
-/

import Codec
import Spec.Defs

open Codec

/-! ## Hex

Each byte becomes two digits from `0123456789abcdef`, the high half
first, as Python's `bytes.hex()` writes it: RFC 4648 base 16 in
lowercase. Decoding reads digits in either case and accepts nothing
else. -/

theorem Spec.hex_encode_nil : Hex.encode [] = [] := sorry

/-- Each byte is two digits, high half first. -/
theorem Spec.hex_encode_cons (b : UInt8) (bs : List UInt8) :
    Hex.encode (b :: bs) =
      Spec.hexDigit (b.toNat / 16) :: Spec.hexDigit (b.toNat % 16) :: Hex.encode bs := sorry

/-- Decoding gives back what was encoded. -/
theorem Spec.hex_decode_encode (bs : List UInt8) :
    Hex.decode (Hex.encode bs) = some bs := sorry

/-- Decoding accepts any mix of upper and lower case. -/
theorem Spec.hex_decode_any_case (cs : List Char) (bs : List UInt8) :
    cs.map Spec.asciiLower = Hex.encode bs → Hex.decode cs = some bs := sorry

/-- Decoding accepts nothing else: whatever it accepts is an encoding,
    up to case. -/
theorem Spec.hex_encode_decode (cs : List Char) (bs : List UInt8) :
    Hex.decode cs = some bs → Hex.encode bs = cs.map Spec.asciiLower := sorry

/-- The test vectors of RFC 4648, section 10. The RFC writes them in
    uppercase: encoding gives them in lowercase, and decoding reads them
    as the RFC writes them. -/
theorem Spec.hex_rfc4648_vectors :
    Hex.encode (Spec.ascii "") = "".toList ∧
    Hex.encode (Spec.ascii "f") = "66".toList ∧
    Hex.encode (Spec.ascii "fo") = "666f".toList ∧
    Hex.encode (Spec.ascii "foo") = "666f6f".toList ∧
    Hex.encode (Spec.ascii "foob") = "666f6f62".toList ∧
    Hex.encode (Spec.ascii "fooba") = "666f6f6261".toList ∧
    Hex.encode (Spec.ascii "foobar") = "666f6f626172".toList ∧
    Hex.decode "".toList = some (Spec.ascii "") ∧
    Hex.decode "66".toList = some (Spec.ascii "f") ∧
    Hex.decode "666F".toList = some (Spec.ascii "fo") ∧
    Hex.decode "666F6F".toList = some (Spec.ascii "foo") ∧
    Hex.decode "666F6F62".toList = some (Spec.ascii "foob") ∧
    Hex.decode "666F6F6261".toList = some (Spec.ascii "fooba") ∧
    Hex.decode "666F6F626172".toList = some (Spec.ascii "foobar") := sorry

/-! ## Base 64

RFC 4648, section 4. -/

theorem Spec.base64_encode_nil : Base64.encode [] = [] := sorry

/-- Three bytes, the first in the high bits, form one group. -/
theorem Spec.base64_encode_three (a b c : UInt8) (rest : List UInt8) :
    Base64.encode (a :: b :: c :: rest) =
      Spec.base64Group (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8 + c.toNat) ++
        Base64.encode rest := sorry

/-- Two final bytes: zero bits fill the group, which is cut to three
    characters and padded with one `=`. -/
theorem Spec.base64_encode_two (a b : UInt8) :
    Base64.encode [a, b] =
      (Spec.base64Group (a.toNat * 2 ^ 16 + b.toNat * 2 ^ 8)).take 3 ++ ['='] := sorry

/-- One final byte: the group is cut to two characters and padded with
    `==`. -/
theorem Spec.base64_encode_one (a : UInt8) :
    Base64.encode [a] = (Spec.base64Group (a.toNat * 2 ^ 16)).take 2 ++ ['=', '='] := sorry

/-- Decoding gives back what was encoded. -/
theorem Spec.base64_decode_encode (bs : List UInt8) :
    Base64.decode (Base64.encode bs) = some bs := sorry

/-- Decoding is strict: whatever it accepts is exactly an encoding. -/
theorem Spec.base64_encode_decode (cs : List Char) (bs : List UInt8) :
    Base64.decode cs = some bs → Base64.encode bs = cs := sorry

/-- The test vectors of RFC 4648, section 10. -/
theorem Spec.base64_rfc4648_vectors :
    Base64.encode (Spec.ascii "") = "".toList ∧
    Base64.encode (Spec.ascii "f") = "Zg==".toList ∧
    Base64.encode (Spec.ascii "fo") = "Zm8=".toList ∧
    Base64.encode (Spec.ascii "foo") = "Zm9v".toList ∧
    Base64.encode (Spec.ascii "foob") = "Zm9vYg==".toList ∧
    Base64.encode (Spec.ascii "fooba") = "Zm9vYmE=".toList ∧
    Base64.encode (Spec.ascii "foobar") = "Zm9vYmFy".toList := sorry

/-! ## CRC-32

The CRC-32 of ISO 3309, ITU-T V.42, and RFC 1952 (gzip), defined one bit
at a time. -/

/-- The table-driven code computes `Spec.crc32`, the CRC-32 defined one
    bit at a time in `Spec/Defs.lean`. -/
theorem Spec.crc32_eq (bs : List UInt8) : Crc32.crc32 bs = Spec.crc32 bs := sorry

/-- The code gives the standard check value. -/
theorem Spec.crc32_check : Crc32.crc32 (Spec.ascii "123456789") = 0xCBF43926 := sorry

/-- A frame is the message followed by its CRC-32, low byte first. -/
theorem Spec.frame_layout (bs : List UInt8) :
    Crc32.frame bs = bs ++ Spec.le32 (Spec.crc32 bs) := sorry

/-- Unframing a frame gives back the message. -/
theorem Spec.unframe_frame (bs : List UInt8) :
    Crc32.unframe (Crc32.frame bs) = some bs := sorry

/-- Unframing accepts nothing else: whatever it accepts is a frame. -/
theorem Spec.frame_unframe (fr bs : List UInt8) :
    Crc32.unframe fr = some bs → Crc32.frame bs = fr := sorry
