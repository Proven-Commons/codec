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

/-- The test vectors of RFC 4648, section 10: encoding gives them, and
    decoding reads them back. -/
theorem Spec.base64_rfc4648_vectors :
    Base64.encode (Spec.ascii "") = "".toList ∧
    Base64.encode (Spec.ascii "f") = "Zg==".toList ∧
    Base64.encode (Spec.ascii "fo") = "Zm8=".toList ∧
    Base64.encode (Spec.ascii "foo") = "Zm9v".toList ∧
    Base64.encode (Spec.ascii "foob") = "Zm9vYg==".toList ∧
    Base64.encode (Spec.ascii "fooba") = "Zm9vYmE=".toList ∧
    Base64.encode (Spec.ascii "foobar") = "Zm9vYmFy".toList ∧
    Base64.decode "".toList = some (Spec.ascii "") ∧
    Base64.decode "Zg==".toList = some (Spec.ascii "f") ∧
    Base64.decode "Zm8=".toList = some (Spec.ascii "fo") ∧
    Base64.decode "Zm9v".toList = some (Spec.ascii "foo") ∧
    Base64.decode "Zm9vYg==".toList = some (Spec.ascii "foob") ∧
    Base64.decode "Zm9vYmE=".toList = some (Spec.ascii "fooba") ∧
    Base64.decode "Zm9vYmFy".toList = some (Spec.ascii "foobar") := sorry

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

/-! ## Percent-encoding

RFC 3986, section 2.1: a byte as `%` and two hex digits. The encoder
keeps the unreserved characters of section 2.3 and writes every other
byte as `%` and two uppercase digits. The decoder reads digits in either
case, and decodes once. -/

/-- The encoder writes each byte as sections 2.1 and 2.3 tell producers
    to: an unreserved character as itself, any other byte as `%` and
    two uppercase digits. -/
theorem Spec.percent_encode_eq (bs : List UInt8) :
    Percent.encode bs = Spec.pctEncode bs := sorry

/-- The decoder reads exactly the text that `Spec.PctReads` allows, and
    reads it as `Spec.PctReads` says. So it refuses a `%` without two
    hex digits after it, and any character outside US-ASCII. -/
theorem Spec.percent_decode_iff (cs : List Char) (bs : List UInt8) :
    Percent.decode cs = some bs ↔ Spec.PctReads cs bs := sorry

/-- Decoding what the encoder wrote gives the bytes back. -/
theorem Spec.percent_decode_encode (bs : List UInt8) :
    Percent.decode (Percent.encode bs) = some bs := sorry

/-- The examples of RFC 3986, sections 2.1, 2.3, 2.5 and 6.2.2 (with
    6.2.2.1's `%3a` and `%3A`); every reserved character of section
    2.2 and the unreserved punctuation of section 2.3; decoding once
    (`%252E` is the text `%2E`, not a dot); and text the decoder
    refuses. -/
theorem Spec.percent_vectors :
    Percent.encode [0x20] = "%20".toList ∧
    Percent.encode (Spec.ascii "A") = "A".toList ∧
    Percent.encode [0xC3, 0x80] = "%C3%80".toList ∧
    Percent.encode [0xE3, 0x82, 0xA2] = "%E3%82%A2".toList ∧
    Percent.encode (Spec.ascii "-._~") = "-._~".toList ∧
    Percent.encode (Spec.ascii "Laguna Beach") = "Laguna%20Beach".toList ∧
    Percent.encode (Spec.ascii "%:/?#[]@!$&'()*+,;=") =
      "%25%3A%2F%3F%23%5B%5D%40%21%24%26%27%28%29%2A%2B%2C%3B%3D".toList ∧
    Percent.decode "%C3%80".toList = some [0xC3, 0x80] ∧
    Percent.decode "%e3%82%a2".toList = some [0xE3, 0x82, 0xA2] ∧
    Percent.decode "%7E".toList = some (Spec.ascii "~") ∧
    Percent.decode "%63/%7bfoo%7d".toList = some (Spec.ascii "c/{foo}") ∧
    Percent.decode "%3a".toList = some (Spec.ascii ":") ∧
    Percent.decode "%3A".toList = some (Spec.ascii ":") ∧
    Percent.decode "a+b c".toList = some (Spec.ascii "a+b c") ∧
    Percent.decode "%252E".toList = some (Spec.ascii "%2E") ∧
    Percent.decode "%".toList = none ∧
    Percent.decode "%2".toList = none ∧
    Percent.decode "%zz".toList = none ∧
    Percent.decode "%%41".toList = none ∧
    Percent.decode "café".toList = none := sorry

/-! ## PEM

RFC 7468, the strict form of the textual encoding (Figure 3): a BEGIN
line with a label, the base 64 of the data in lines of 64 characters,
and an END line with the same label. -/

/-- The encoder writes the strict form, each line ending in LF, and for
    empty data the BEGIN and END lines alone; it fails on a label the
    `label` rule does not allow. -/
theorem Spec.pem_encode_iff (label : List Char) (data : List UInt8) (text : List Char) :
    Pem.encode label data = some text ↔ Spec.Label label ∧ text = Spec.pemText label data :=
  sorry

/-- The decoder reads exactly the messages in the strict form, and for
    empty data the BEGIN and END lines alone, with any `eol` at the end
    of each line, and gives their label and data. So
    it refuses a different label on the END line, blanks, headers, text
    before or after the message, lines of another length, and base 64
    that is not exactly the encoding of the data. -/
theorem Spec.pem_decode_iff (text label : List Char) (data : List UInt8) :
    Pem.decode text = some (label, data) ↔ Spec.StrictPem text label data := sorry

/-- Decoding what the encoder wrote gives the label and the data back. -/
theorem Spec.pem_decode_encode (label : List Char) (data : List UInt8) (text : List Char) :
    Pem.encode label data = some text → Pem.decode text = some (label, data) := sorry

/-- RFC 7468, Figure 15, written exactly as the RFC prints it and read
    back with CR LF line ends; empty data and an empty label; labels the
    `label` rule refuses; and texts the decoder refuses. -/
theorem Spec.pem_vectors :
    Pem.encode "PUBLIC KEY".toList Spec.figure15 = some
      ("-----BEGIN PUBLIC KEY-----\nMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAEn1LlwLN/KBYQRVH6HfIMTzfEqJOVztLe\n".toList ++
       "kLchp2hi78cCaMY81FBlYs8J9l7krc+M4aBeCGYFjba+hiXttJWPL7ydlE+5UG4U\nNkn3Eos8EiZByi9DVsyfy9eejh+8AXgp\n-----END PUBLIC KEY-----\n".toList) ∧
    Pem.decode ("-----BEGIN PUBLIC KEY-----\r\nMHYwEAYHKoZIzj0CAQYFK4EEACIDYgAEn1LlwLN/KBYQRVH6HfIMTzfEqJOVztLe\r\n".toList ++
       "kLchp2hi78cCaMY81FBlYs8J9l7krc+M4aBeCGYFjba+hiXttJWPL7ydlE+5UG4U\r\nNkn3Eos8EiZByi9DVsyfy9eejh+8AXgp\r\n-----END PUBLIC KEY-----\r\n".toList) =
      some ("PUBLIC KEY".toList, Spec.figure15) ∧
    Pem.encode "X".toList [] = some "-----BEGIN X-----\n-----END X-----\n".toList ∧
    Pem.decode "-----BEGIN X-----\n-----END X-----\n".toList = some ("X".toList, []) ∧
    Pem.decode "-----BEGIN -----\rAA==\r-----END -----\r".toList = some ([], [0]) ∧
    Pem.encode "RSA PRIVATE KEY".toList [0] =
      some "-----BEGIN RSA PRIVATE KEY-----\nAA==\n-----END RSA PRIVATE KEY-----\n".toList ∧
    Pem.encode "A,B".toList [] = some "-----BEGIN A,B-----\n-----END A,B-----\n".toList ∧
    Pem.encode "A--B".toList [] = none ∧
    Pem.encode "A  B".toList [] = none ∧
    Pem.encode " A".toList [] = none ∧
    Pem.encode "A-".toList [] = none ∧
    Pem.encode "\u00c9".toList [] = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END Y-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END X-----".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA== \n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X----- \nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\n\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nProc-Type: 4,ENCRYPTED\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "text\n-----BEGIN X-----\nAA==\n-----END X-----\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAA==\n-----END X-----\n\n".toList = none ∧
    Pem.decode "-----BEGIN X-----\nAB==\n-----END X-----\n".toList = none ∧
    Pem.decode ("-----BEGIN X-----\nAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\nAAAAAAAA\n".toList ++
      "-----END X-----\n".toList) = none := sorry
