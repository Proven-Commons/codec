/-
  The definitions the specification uses, written from the standards,
  independently of the code in `Codec/`, with one exception: the PEM
  definitions take their base 64 from `Base64.encode`, which the base 64
  statements in `Spec.lean` pin down exactly. Part of the approved
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

/-! ## PEM

RFC 7468, the textual encoding of PKIX, PKCS, and CMS structures,
section 3, the strict form (Figure 3) and the rules it uses (Figure 1):

```
stricttextualmsg = preeb eol
                   strictbase64text
                   posteb eol

strictbase64finl = *15(4base64char) (4base64char / 3base64char
                     base64pad / 2base64char 2base64pad) eol
base64fullline   = 64base64char eol
strictbase64text = *base64fullline strictbase64finl

preeb      = "-----BEGIN " label "-----"
posteb     = "-----END " label "-----"
labelchar  = %x21-2C / %x2E-7E    ; any printable character,
                                  ; except hyphen-minus
label      = [ labelchar *( ["-" / SP] labelchar ) ]       ; empty ok
eol        = CRLF / CR / LF
```

Section 2: "Generators MUST put the same label on the "-----END " line
(post-encapsulation boundary) as the corresponding "-----BEGIN " line."
"Generators MUST wrap the base64-encoded lines so that each line consists
of exactly 64 characters except for the final line".

The base 64 is RFC 4648, section 4, as `Base64.encode` writes it; its
statements pin it down. Two points depart from the strict form. It has
no text for empty data, since `strictbase64finl` needs four characters:
here empty data has no line of base 64, so its text is the BEGIN and END
lines alone. With LF line ends only the lax form (Figure 2) allows that
text, and the standard form's text for empty data (Figure 1), with one
empty line, is refused. And the strict form allows a final group whose
unused bits are not zero, which strict base 64 refuses: here the base 64
is exactly `Base64.encode` of the data. -/

/-- `labelchar`: printable US-ASCII, `!` to `~`, except `-`. -/
def Spec.labelChar (c : Char) : Prop :=
  (0x21 ≤ c.toNat ∧ c.toNat ≤ 0x2C) ∨ (0x2E ≤ c.toNat ∧ c.toNat ≤ 0x7E)

/-- `*( ["-" / SP] labelchar )`: label characters, each of which may
    follow one `-` or space. -/
inductive Spec.LabelTail : List Char → Prop where
  | nil : Spec.LabelTail []
  | char {c : Char} {rest : List Char} :
      Spec.labelChar c → Spec.LabelTail rest → Spec.LabelTail (c :: rest)
  | sep {s c : Char} {rest : List Char} :
      (s = '-' ∨ s = ' ') → Spec.labelChar c → Spec.LabelTail rest →
      Spec.LabelTail (s :: c :: rest)

/-- `label = [ labelchar *( ["-" / SP] labelchar ) ]`. -/
def Spec.Label (l : List Char) : Prop :=
  l = [] ∨ ∃ c rest, l = c :: rest ∧ Spec.labelChar c ∧ Spec.LabelTail rest

/-- `eol = CRLF / CR / LF`. -/
def Spec.Eol (e : List Char) : Prop :=
  e = ['\r', '\n'] ∨ e = ['\r'] ∨ e = ['\n']

/-- The text `text` is the lines `ls`, each followed by an `eol`. No
    line holds a CR or an LF. -/
inductive Spec.LinesEol : List Char → List (List Char) → Prop where
  | nil : Spec.LinesEol [] []
  | cons {l e rest : List Char} {ls : List (List Char)} :
      '\r' ∉ l → '\n' ∉ l → Spec.Eol e → Spec.LinesEol rest ls →
      Spec.LinesEol (l ++ e ++ rest) (l :: ls)

/-- `*base64fullline strictbase64finl`, without the line ends: the base
    64 text cut into lines of 64 characters, the last one at most 64. -/
def Spec.lines64 (s : List Char) : List (List Char) :=
  (List.range ((s.length + 63) / 64)).map fun i => (s.drop (64 * i)).take 64

/-- The lines of the message for `label` and `data`, without their line
    ends: `preeb`, the base 64 of the data, `posteb`. The END line has
    the same label as the BEGIN line. -/
def Spec.pemLines (label : List Char) (data : List UInt8) : List (List Char) :=
  ["-----BEGIN ".toList ++ label ++ "-----".toList] ++ Spec.lines64 (Base64.encode data) ++
    ["-----END ".toList ++ label ++ "-----".toList]

/-- What a generator writes: each line, then LF. -/
def Spec.pemText (label : List Char) (data : List UInt8) : List Char :=
  ((Spec.pemLines label data).map (· ++ ['\n'])).flatten

/-- `text` is a message in the strict form, for this label and data:
    the label is a `label`, and the text is the message's lines, each
    followed by any `eol`. -/
def Spec.StrictPem (text label : List Char) (data : List UInt8) : Prop :=
  Spec.Label label ∧ Spec.LinesEol text (Spec.pemLines label data)

-- 48 bytes are one full line of 64 characters; 49 bytes need a second.
example : (Spec.lines64 (List.replicate 64 'A')).map List.length = [64] := by decide
example : (Spec.lines64 (List.replicate 68 'A')).map List.length = [64, 4] := by decide
example : Spec.lines64 [] = [] := by decide

/-- The data of RFC 7468, Figure 15 (a subject public key info), as the
    base 64 there spells it. -/
def Spec.figure15 : List UInt8 := [
    0x30, 0x76, 0x30, 0x10, 0x06, 0x07, 0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02,
    0x01, 0x06, 0x05, 0x2B, 0x81, 0x04, 0x00, 0x22, 0x03, 0x62, 0x00, 0x04,
    0x9F, 0x52, 0xE5, 0xC0, 0xB3, 0x7F, 0x28, 0x16, 0x10, 0x45, 0x51, 0xFA,
    0x1D, 0xF2, 0x0C, 0x4F, 0x37, 0xC4, 0xA8, 0x93, 0x95, 0xCE, 0xD2, 0xDE,
    0x90, 0xB7, 0x21, 0xA7, 0x68, 0x62, 0xEF, 0xC7, 0x02, 0x68, 0xC6, 0x3C,
    0xD4, 0x50, 0x65, 0x62, 0xCF, 0x09, 0xF6, 0x5E, 0xE4, 0xAD, 0xCF, 0x8C,
    0xE1, 0xA0, 0x5E, 0x08, 0x66, 0x05, 0x8D, 0xB6, 0xBE, 0x86, 0x25, 0xED,
    0xB4, 0x95, 0x8F, 0x2F, 0xBC, 0x9D, 0x94, 0x4F, 0xB9, 0x50, 0x6E, 0x14,
    0x36, 0x49, 0xF7, 0x12, 0x8B, 0x3C, 0x12, 0x26, 0x41, 0xCA, 0x2F, 0x43,
    0x56, 0xCC, 0x9F, 0xCB, 0xD7, 0x9E, 0x8E, 0x1F, 0xBC, 0x01, 0x78, 0x29]
