# Specification: codec

Five small codecs: hex, base 64, CRC-32 with a frame around a message, percent-encoding, and PEM; and two check digits, Luhn and IBAN. A reviewer who did not write this specification approves it, together with `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

Bytes are `List UInt8` and text is `List Char`. The command-line tool converts at the edges.

## Hex

Scope: each byte as two hex digits, the high half first, as Python's `bytes.hex()` writes it. This is RFC 4648 base 16 (section 8) up to case: the RFC's alphabet is uppercase.

- Encoding writes lowercase digits from `0123456789abcdef`. Every byte list has exactly one encoding.
- Decoding reads digits in either case. It fails on an odd number of digits and on any character that is not a hex digit. Spaces, line breaks, and `0x` prefixes are errors.

## Base 64

Scope: RFC 4648, section 4. The standard alphabet (Table 1), with padding. The URL-safe alphabet (section 5), line breaks (MIME), and unpadded forms are out of scope.

- Encoding takes three bytes at a time as a 24-bit group, the first byte in the high bits, and writes it as four 6-bit values, each as its character in Table 1. When one or two bytes remain, zero bits fill the group, which is cut to two or three characters and padded with `==` or `=`.
- Decoding is strict: it accepts exactly the text encoding produces, and fails on everything else. That includes padding that is missing, extra, or not at the end; characters outside the alphabet; and a last character whose unused bits are not zero. Python's `binascii.a2b_base64(strict_mode=True)` decodes that last case, and in Python 3.11 and in 3.12 before 3.12.4 it also decodes padding after a whole group, such as `Zm9v=` (CPython issue gh-118314). The tests count both separately.

## CRC-32

Scope: the CRC-32 of ISO 3309, ITU-T V.42, and RFC 1952 (gzip, zip, PNG). The register starts as all ones. Each byte is xored into its low end, followed by eight steps of shifting right, xoring in the reflected polynomial `0xEDB88320` whenever a one bit falls out. The result is inverted. The check value for the ASCII bytes of `123456789` is `0xCBF43926`.

- `crc32` computes it with a 256-entry table, a byte at a time.
- `frame` appends the CRC-32 of a message to it, low byte first, as gzip stores it.
- `unframe` returns the message when the last four bytes of its input are the message's CRC-32, and fails otherwise.

## Percent-encoding

Scope: RFC 3986, section 2.1: a byte written as `%` and two hex digits.

- Encoding keeps the unreserved characters of section 2.3 (`A` to `Z`, `a` to `z`, `0` to `9`, `-`, `.`, `_` and `~`) as they are, and writes every other byte as `%` and two uppercase hex digits, the high half first. The RFC asks producers for both: uppercase digits (section 2.1), and no percent-encoding of unreserved characters (section 2.3). So the encoder's output is already in the normal form of sections 6.2.2.1 (uppercase digits) and 6.2.2.2 (unreserved characters not encoded).
- Decoding reads `%` and two hex digits, in either case, as the byte they spell, and any other US-ASCII character but `%` as its own code. It does not check which characters a URI allows: a space, a control character or `{` reads as itself. It fails on a `%` without two hex digits after it, and on any character outside US-ASCII. It decodes once (section 2.4): `%252E` decodes to the text `%2E`, not to a dot.

Decoders differ on bad escapes. Go's `url.PathUnescape` returns an error, as this one does. Python's `urllib.parse.unquote` passes them through as text.

## PEM

Scope: RFC 7468, the textual encoding of PKIX, PKCS, and CMS structures, in its strict form (section 3, Figure 3). One message: a BEGIN line with a label, the base 64 of the data (RFC 4648, section 4, as the base 64 codec above writes it), and an END line with the same label.

- Encoding writes `-----BEGIN label-----`, the base 64 in lines of 64 characters with the last line at most 64, and `-----END label-----`, each line ending in LF. It fails on a label that the `label` rule does not allow: `label = [ labelchar *( ["-" / SP] labelchar ) ]`, where a `labelchar` is printable US-ASCII except `-`. So a label is empty, or has no `-` or space at either end and never two in a row.
- Decoding reads exactly one message in that form. Each line may end in LF, CR, or CR LF, as the `eol` rule allows; CR LF is one line end. It fails on everything else, including:
  - a different label on the END line, which the RFC lets parsers ignore but this one does not;
  - blanks, empty lines, headers, and text before or after the message;
  - a base 64 line of another length;
  - base 64 that is not exactly the encoding of the data, such as a last group whose unused bits are not zero.

The strict form has no text for empty data, since its last line of base 64 needs four characters. Here empty data is the BEGIN and END lines with nothing between, as Go's `encoding/pem` and Python's `ssl.DER_cert_to_PEM_cert` write it. With LF line ends, only the lax form (Figure 2) allows that text; the text the standard form (Figure 1) gives empty data, with one empty line between BEGIN and END, is refused.

## Luhn

Scope: the check digit of ISO/IEC 7812-1, Annex B, from H. P. Luhn's US patent 2,950,048. Numbers are lists of digits 0 to 9, most significant first.

- `valid` holds when every digit is 0 to 9 and the Luhn sum is a multiple of 10. The sum counts from the right, starting with the check digit: every second digit is doubled, and 9 is taken off a doubled digit above 9. The empty number passes, since its sum is 0.
- `checkDigit` gives the digit to put after a payload so that the whole is valid; it is the only such digit.
- What the check catches is a theorem: any one digit typed wrong, and any two adjacent different digits typed in the wrong order, except 0 and 9. That exception is a theorem too.

## IBAN

Scope: the check digits of ISO 13616-1, by ISO 7064 MOD 97-10, on the electronic form: a country code of two upper-case letters, two check digits, and a BBAN of 1 to 30 upper-case letters and digits.

- `valid` holds when the text has that shape and, with its first four characters moved to the end and each letter written as A = 10 to Z = 35, the digits read as one number leave 1 when divided by 97.
- `checkDigits` gives, for a country code and a BBAN of the right shape, the two digits from 02 to 98 that make the IBAN pass: 98 less the remainder of the BBAN, the country code and `00`. There is never more than one, and it fails on the wrong shape.
- What the check catches is a theorem: one digit typed for another or one letter for another, and two adjacent digits or two adjacent letters typed in the wrong order. Where the rearrangement splits an adjacent pair, the 4th and 5th characters, the swap is still caught, since 10 has order 96 mod 97. A letter and a digit swapped need not be caught: B is 11, so `4B1` and `41B` both read as `4111`, and a proved vector gives two IBANs that pass and differ only so.
- Not checked: each country's BBAN format and length, in the SWIFT IBAN Registry, and whether the country code is one. Check digits 00, 01 and 99 never come from the computation, but an IBAN with them can pass the check.

## Valid inputs and errors

Every encoder input, except a PEM label that the `label` rule refuses, and every `crc32` and `frame` input is valid. The decoders and `unframe` return `none` for anything they do not accept, PEM encoding returns `none` for such a label, and `Iban.checkDigits` returns `none` for a country code or BBAN of the wrong shape. No function can fail any other way.

The command-line tool in `Main.lean` reads one request per line and prints one answer per line. A request is an operation, then optionally one space and its comma-separated numbers; with no numbers after the space, the input is empty. `pemenc` is the exception: after its one space come the label's character codes, `;`, and the bytes, each list possibly empty, and it answers `ok:` and the character codes of the PEM text, or `none`. `pemdec` answers `ok:`, the label's character codes, `;`, and the bytes, or `none`. The tool prints `error` for any other line, including `pemenc` without its space or its `;`, an unknown operation, a number that is not plain decimal digits, a byte above 255, or a character code that is not a Unicode scalar value. A line may end in LF or CR LF; nothing else around a request is ignored.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use, written from the standards and checked against their test values, are in `Spec/Defs.lean`.

| Property | Theorem |
|----------|---------|
| Hex encodes each byte as two digits, high half first, from `0123456789abcdef`. | `Spec.hex_encode_nil`, `Spec.hex_encode_cons` |
| Hex decoding gives back what was encoded. | `Spec.hex_decode_encode` |
| Hex decoding accepts any mix of upper and lower case. | `Spec.hex_decode_any_case` |
| Hex decoding accepts nothing that is not an encoding, up to case. | `Spec.hex_encode_decode` |
| Hex matches the test vectors of RFC 4648, section 10, in lowercase, and decodes them as the RFC writes them. | `Spec.hex_rfc4648_vectors` |
| Base 64 encodes three bytes as one group of four characters from RFC 4648 Table 1. | `Spec.base64_encode_nil`, `Spec.base64_encode_three` |
| Base 64 encodes a final one or two bytes with zero fill and `==` or `=` padding. | `Spec.base64_encode_one`, `Spec.base64_encode_two` |
| Base 64 decoding gives back what was encoded. | `Spec.base64_decode_encode` |
| Base 64 decoding accepts exactly the encodings and nothing else. | `Spec.base64_encode_decode` |
| Base 64 encoding matches the test vectors of RFC 4648, section 10. | `Spec.base64_rfc4648_vectors` |
| The table-driven CRC-32 equals the bit-at-a-time definition. | `Spec.crc32_eq` |
| The CRC-32 of `123456789` is the standard check value `0xCBF43926`. | `Spec.crc32_check` |
| A frame is the message followed by its CRC-32, low byte first. | `Spec.frame_layout` |
| Unframing a frame gives back the message. | `Spec.unframe_frame` |
| Unframing accepts nothing that is not a frame. | `Spec.frame_unframe` |
| Percent-encoding writes each byte as `Spec.pctByte` says: an unreserved character as itself, any other byte as `%` and two uppercase digits. | `Spec.percent_encode_eq` |
| Percent-decoding reads exactly what `Spec.PctReads` allows, as it says. | `Spec.percent_decode_iff` |
| Percent-decoding gives back what was encoded. | `Spec.percent_decode_encode` |
| The examples of RFC 3986, sections 2.1, 2.3, 2.5 and 6.2.2; the reserved and unreserved characters; decoding once; and text the decoder refuses. | `Spec.percent_vectors` |
| PEM encoding gives `Spec.pemText` for a label the `label` rule allows, and fails on any other label. | `Spec.pem_encode_iff` |
| PEM decoding gives a label and data exactly when `Spec.StrictPem` holds: the text is the message's lines, each followed by any `eol`. | `Spec.pem_decode_iff` |
| PEM decoding gives back what was encoded. | `Spec.pem_decode_encode` |
| `Luhn.valid` decides the Luhn sum's rule. | `Spec.luhn_valid_iff` |
| The check digit is a digit, and the only one that makes the payload valid. | `Spec.luhn_checkDigit` |
| One digit typed wrong is caught. | `Spec.luhn_single_error` |
| Two adjacent different digits swapped are caught, unless they are 0 and 9. | `Spec.luhn_adjacent_swap` |
| An adjacent 0 and 9 swapped is never caught. | `Spec.luhn_swap_09` |
| 79927398713, its check digit, a wrong check digit, a test card number, and `10`. | `Spec.luhn_vectors` |
| `Iban.valid` decides `Spec.IbanValid`: the shape, and the rearranged number mod 97 is 1. | `Spec.iban_valid_iff` |
| `checkDigits` gives exactly the two digits from 02 to 98 that make the IBAN pass. | `Spec.iban_checkDigits_iff` |
| One digit for another, or one letter for another, is caught. | `Spec.iban_substitution` |
| Two adjacent digits, or two adjacent letters, swapped are caught. | `Spec.iban_adjacent_swap` |
| Example IBANs and their check digits; a digit wrong; lower case refused; a letter and a digit swapped, both passing. | `Spec.iban_vectors` |
| RFC 7468's Figure 15, written exactly as the RFC prints it and read back with CR LF; empty data and an empty label; labels the rule refuses; texts the decoder refuses. | `Spec.pem_vectors` |

Together these fix every output. The encoders, `crc32`, and `frame` are given exactly. Each of the hex and base 64 decoders and `unframe` accepts exactly the outputs of its encoder or `frame` (for hex, up to ASCII case), and returns the matching input. The percent-decoder accepts more than the encoder writes, since text may carry reserved characters as they are and escapes in lowercase: `Spec.PctReads` gives what it accepts and what each text reads as. The PEM decoder accepts what the PEM encoder writes, with any `eol` in place of each LF: `Spec.StrictPem` gives what it accepts. `Luhn.valid` and `Iban.valid` are decided exactly, `Iban.checkDigits` is given exactly, and `Luhn.checkDigit` is given exactly for a payload of digits. A function that did nothing, or that accepted too much, would fail at least one of them.

## Oracle

Python's `binascii.hexlify` and `binascii.unhexlify`, `base64.b64encode` and `binascii.a2b_base64(strict_mode=True)`, `zlib.crc32`, and `urllib.parse.quote(safe="")` and `urllib.parse.unquote_to_bytes`. `unquote_to_bytes` passes a bad escape through, so the tests give it only text that `Spec.PctReads` accepts, checked with a regular expression; the decoder must refuse the rest. For PEM, a strict parser written in the tests from the ABNF of RFC 7468 decides every decoding, with the base 64 checked by strict `binascii.a2b_base64` and by encoding it again; where it accepts a text with the `CERTIFICATE` label, Python's `ssl.PEM_cert_to_DER_cert` must read the same data. Encoding is checked against `ssl.DER_cert_to_PEM_cert` for the `CERTIFICATE` label and against an encoder written in the tests for the others.
