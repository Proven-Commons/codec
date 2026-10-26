# Specification: codec

Four small codecs: hex, base 64, CRC-32 with a frame around a message, and percent-encoding. A reviewer who did not write this specification approves it, together with `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

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

## Valid inputs and errors

Every encoder input and every `crc32` and `frame` input is valid. The decoders and `unframe` return `none` for anything they do not accept. No function can fail any other way.

The command-line tool in `Main.lean` reads one request per line and prints one answer per line. A request is an operation, then optionally one space and its comma-separated numbers; with no numbers after the space, the input is empty. The tool prints `error` for any other line, an unknown operation, a number that is not plain decimal digits, a byte above 255, or a character code that is not a Unicode scalar value. A line may end in LF or CR LF; nothing else around a request is ignored.

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
| Base 64 matches the test vectors of RFC 4648, section 10, and decodes them. | `Spec.base64_rfc4648_vectors` |
| The table-driven CRC-32 equals the bit-at-a-time definition. | `Spec.crc32_eq` |
| The CRC-32 of `123456789` is the standard check value `0xCBF43926`. | `Spec.crc32_check` |
| A frame is the message followed by its CRC-32, low byte first. | `Spec.frame_layout` |
| Unframing a frame gives back the message. | `Spec.unframe_frame` |
| Unframing accepts nothing that is not a frame. | `Spec.frame_unframe` |
| Percent-encoding writes each byte as `Spec.pctByte` says: an unreserved character as itself, any other byte as `%` and two uppercase digits. | `Spec.percent_encode_eq` |
| Percent-decoding reads exactly what `Spec.PctReads` allows, as it says. | `Spec.percent_decode_iff` |
| Percent-decoding gives back what was encoded. | `Spec.percent_decode_encode` |
| The examples of RFC 3986, sections 2.1, 2.3, 2.5 and 6.2.2; the reserved and unreserved characters; decoding once; and text the decoder refuses. | `Spec.percent_vectors` |

Together these fix every output. The encoders, `crc32`, and `frame` are given exactly. Each of the hex and base 64 decoders and `unframe` accepts exactly the outputs of its encoder or `frame` (for hex, up to ASCII case), and returns the matching input. The percent-decoder accepts more than the encoder writes, since text may carry reserved characters as they are and escapes in lowercase: `Spec.PctReads` gives what it accepts and what each text reads as. A function that did nothing, or that accepted too much, would fail at least one of them.

## Oracle

Python's `binascii.hexlify` and `binascii.unhexlify`, `base64.b64encode` and `binascii.a2b_base64(strict_mode=True)`, `zlib.crc32`, and `urllib.parse.quote(safe="")` and `urllib.parse.unquote_to_bytes`. `unquote_to_bytes` passes a bad escape through, so the tests give it only text that `Spec.PctReads` accepts, checked with a regular expression; the decoder must refuse the rest.
