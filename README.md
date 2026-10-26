# codec: hex, base 64, CRC-32, percent-encoding, PEM and check digits, proved

Small codecs and check digits in Lean, each with machine-checked proofs that it does exactly what its specification says, and tested on a million inputs in all against Python's standard library, for PEM against an encoder and strict parser written in the tests from RFC 7468, and for the check digits against the Luhn and IBAN rules written in the tests (see `tests/TEST-RESULTS.md`). Hex is written as Python's `bytes.hex()` writes it, base 64 follows RFC 4648, the CRC-32 is the one in gzip, zip, and PNG, percent-encoding follows RFC 3986, PEM is the strict form of RFC 7468, the text that wraps certificates and keys, and the check digits are Luhn's, as on card numbers, and the IBAN's, by ISO 7064 MOD 97-10. The check digits come with what each catches and, also as theorems, an error each misses. They are also the material for Level 0 of the [Proven Commons academy](https://github.com/Proven-Commons/mission): a first proof, read and then written, on code small enough to hold in your head.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`. Together they fix every output: the encoders and the checksum are given exactly. The hex and base 64 decoders and unframing accept exactly the outputs of their encoder or of framing (for hex, up to ASCII case) and return the matching input. The percent-decoder accepts more than the encoder writes, such as reserved characters as they are and escapes in lowercase, and `Spec.PctReads` gives exactly what it accepts and what each text reads as. The PEM decoder accepts what the PEM encoder writes, with any of the line ends LF, CR, and CR LF, and `Spec.StrictPem` gives exactly what it accepts. `Luhn.valid` and `Iban.valid` are decided exactly, and `Iban.checkDigits` is given exactly. `Luhn.checkDigit` is given exactly for a payload of digits 0 to 9; on a payload with a value above 9, no statement says what it gives.

| Claim | Theorem |
|-------|---------|
| Hex writes each byte as two digits, high half first, from `0123456789abcdef`. | `Spec.hex_encode_nil`, `Spec.hex_encode_cons` |
| Hex decoding gives back what was encoded. | `Spec.hex_decode_encode` |
| Hex decoding accepts any mix of upper and lower case. | `Spec.hex_decode_any_case` |
| Hex decoding accepts nothing that is not an encoding, up to case. | `Spec.hex_encode_decode` |
| Hex matches the test vectors of RFC 4648, section 10: encoding gives them in lowercase, and decoding reads them as the RFC writes them, in uppercase. | `Spec.hex_rfc4648_vectors` |
| Base 64 writes three bytes as one group of four characters from RFC 4648, Table 1. | `Spec.base64_encode_nil`, `Spec.base64_encode_three` |
| Base 64 writes a final one or two bytes with zero fill and `==` or `=` padding, as RFC 4648 section 4 says. | `Spec.base64_encode_one`, `Spec.base64_encode_two` |
| Base 64 decoding gives back what was encoded. | `Spec.base64_decode_encode` |
| Base 64 decoding accepts exactly the encodings and nothing else. | `Spec.base64_encode_decode` |
| Base 64 matches the test vectors of RFC 4648, section 10: encoding gives them, and decoding reads them back. | `Spec.base64_rfc4648_vectors` |
| The table-driven CRC-32 equals the CRC-32 defined one bit at a time. | `Spec.crc32_eq` |
| The CRC-32 of `123456789` is the standard check value `0xCBF43926`. | `Spec.crc32_check` |
| A frame is the message followed by its CRC-32, low byte first. | `Spec.frame_layout` |
| Unframing a frame gives back the message. | `Spec.unframe_frame` |
| Unframing accepts nothing that is not a frame. | `Spec.frame_unframe` |
| Percent-encoding keeps the unreserved characters of RFC 3986, section 2.3, and writes every other byte as `%` and two uppercase digits, as section 2.1 recommends. | `Spec.percent_encode_eq` |
| Percent-decoding reads `%` and two hex digits (the `pct-encoded` rule of section 2.1), in either case, as one byte, and any other US-ASCII character but `%` as itself. It does not check which characters a URI allows, so a space or a control character reads as itself. It refuses a `%` without two hex digits after it, and any character outside US-ASCII, rather than passing them through. | `Spec.percent_decode_iff` |
| Percent-decoding gives back what was encoded. | `Spec.percent_decode_encode` |
| Percent-encoding matches the examples of RFC 3986, sections 2.1, 2.3, 2.5 and 6.2.2, and decodes once: `%252E` decodes to the text `%2E`, not to a dot. | `Spec.percent_vectors` |
| PEM encoding writes the strict form of RFC 7468 (Figure 3): `-----BEGIN label-----`, the base 64 of the data in lines of 64 characters with the last at most 64, and `-----END label-----`, each line ending in LF. For empty data, which that form cannot express, it writes the BEGIN and END lines alone (see What is not proved). It refuses a label that the `label` rule of section 3 does not allow. | `Spec.pem_encode_iff` |
| PEM decoding reads exactly one message in the strict form, or for empty data the BEGIN and END lines alone, with each line ending in LF, CR, or CR LF, and gives its label and data. So it refuses a different label on the END line, blanks, headers, text before or after the message, lines of another length, and base 64 that is not exactly the encoding of the data. | `Spec.pem_decode_iff` |
| PEM decoding gives back the label and data that were encoded. | `Spec.pem_decode_encode` |
| Luhn: `valid` decides the rule (every second digit from the right doubled, less 9 above 9, the sum a multiple of 10), and, for a payload of digits, the check digit is the one digit that makes it valid. | `Spec.luhn_valid_iff`, `Spec.luhn_checkDigit` |
| Luhn catches any one digit typed wrong, and any two adjacent different digits typed in the wrong order, except 0 and 9. | `Spec.luhn_single_error`, `Spec.luhn_adjacent_swap` |
| Among adjacent swaps, Luhn misses only one: an adjacent 0 and 9 swapped is never caught. | `Spec.luhn_swap_09` |
| Luhn gives the common worked example, 79927398713, and a test card number. | `Spec.luhn_vectors` |
| IBAN: `valid` decides the check of ISO 13616 by ISO 7064 MOD 97-10 (the shape, and the rearranged number mod 97), and `checkDigits` gives exactly the two digits from 02 to 98 that make an IBAN pass. | `Spec.iban_valid_iff`, `Spec.iban_checkDigits_iff` |
| IBAN catches one digit typed for another or one letter for another, and two adjacent digits or two adjacent letters typed in the wrong order. | `Spec.iban_substitution`, `Spec.iban_adjacent_swap` |
| IBAN gives the SWIFT registry's UK example and Germany's, France's and Norway's, and their check digits; and its blind spot: a letter and a digit swapped, `4B1` for `41B`, gives another IBAN that passes. | `Spec.iban_vectors` |
| PEM encoding writes RFC 7468's Figure 15 exactly as the RFC prints it, and decoding reads it back with CR LF line ends; empty data, an empty label, labels the rule refuses, and texts the decoder refuses. | `Spec.pem_vectors` |

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, the checks that bytes are below 256 and character codes are Unicode scalar values, `luhncheck`'s check that every number is a digit, the `;` that splits `pemenc` and `ibancheck`, and the conversions `Nat.toUInt8`, `Char.ofNat`, and `String.ofList`. The differential tests cover them, malformed requests included.
- Other errors the check digits miss. Luhn never catches a jump transposition, `abc` for `cba`, since both outer digits are doubled or neither is, nor the twin errors `22` for `55`, `33` for `66` and `44` for `77`. IBAN can miss a letter and a digit swapped, or a letter typed for a digit. No theorem covers these, and the tests do not count them.
- `Luhn.checkDigit` on a payload with a value above 9. No statement says what it gives there; the tool's `luhncheck` answers `error`.
- Speed. The code works on lists, which suits proofs, not large data.
- Base 64 variants: the URL-safe alphabet, line breaks, and unpadded text are not supported. Strict decoding also rejects two kinds of text that Python's strict mode decodes: unused bits before the padding that are not zero, and, in Python 3.11 and in 3.12 before 3.12.4, padding after a whole group, such as `Zm9v=`. The tests count both.
- Percent-encoding with another set of characters left as they are, such as the `+` for a space of HTML forms or the wider sets of JavaScript's `encodeURIComponent`. Which characters a URI component allows, and whether text is decoded at the right layer, are for a URI parser. This codec decodes what it is given, once, and does not check that it is URI text: it reads any US-ASCII character but `%` as itself, and reads `%00` as a NUL byte. Section 7.3 of RFC 3986 says `%00` should be rejected where an application does not expect raw data in a component; that check is the caller's.
- PEM in any form but the strict one. The standard and lax forms of RFC 7468 (Figures 1 and 2), which allow blanks, empty lines, and other line lengths, are refused, as are the headers of older PEM (RFC 1421), text around the message, and a file of several messages. Which label goes with which kind of data, and what that data means, is for the caller: a label is any text the `label` rule allows.
- Two points where this codec departs from the strict form. The strict form has no text for empty data, since its last line of base 64 needs four characters. Here empty data is the BEGIN and END lines alone, as Go's `encoding/pem` and Python's `ssl` write it. With LF line ends, only the lax form of RFC 7468 (Figure 2) allows that text; the text the standard form (Figure 1) gives empty data, with one empty line between BEGIN and END, is refused. And the strict form allows a last group whose unused bits are not zero, which this codec's strict base 64 refuses.
- The IBAN registry. The check is the shape and the mod-97 sum only: each country's BBAN length and format, in the SWIFT IBAN Registry, are not checked, and nor is whether the country code is one. An IBAN with spaces or lower-case letters, which many tools tidy first, is refused. Check digits 00, 01 and 99 never come from the computation, which gives 02 to 98, but an IBAN with them can still pass the check, as 01 and 98 are the same mod 97.
- Luhn on an empty number, which passes, since its sum is 0. Each digit is a number 0 to 9; there is no text form with spaces or dashes.
- Hex with spaces, line breaks, or a `0x` prefix, which decoding rejects. Hex is RFC 4648 base 16 up to case: it writes lowercase, as Python does, where the RFC's alphabet is uppercase.
- Other checksums, such as CRC-32C. A frame is this library's own layout, a message and its CRC-32, not a gzip or zip file.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the fixed-width integer operations in CRC-32 and the arithmetic on natural numbers.
- The operating system and hardware it runs on.
- Python's standard library and zlib, for PEM an encoder and strict parser written in `tests/run_tests.py` from RFC 7468, and for Luhn and IBAN the rules written in `tests/run_tests.py`, with Python's integers for the IBAN number, as the oracles in the differential tests. The record names their versions.

This project has no dependencies beyond Lean itself.

## Other decoders

`tests/CROSS-CHECK.md` records a one-off comparison of the percent-decoder with Go's `net/url.PathUnescape`, of PEM with Go's `encoding/pem`, and of the check digits with python-stdnum. It is not part of the verified bar. On every text in US-ASCII that the tests give the decoder, Go gives the same answer, bad escapes included. Go reads a character outside US-ASCII as its UTF-8 bytes, where this decoder refuses it.

For Luhn, python-stdnum 2.2 gives the same answer on every request the tests make, apart from the empty number, which it refuses, and a value above 9, which becomes more than one digit when written out for it. For IBAN, stdnum has no check of the shape on its own. Its mod 97-10 check gives the same answer on every IBAN request, with the shape taken from the tests' own rule. Its `calc_check_digits` gives the same check digits wherever the country code and BBAN have the IBAN's shape; it checks neither, and it removes spaces, dashes and dots and upper-cases letters first. Its whole `iban.validate` checks each country's format in the SWIFT registry. It never accepts an IBAN this codec refuses, apart from three it reads after that tidying. But it refuses almost every random IBAN this codec accepts, for a country code or format not in the registry, and one more for its own list of Belgian bank codes. 20 pass both. `tests/CROSS-CHECK.md` gives the counts.

For PEM, the cross-check tries 17 labels that the RFC's `label` rule allows, and for each of them Go writes the same text, empty data included; it also writes labels the rule refuses. Go reads PEM laxly: it skips text around a block and takes headers and blanks, which this decoder refuses. And it ends lines at LF only, so it refuses most text with a CR alone as a line end, which RFC 7468 allows and this decoder reads. Go also refuses a message with empty data whose label holds a `:`, such as `-----BEGIN A:B-----` then `-----END A:B-----`, which Go itself writes: it takes the END line for an RFC 1421 header. Apart from those, on every text the cross-check gives this decoder and it accepts, Go reads the same label and data.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.11 or later.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean. The test script compares the tool with Python's standard library, for PEM with an encoder and strict parser written in the script, and for Luhn and IBAN with the rules written in the script, on a million inputs in all, from a recorded seed, and rewrites `tests/TEST-RESULTS.md`. Frames are compared with messages framed by `zlib.crc32`. The record is from Python 3.13.17. Runs under 3.11.17 and 3.12.3 give the same inputs and failures, and differ only in how many strict base 64 rejections each kind accounts for; those runs are not kept in the repo. `tests/planted_bugs.py` plants 137 small bugs in the command-line tool and the code under proof, one at a time in a copy, and `tests/PLANTED-BUGS.md` records that the tests catch 128 of them and why the other 9 print the same on stdout as the real tool.

## Layout

- `Codec/Hex.lean`, `Codec/Base64.lean`, `Codec/Crc32.lean`, `Codec/Percent.lean`, `Codec/Pem.lean`, `Codec/Luhn.lean`, `Codec/Iban.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the standards, with checks against their test values.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests, and `tests/TEST-RESULTS.md`, the record they write.
- `tests/planted_bugs.py` and `tests/PLANTED-BUGS.md`: the planted bugs, and the record of which ones the tests catch.
- `tests/cross_check.py` and `tests/cross_check/`: the one-off comparison with Go and python-stdnum.
