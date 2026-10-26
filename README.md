# codec: hex, base 64, CRC-32 and percent-encoding, proved

Four small codecs in Lean, each with machine-checked proofs that it does exactly what its specification says, and tested against Python's standard library on a million inputs in all (see `tests/TEST-RESULTS.md`). Hex is written as Python's `bytes.hex()` writes it, base 64 follows RFC 4648, the CRC-32 is the one in gzip, zip, and PNG, and percent-encoding follows RFC 3986. They are also the material for Level 0 of the [Proven Commons academy](https://github.com/Proven-Commons/mission): a first proof, read and then written, on code small enough to hold in your head.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`. Together they fix every output: the encoders and the checksum are given exactly. The hex and base 64 decoders and unframing accept exactly the outputs of their encoder or of framing (for hex, up to ASCII case) and return the matching input. The percent-decoder accepts more than the encoder writes, such as reserved characters as they are and escapes in lowercase, and `Spec.PctReads` gives exactly what it accepts and what each text reads as.

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

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, the checks that bytes are below 256 and character codes are Unicode scalar values, and the conversions `Nat.toUInt8`, `Char.ofNat`, and `String.ofList`. The differential tests cover them, malformed requests included.
- Speed. The code works on lists, which suits proofs, not large data.
- Base 64 variants: the URL-safe alphabet, line breaks, and unpadded text are not supported. Strict decoding also rejects two kinds of text that Python's strict mode decodes: unused bits before the padding that are not zero, and, in Python 3.11 and in 3.12 before 3.12.4, padding after a whole group, such as `Zm9v=`. The tests count both.
- Percent-encoding with another set of characters left as they are, such as the `+` for a space of HTML forms or the wider sets of JavaScript's `encodeURIComponent`. Which characters a URI component allows, and whether text is decoded at the right layer, are for a URI parser. This codec decodes what it is given, once, and does not check that it is URI text: it reads any US-ASCII character but `%` as itself, and reads `%00` as a NUL byte. Section 7.3 of RFC 3986 says `%00` should be rejected where an application does not expect raw data in a component; that check is the caller's.
- Hex with spaces, line breaks, or a `0x` prefix, which decoding rejects. Hex is RFC 4648 base 16 up to case: it writes lowercase, as Python does, where the RFC's alphabet is uppercase.
- Other checksums, such as CRC-32C. A frame is this library's own layout, a message and its CRC-32, not a gzip or zip file.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the fixed-width integer operations in CRC-32 and the arithmetic on natural numbers.
- The operating system and hardware it runs on.
- Python's standard library and zlib, as the oracle in the differential tests. The record names their versions.

This project has no dependencies beyond Lean itself.

## Other decoders

`tests/CROSS-CHECK.md` records a one-off comparison of the percent-decoder with Go's `net/url.PathUnescape`. It is not part of the verified bar. On every text in US-ASCII that the tests give the decoder, Go gives the same answer, bad escapes included. Go reads a character outside US-ASCII as its UTF-8 bytes, where this decoder refuses it.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.11 or later.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean. The test script compares the tool with Python's standard library on a million inputs in all, from a recorded seed, and rewrites `tests/TEST-RESULTS.md`. Frames are compared with messages framed by `zlib.crc32`. Python 3.11.17, 3.12.3, and 3.13.17 give the same seed, count, and failures; they differ only in how many strict rejections each kind accounts for. `tests/planted_bugs.py` plants 110 small bugs in the tool, one at a time in a copy, and `tests/PLANTED-BUGS.md` records that the tests catch 101 of them and why the other 9 change nothing the tool prints.

## Layout

- `Codec/Hex.lean`, `Codec/Base64.lean`, `Codec/Crc32.lean`, `Codec/Percent.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the standards, with checks against their test values.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/cross_check.py` and `tests/cross_check/`: the one-off comparison with Go.
