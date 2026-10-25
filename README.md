# codec: hex, base 64, and CRC-32, proved

Three small codecs in Lean, each with machine-checked proofs that it does exactly what its specification says, and tested against Python's standard library on a million inputs in all (see `tests/TEST-RESULTS.md`). Hex is written as Python's `bytes.hex()` writes it, base 64 follows RFC 4648, and the CRC-32 is the one in gzip, zip, and PNG. They are also the material for Level 0 of the [Proven Commons academy](https://github.com/Proven-Commons/mission): a first proof, read and then written, on code small enough to hold in your head.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`. Together they fix every output: the encoders and the checksum are given exactly, and each decoder accepts exactly the outputs of its encoder (for hex, up to ASCII case) and returns the matching input.

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
| Base 64 matches the test vectors of RFC 4648, section 10. | `Spec.base64_rfc4648_vectors` |
| The table-driven CRC-32 equals the CRC-32 defined one bit at a time. | `Spec.crc32_eq` |
| The CRC-32 of `123456789` is the standard check value `0xCBF43926`. | `Spec.crc32_check` |
| A frame is the message followed by its CRC-32, low byte first. | `Spec.frame_layout` |
| Unframing a frame gives back the message. | `Spec.unframe_frame` |
| Unframing accepts nothing that is not a frame. | `Spec.frame_unframe` |

The command-line tool in `Main.lean` calls these functions directly.

## What is not proved

- Reading requests and printing answers in `Main.lean`: splitting lines, the decimal parser, the checks that bytes are below 256 and character codes are Unicode scalar values, and the conversions `Nat.toUInt8`, `Char.ofNat`, and `String.ofList`. The differential tests cover them, malformed requests included.
- Speed. The code works on lists, which suits proofs, not large data.
- Base 64 variants: the URL-safe alphabet, line breaks, and unpadded text are not supported. Strict decoding also rejects two kinds of text that Python's strict mode decodes: unused bits before the padding that are not zero, and, in Python 3.11 and in 3.12 before 3.12.4, padding after a whole group, such as `Zm9v=`. The tests count both.
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

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.11 or later.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean. The test script compares the tool with Python's standard library on a million inputs in all, from a recorded seed, and rewrites `tests/TEST-RESULTS.md`. Frames are compared with messages framed by `zlib.crc32`. Python 3.11.17, 3.12.3, and 3.13.17 give the same seed, count, and failures; they differ only in how many strict rejections each kind accounts for.

## Layout

- `Codec/Hex.lean`, `Codec/Base64.lean`, `Codec/Crc32.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from the standards, with checks against their test values.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
