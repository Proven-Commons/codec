# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 272697 of the inputs are mutated encodings or frames
- By operation: b64dec 181814, b64enc 90900, crc 90902, error 69, frame 90899, hexdec 272715, hexenc 90903, unframe 181798
- Malformed requests answered `error`: 69 of 69
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 16333 (16333 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
