# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `binascii`, `base64`, `zlib` (zlib 1.3)
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 285676 of the inputs are mutated encodings or frames
- By operation: b32dec 142854, b32enc 71420, b64dec 142854, b64enc 71420, crc 71422, error 73, frame 71420, hexdec 214275, hexenc 71423, unframe 142839
- Malformed requests answered `error`: 73 of 73
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 16039 (12676 with unused bits before the padding not zero, 3363 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Strict base 32 rejections where Python decodes: 5756 (5756 with base 32 unused bits before the padding not zero, 0 with base 32 padding after a whole group, which Python decodes)
- Failures: 0
