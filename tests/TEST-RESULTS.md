# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.12.3 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 249760 of the inputs are mutated encodings or frames
- By operation: b32dec 99919, b32enc 49953, b64dec 99920, b64enc 49953, crc 49954, error 75, frame 49952, hexdec 149874, hexenc 49956, pctdec 250332, pctenc 50208, unframe 99904
- Malformed requests answered `error`: 75 of 75
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 11265 (8945 with unused bits before the padding not zero, 2320 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Strict base 32 rejections where Python decodes: 4019 (4019 with base 32 unused bits before the padding not zero, 0 with base 32 padding after a whole group, which Python decodes)
- Failures: 0
