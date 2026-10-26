# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 235073 of the inputs are mutated encodings or frames
- By operation: b64dec 117552, b64enc 58769, crc 58771, error 71, frame 58769, hexdec 176323, hexenc 58772, pctdec 294412, pctenc 59024, unframe 117537
- Malformed requests answered `error`: 71 of 71
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 10562 (10562 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
