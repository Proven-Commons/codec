# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`, `ssl.DER_cert_to_PEM_cert`
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 245115 of the inputs are mutated encodings or frames
- By operation: b64dec 101665, b64enc 50825, crc 50827, error 77, frame 50825, hexdec 152491, hexenc 50828, pctdec 254697, pctenc 51081, pemdec 83920, pemenc 51114, unframe 101650
- Malformed requests answered `error`: 77 of 77
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 9256 (9256 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
