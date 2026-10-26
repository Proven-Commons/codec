# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`; for PEM, a strict encoder and parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label; for Luhn and IBAN, the rules written in tests/run_tests.py, with Python's integers for the IBAN number
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 319602 of the inputs are mutated encodings or frames
- By operation: b32dec 64901, b32enc 32443, b64dec 64901, b64enc 32443, crc 32445, error 94, frame 32443, hexdec 97345, hexenc 32446, iban 64915, ibancheck 64931, luhn 98450, luhncheck 33554, pctdec 162787, pctenc 32699, pemdec 55554, pemenc 32763, unframe 64886
- Malformed requests answered `error`: 94 of 94
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 5796 (5796 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Strict base 32 rejections where Python decodes: 2624 (2624 with base 32 unused bits before the padding not zero, 0 with base 32 padding after a whole group, which Python decodes)
- Failures: 0
