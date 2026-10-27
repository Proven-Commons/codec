# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`; for PEM, a strict encoder and parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label; for Luhn and IBAN, the rules written in tests/run_tests.py, with Python's integers for the IBAN number
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 319608 of the inputs are mutated encodings or frames
- By operation: b32dec 64892, b32enc 32439, b64dec 64892, b64enc 32439, crc 32440, error 94, frame 32438, hexdec 97332, hexenc 32442, iban 64923, ibancheck 64939, luhn 98435, luhncheck 33549, pctdec 162762, pctenc 32694, pemdec 55656, pemenc 32758, unframe 64876
- Malformed requests answered `error`: 94 of 94
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 5797 (5797 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Strict base 32 rejections where Python decodes: 2655 (2655 with base 32 unused bits before the padding not zero, 0 with base 32 padding after a whole group, which Python decodes)
- Failures: 0
