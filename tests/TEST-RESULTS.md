# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`; for PEM, a strict encoder and parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label; for Luhn and IBAN, the rules written in tests/run_tests.py, with Python's integers for the IBAN number
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 318258 of the inputs are mutated encodings or frames
- By operation: b64dec 71932, b64enc 35959, crc 35961, error 85, frame 35959, hexdec 107893, hexenc 35962, iban 71944, ibancheck 71960, luhn 108995, luhncheck 37069, pctdec 180362, pctenc 36214, pemdec 61510, pemenc 36278, unframe 71917
- Malformed requests answered `error`: 85 of 85
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 6450 (6450 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
