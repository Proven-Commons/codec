# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`; for PEM, a strict encoder and parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 265473 of the inputs are mutated encodings or frames
- By operation: b64dec 77551, b64enc 38769, crc 38770, error 82, frame 38768, hexdec 116322, hexenc 38772, iban 77549, ibancheck 38781, luhn 78647, luhncheck 39879, pctdec 194412, pctenc 39024, pemdec 66050, pemenc 39088, unframe 77536
- Malformed requests answered `error`: 82 of 82
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 7102 (7102 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
