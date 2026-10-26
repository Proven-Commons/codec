# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `binascii`, `base64`, `zlib` (zlib 1.3), `urllib.parse`; for PEM, a strict encoder and parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261024
- Inputs: 1000000
- Mutated: 245733 of the inputs are mutated encodings or frames
- By operation: b64dec 101405, b64enc 50695, crc 50697, error 77, frame 50695, hexdec 152103, hexenc 50699, pctdec 254047, pctenc 50951, pemdec 86226, pemenc 51015, unframe 101390
- Malformed requests answered `error`: 77 of 77
- Last lines with no LF, sent alone, answered right: 6 of 6
- Strict base 64 rejections where Python decodes: 9024 (9024 with unused bits before the padding not zero, 0 with padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode)
- Failures: 0
