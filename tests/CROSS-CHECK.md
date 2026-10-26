# Cross-check with Go

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261024
- Texts given to the percent-decoder: 194412, of which 166412 it accepts
- Go: `net/url.PathUnescape`, go version go1.24.7 linux/amd64
- Texts in US-ASCII: 180340, differences: 0
- Texts with a character outside US-ASCII: 14072, of which this decoder accepts 0. Go reads such a character as its UTF-8 bytes, and gives the same answer on 3917 of them (where it finds a bad escape too) and a different one on 10155.


## PEM

- Go: `encoding/pem`, go version go1.24.7 linux/amd64
- Encoding requests: 39088. The same text from both: 33035. Go writes a label this encoder refuses: 6053. Other differences: 0.
- Decoding requests: 66050. The same answer from both, with nothing left over in Go: 39312. Go reads text this decoder refuses: 3619. This decoder accepts text with a CR alone as a line end, as RFC 7468's `eol` allows, and Go does not, since it ends lines at LF only: 22677. This decoder reads empty data under a label with a `:`, and Go takes the END line for a header: 442. Other differences, where this decoder accepts text that Go reads differently or not at all: 0.


## Luhn and IBAN

- python-stdnum 2.2: `luhn.is_valid`, `luhn.calc_check_digit`, `iban.calc_check_digits`, and `iso7064.mod_97_10.is_valid` for the IBAN check
- Requests: 234856. The same answer: 234855. An empty Luhn number, which this codec passes and stdnum refuses: 1. IBAN text with a space, a dash, a dot or a lower-case letter, which stdnum removes or upper-cases first and this codec refuses: 0. Other differences: 0.
- The same IBANs given to stdnum's whole `iban.validate`: the same answer on 38564. It refuses, for a country code or BBAN format not in the SWIFT registry, 38983 that pass this codec's check, which does not use the registry. Read after stdnum's normalizing: 2. Other differences: 0.

