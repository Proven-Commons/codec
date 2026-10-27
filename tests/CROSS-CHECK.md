# Cross-check with Go

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261024
- Texts given to the percent-decoder: 162762, of which 139643 it accepts
- Go: `net/url.PathUnescape`, go version go1.24.7 linux/amd64
- Texts in US-ASCII: 151159, differences: 0
- Texts with a character outside US-ASCII: 11603, of which this decoder accepts 0. Go reads such a character as its UTF-8 bytes, and gives the same answer on 3121 of them (where it finds a bad escape too) and a different one on 8482.


## PEM

- Go: `encoding/pem`, go version go1.24.7 linux/amd64
- Encoding requests: 32758. The same text from both: 27836. Go writes a label this encoder refuses: 4922. Other differences: 0.
- Decoding requests: 55656. The same answer from both, with nothing left over in Go: 33243. Go reads text this decoder refuses: 3107. This decoder accepts text with a CR alone as a line end, as RFC 7468's `eol` allows, and Go does not, since it ends lines at LF only: 18931. This decoder reads empty data under a label with a `:`, and Go takes the END line for a header: 375. Other differences, where this decoder accepts text that Go reads differently or not at all: 0.


## Luhn and IBAN

- python-stdnum 2.2: `luhn.is_valid`, `luhn.calc_check_digit`, `iban.calc_check_digits`, and `iso7064.mod_97_10.is_valid` for the IBAN check. stdnum has no check of the IBAN shape on its own, so for `iban` requests the shape comes from the tests' own regular expression and only the mod 97-10 check from stdnum
- Requests: 261851. The same answer: 253274. An empty Luhn number, which this codec passes and stdnum refuses: 1. IBAN text with a space, a dash, a dot or a lower-case letter, which stdnum removes or upper-cases first and this codec refuses: 3828. A country code that is not two characters, which this codec refuses and stdnum's `calc_check_digits` takes, since it does not check the country code: 6. A country code and BBAN that do not have the IBAN's shape, such as an empty BBAN or one of 31 characters, which this codec refuses and `calc_check_digits` takes, since it does not check the shape: 1866. A Luhn number with a value above 9, which this codec refuses as not a digit and which, written out for stdnum, becomes more than one digit: 2871. A Luhn number with more than seven digits after its leading zeros, which this tool answers with `error` and stdnum reads: 5, of which stdnum gives `false` on 5. Other differences: 0.
- The same IBANs given to stdnum's whole `iban.validate`, which checks the shape itself: the same answer on 32301, of which 18 pass both, 12 of them the tests' example IBANs. It refuses, for a country code or BBAN format not in the SWIFT registry, 32619 that pass this codec's check, which does not use the registry; and 1 for one of its own national checks, such as a bank code missing from its list. Read after stdnum's normalizing: 2. Other differences: 0.

