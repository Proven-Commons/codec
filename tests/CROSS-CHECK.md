# Cross-check with Go

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261024
- Texts given to the percent-decoder: 254697, of which 218319 it accepts
- Go: `net/url.PathUnescape`, go version go1.24.7 linux/amd64
- Texts in US-ASCII: 236466, differences: 0
- Texts with a character outside US-ASCII: 18231, of which this decoder accepts 0. Go reads such a character as its UTF-8 bytes, and gives the same answer on 4869 of them (where it finds a bad escape too) and a different one on 13362.


## PEM

- Go: `encoding/pem`, go version go1.24.7 linux/amd64
- Encoding requests: 51114. The same text from both: 41955. Go writes a label this encoder refuses: 9159. Other differences: 0.
- Decoding requests: 83920. The same answer from both, with nothing left over in Go: 50108. Go reads text this decoder refuses: 4721. This decoder accepts text with a CR alone as a line end, as RFC 7468's `eol` allows, and Go does not, since it ends lines at LF only: 29091. Other differences, where this decoder accepts text that Go reads differently or not at all: 0.

