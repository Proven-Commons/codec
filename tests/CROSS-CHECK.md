# Cross-check with Go

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261024
- Texts given to the percent-decoder: 294412, of which 252015 it accepts
- Go: `net/url.PathUnescape`, go version go1.24.7 linux/amd64
- Texts in US-ASCII: 272971, differences: 0
- Texts with a character outside US-ASCII: 21441, of which this decoder accepts 0. Go reads such a character as its UTF-8 bytes, and gives the same answer on 5828 of them (where it finds a bad escape too) and a different one on 15613.

