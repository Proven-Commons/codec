#!/usr/bin/env python3
"""Differential tests: the Lean codecs against Python's own.

The oracles are Python's `binascii.hexlify` and `binascii.unhexlify`,
`base64.b64encode` and strict `binascii.a2b_base64`, `zlib.crc32`, and
for percent-encoding `urllib.parse.quote` with no safe characters and
`urllib.parse.unquote_to_bytes`; for PEM, `ssl.DER_cert_to_PEM_cert`
for the `CERTIFICATE` label, and for other labels an encoder and a strict
parser written here from the ABNF of RFC 7468, section 3, with the base
64 checked by strict `binascii.a2b_base64`. `unquote_to_bytes` passes a bad escape
through as text, where RFC 3986 has none, so text is first checked
against what `Spec.PctReads` accepts, as a regular expression, and only
text that matches is given to it; the rest must be refused. Inputs come from
a recorded seed:

- random byte strings, encoded, decoded, checksummed and framed;
- mutations of valid encodings and frames: a character replaced,
  inserted or deleted, the case flipped, padding moved, a code point
  moved out of ASCII, a bit flipped. A mutation that leaves the input
  unchanged is drawn again;
- malformed requests, which the tool must answer with `error`, and
  character codes at the edges of Unicode, which it must accept.

For every input the Lean answer must equal the oracle's, with two
expected differences, both because the Lean base 64 decoder is strict
and Python's strict mode is less so. Python decodes text whose unused
bits before the padding are not zero, and Python 3.11, and 3.12 before
3.12.4, also decode padding after a whole group, such as `Zm9v=`
(CPython issue gh-118314). Each such case is checked to be exactly one
of the two, by re-encoding what Python decoded, and counted. Any other
case where Python decodes text that does not re-encode to itself is
compared as usual, and fails.

    python3 tests/run_tests.py [--seed N] [--count N]

It builds the executable first, writes tests/TEST-RESULTS.md, and exits
non-zero if any input disagrees. It needs Python 3.11 or later.

The cases are made from the seed as they are sent, and made again from
the seed to check the answers as they come back. No case is kept, so
memory stays small however many inputs there are.
"""

import argparse
import base64
import binascii
import platform
import random
import re
import ssl
import subprocess
import sys
import threading
import urllib.parse
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "codec"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
# A million inputs take about a minute; a tool that has not finished in
# half an hour is reported as hung, and so is a build that takes an hour.
TIMEOUT = 1800
BUILD_TIMEOUT = 3600

PADDING_BITS = "unused bits before the padding not zero"
EXTRA_PADDING = "padding after a whole group, which Python 3.11 and 3.12 before 3.12.4 decode"


def nums(values):
    return ",".join(str(v) for v in values)


def text_nums(text):
    return nums(ord(c) for c in text)


def wrapped(text, bits):
    """The code points of `text`, each plus 2^bits: a parser that wraps
    at that width reads them as `text`."""
    return nums(2 ** bits + ord(c) for c in text)


def decoded(result):
    return "none" if result is None else "ok:" + nums(result)


# Requests the tool must answer with `error`, and why. Each check on a
# number is tried on a later number, where a parser that checks only
# the first would miss it.
MALFORMED = [
    ("frob 1", "unknown operation"),
    ("HEXENC 1", "operations are lowercase"),
    ("Hexdec 48,48", "operations are lowercase"),
    ("hexen 1", "unknown operation"),
    ("hexencx 1", "unknown operation"),
    ("", "an empty line"),
    ("\r", "an empty line ending CR LF"),
    ("   ", "only spaces"),
    (" hexenc 1", "a leading space"),
    ("hexenc 1 ", "a trailing space"),
    ("hexenc  1", "two spaces"),
    ("hexenc\t1", "a tab"),
    ("hexenc\x0b1", "a vertical tab"),
    ("hexenc\xa01", "a no-break space"),
    ("hexenc 1\t", "a trailing tab"),
    ("crc\x0b", "a trailing vertical tab"),
    ("hexenc 1\r\r", "two CRs before the LF"),
    ("\rhexenc 1", "a CR before the operation, as after an LF CR line end"),
    ("\ufeffhexenc 1", "a byte order mark"),
    ("hexenc 1\x0c", "a trailing form feed"),
    ("hexenc 1\x1e", "a trailing record separator"),
    ("hexenc 1\x85", "a trailing next line (U+0085)"),
    ("hexenc 1\u2028", "a trailing line separator (U+2028)"),
    ("crc\u2029", "a trailing paragraph separator (U+2029)"),
    ("hexenc 1\u2028hexenc 2", "a line separator between two requests"),
    ("hexenc 1\r2", "a CR inside the numbers"),
    ("hex\renc 1", "a CR inside the operation"),
    ("hexenc\r1", "a CR as the separator"),
    ("hexenc 1,\t2", "a tab before a number"),
    ("hexenc 1,2 ", "a space after the numbers"),
    ("hexenc 1 2", "two arguments"),
    ("crc 1,,2", "an empty number"),
    ("frame 1,", "an empty number"),
    ("crc ,", "only a comma"),
    ("hexenc ,1", "an empty first number"),
    ("crc  ", "two spaces and no numbers"),
    ("hexenc,1", "a comma as the separator"),
    ("b64enc 1,+1", "a sign"),
    ("hexenc +1", "a sign on the first number"),
    ("hexenc 1,-1", "a sign"),
    ("hexenc -0", "a sign on zero"),
    ("crc 1,-00", "a sign on zero"),
    ("hexenc 1,1_0", "an underscore"),
    ("hexenc 1,0x1", "a hex number"),
    ("hexenc 1,1e2", "an exponent"),
    ("hexenc 1,\u0661", "a digit that is not ASCII"),
    ("hexenc 1,\uff11", "a fullwidth digit, which NFKC folds to ASCII"),
    ("hexenc 1,\u2081", "a subscript digit, which NFKC folds to ASCII"),
    ("hexenc 256", "a byte above 255"),
    ("hexenc 0,511", "a byte above 255"),
    ("b64enc 1,256", "a byte above 255"),
    ("crc 1,256", "a byte above 255"),
    ("frame 0,256", "a byte above 255"),
    ("unframe 0,1,2,300", "a byte above 255"),
    ("hexenc 1,65536", "a byte of 2^16, which wraps to 0"),
    ("hexenc 1,4294967296", "a byte of 2^32, which wraps to 0"),
    ("crc 1,18446744073709551617", "a byte of 2^64 + 1, which wraps to 1"),
    ("hexdec 48,55296", "a surrogate, not a character"),
    ("b64dec 90,103,61,57343", "a surrogate, not a character"),
    ("hexdec 48,1114112", "beyond Unicode"),
    ("pctenc 37,256", "a byte above 255"),
    ("pctdec 37,55296", "a surrogate, not a character"),
    ("pemenc", "no arguments"),
    ("pemenc 88", "no `;` between the label and the data"),
    ("pemenc 88;1;2", "two `;`"),
    ("pemenc 88;256", "a byte above 255"),
    ("pemenc 55296;1", "a surrogate in the label"),
    ("pemdec 45,1114112", "beyond Unicode"),
    ("hexdec 48,2097201", "2^21 + 49, which wraps at 21 bits to a digit"),
    ("hexdec 55357,56385", "a UTF-16 surrogate pair, not a character"),
    ("b64dec 90,103,61,99999999999999999999", "beyond Unicode"),
    (f"hexdec {wrapped('01', 32)}", "code points that wrap at 2^32 to digits"),
    (f"b64dec {wrapped('Zm8=', 32)}", "code points that wrap at 2^32 to base 64"),
    (f"hexdec {wrapped('01', 64)}", "code points that wrap at 2^64 to digits"),
    (f"b64dec {wrapped('Zm8=', 64)}", "code points that wrap at 2^64 to base 64"),
    ("hexenc 1" + "0" * 100 + "1", "a number with a hundred digits"),
    ("crc 1,1" + "0" * 100 + "1", "a number with a hundred digits"),
]

# Valid characters at the edges of the ranges, or whose low bits are
# alphabet characters: decoding must reject them, not the tool.
EDGE_CHARS = ["\x00", "\x7f", "\x80", "\xff", "Ā", "İ", "Ł", "퟿", "",
              "￿", "\U00010000", "\U00010030", "\U0001005a", "\U0001f441", "\U0010ffff"]

# Well-formed requests in less usual forms: CR LF at the end, which is
# answered as without it, and leading zeros.
UNUSUAL = [
    ("hexenc", "hexenc 1,171\r", "01ab"),
    ("crc", "crc\r", "0"),
    ("hexenc", "hexenc 0,00255,0000000000000000000001", "00ff01"),
    ("hexdec", "hexdec 000048,0001114111", "none"),
    ("hexenc", "hexenc " + "0" * 1000 + "1", "01"),
    ("crc", "crc ", "0"),
]

# Last lines with no LF, each sent alone: a final line is read like any
# other, and a CR is ignored only before an LF.
AT_EOF = [("hexenc 1", "01"), ("hexenc 1\r", "error"), ("\r", "error"), (" ", "error"),
          ("hexenc 1\u2028", "error"), ("\ufeffhexenc 1", "error")]


def oracle_unhex(text):
    try:
        return binascii.unhexlify(text.encode("latin-1"))
    except (binascii.Error, ValueError, UnicodeEncodeError):
        return None


def oracle_b64decode(text):
    try:
        raw = text.encode("ascii")
    except UnicodeEncodeError:
        return None
    try:
        return binascii.a2b_base64(raw, strict_mode=True)
    except binascii.Error:
        return None


# What `Spec.PctReads` accepts, as a regular expression: each piece is `%`
# and two hex digits (the `pct-encoded` rule of RFC 3986, section 2.1),
# or a US-ASCII character other than `%`.
PCT_TEXT = re.compile(r"(?:%[0-9A-Fa-f]{2}|[\x00-\x24\x26-\x7f])*")


def oracle_pctenc(data):
    return urllib.parse.quote(data, safe="")


def oracle_pctdec(text):
    if not PCT_TEXT.fullmatch(text):
        return None
    return urllib.parse.unquote_to_bytes(text)


def lower_escapes(text):
    return re.sub(r"%[0-9A-F]{2}", lambda m: m.group().lower(), text)


PCT_POOL = "%%%0123456789abcdefABCDEFgG/+ ~.-_?#\x00\x7f\x80\xe9\u0100\U0001f441"


def mutate_pct(rng, text):
    """One random mutation of percent-encoded text."""
    kind = rng.randrange(5)
    i = rng.randrange(len(text) + 1)
    if kind == 0 and text:
        return text[:i % len(text)] + rng.choice(PCT_POOL) + text[i % len(text) + 1:]
    if kind == 1:
        return text[:i] + rng.choice(PCT_POOL) + text[i:]
    if kind == 2 and text:
        return text[:i % len(text)] + text[i % len(text) + 1:]
    if kind == 3:
        return text.swapcase()
    return text[:i] + "".join(rng.choice(PCT_POOL) for _ in range(rng.randrange(1, 4))) + text[i:]


# RFC 7468, section 3: `label`, `eol`, and the strict form (Figure 3).
PEM_LABEL = r"(?:[\x21-\x2c\x2e-\x7e](?:[- ]?[\x21-\x2c\x2e-\x7e])*)?"
PEM_EOL = r"(?:\r\n|\r|\n)"
PEM_TEXT = re.compile(r"-----BEGIN (" + PEM_LABEL + r")-----" + PEM_EOL +
                      r"((?:[A-Za-z0-9+/=]+" + PEM_EOL + r")*)" +
                      r"-----END \1-----" + PEM_EOL)
PEM_LABELS = ["CERTIFICATE", "X509 CRL", "CERTIFICATE REQUEST", "PKCS7", "CMS", "PRIVATE KEY",
              "ENCRYPTED PRIVATE KEY", "ATTRIBUTE CERTIFICATE", "PUBLIC KEY", "", "A", "a-b c",
              "!~", "X.509 CERTIFICATE", ",", "A,B", "A:B"]
BAD_PEM_LABELS = ["A--B", "A  B", "A -B", " A", "A ", "-A", "A-", "-", " ", "\xe9", "\x7f", "A\tB",
                  "A\nB", "A-----", "\u0130"]
PEM_POOL = "\r\n -=+/AZaz09-!~,:\t\xe9"


def oracle_pem_encode(label, data):
    if not re.fullmatch(PEM_LABEL, label):
        return None
    b64 = base64.b64encode(data).decode()
    lines = [b64[i:i + 64] for i in range(0, len(b64), 64)]
    return "".join(line + "\n" for line in
                   [f"-----BEGIN {label}-----"] + lines + [f"-----END {label}-----"])


def pem_encoded(label, data):
    """The expected `pemenc` answer: from Python's own `ssl` for
    certificates, else from the encoder above."""
    text = (ssl.DER_cert_to_PEM_cert(data) if label == "CERTIFICATE"
            else oracle_pem_encode(label, data))
    return "none" if text is None else "ok:" + text_nums(text)


def oracle_pem_decode(text):
    m = PEM_TEXT.fullmatch(text)
    if not m:
        return None
    label, body = m.group(1), m.group(2)
    lines = re.split(PEM_EOL, body)[:-1] if body else []
    if any(len(line) != 64 for line in lines[:-1]) or (lines and len(lines[-1]) > 64):
        return None
    b64 = "".join(lines)
    try:
        data = binascii.a2b_base64(b64.encode(), strict_mode=True)
    except binascii.Error:
        return None
    if base64.b64encode(data).decode() != b64:
        return None
    # Python's own reader, which is lax, must read an accepted certificate
    # the same way.
    if label == "CERTIFICATE" and ssl.PEM_cert_to_DER_cert(text) != data:
        raise AssertionError(f"ssl.PEM_cert_to_DER_cert disagrees on {text!r}")
    return label, data


def pem_decoded(text):
    result = oracle_pem_decode(text)
    return "none" if result is None else f"ok:{text_nums(result[0])};{nums(result[1])}"


def pem_eols(rng, text):
    """`text`, each LF replaced by a line end drawn from LF, CR and CR LF."""
    return "".join(rng.choice(["\n", "\r", "\r\n"]) if c == "\n" else c for c in text)


def mutate_pem(rng, text):
    """One random mutation of a PEM text."""
    kind = rng.randrange(8)
    i = rng.randrange(len(text) + 1)
    if kind == 0 and text:
        return text[:i % len(text)] + rng.choice(PEM_POOL) + text[i % len(text) + 1:]
    if kind == 1:
        return text[:i] + rng.choice(PEM_POOL) + text[i:]
    if kind == 2 and text:
        return text[:i % len(text)] + text[i % len(text) + 1:]
    if kind == 3:
        return rng.choice(["x\n", "\n", " "]) + text
    if kind == 4:
        return text + rng.choice(["x", "\n", " ", "x\n"])
    if kind == 5:
        return text.replace("-----END ", "-----END X", 1)
    if kind == 6:
        first = text.find("\n")
        return text[:first + 1] + "Proc-Type: 4,ENCRYPTED\n" + text[first + 1:]
    # Join two lines, or cut a line in two.
    nl = [k for k, c in enumerate(text) if c == "\n"]
    if len(nl) > 2 and rng.random() < 0.5:
        k = rng.choice(nl[1:-1])
        return text[:k] + text[k + 1:]
    return text[:i] + "\n" + text[i:]


def oracle_unframe(fr):
    if len(fr) < 4:
        return None
    msg, tail = fr[:-4], fr[-4:]
    return msg if tail == zlib.crc32(msg).to_bytes(4, "little") else None


def b64_difference(text, py):
    """Why Python decoded `text` to `py` though strict decoding rejects
    it: one of the two known differences, or None."""
    canon = base64.b64encode(py).decode()
    if canon == text:
        return None
    core, text_core = canon.rstrip("="), text.rstrip("=")
    if (len(canon) == len(text) and canon != core and len(core) == len(text_core)
            and core[:-1] == text_core[:-1]):
        return PADDING_BITS
    if canon == core and text.startswith(canon) and set(text[len(canon):]) == {"="}:
        return EXTRA_PADDING
    return None


POOL = "AZaz09+/=GgQw-_ .\n\xe9İŁ\U00010030\U0001f441"
B64_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


def mutate_text(rng, text):
    """One random mutation of an encoding."""
    kind = rng.randrange(7)
    i = rng.randrange(len(text) + 1)
    if kind == 0 and text:
        return text[:i % len(text)] + rng.choice(POOL) + text[i % len(text) + 1:]
    if kind == 1:
        return text[:i] + rng.choice(POOL) + text[i:]
    if kind == 2 and text:
        return text[:i % len(text)] + text[i % len(text) + 1:]
    if kind == 3:
        return text.swapcase()
    if kind == 4:
        return text.rstrip("=") + "=" * rng.randrange(4)
    if kind == 5 and text:
        # Move one code point out of ASCII, keeping its low bits.
        j = i % len(text)
        return text[:j] + chr(ord(text[j]) + rng.choice([0x100, 0x10000, 0x100000])) + text[j + 1:]
    # Change the last character before the padding: often only its
    # unused bits, which strict decoding must reject.
    core = text.rstrip("=")
    if core:
        return core[:-1] + rng.choice(B64_ALPHABET) + text[len(core):]
    return text


def mutate_bytes(rng, data):
    if not data:
        return bytes([rng.randrange(256)])
    out = bytearray(data)
    kind = rng.randrange(3)
    i = rng.randrange(len(out))
    if kind == 0:
        out[i] ^= 1 << rng.randrange(8)
    elif kind == 1:
        del out[i]
    else:
        out.insert(i, rng.randrange(256))
    return bytes(out)


def changed(mutate, rng, value):
    """A mutation of `value` that differs from it."""
    while True:
        out = mutate(rng, value)
        if out != value:
            return out


def fixed_cases():
    items = [("error", req, "error", why, False) for req, why in MALFORMED]
    for c in EDGE_CHARS:
        items.append(("hexdec", f"hexdec {text_nums(c * 2)}", decoded(oracle_unhex(c * 2)),
                      None, False))
        items.append(("b64dec", f"b64dec {text_nums(c * 4)}", decoded(oracle_b64decode(c * 4)),
                      None, False))
        for text in (c, "%4" + c, "%" + c + "1", "a" + c + "%41"):
            items.append(("pctdec", f"pctdec {text_nums(text)}", decoded(oracle_pctdec(text)),
                          None, False))
    # Every byte alone, and every one-character text: the whole of the
    # encoder's and the decoder's per-character rules.
    for b in range(256):
        items.append(("pctenc", f"pctenc {b}", oracle_pctenc(bytes([b])), None, False))
    # PEM: every label above with data at the line edges (48 bytes are
    # one full line), and every bad label.
    for label in PEM_LABELS + BAD_PEM_LABELS:
        for n in (0, 1, 2, 3, 47, 48, 49, 95, 96, 97):
            data = bytes((7 * k + n) % 256 for k in range(n))
            items.append(("pemenc", f"pemenc {text_nums(label)};{nums(data)}",
                          pem_encoded(label, data), None, False))
            text = oracle_pem_encode(label, data) or f"-----BEGIN {label}-----\n-----END {label}-----\n"
            items.append(("pemdec", f"pemdec {text_nums(text)}", pem_decoded(text), None, False))
    for c in range(128):
        text = chr(c)
        items.append(("pctdec", f"pctdec {text_nums(text)}", decoded(oracle_pctdec(text)), None, False))
    for hi in range(128):
        for lo in "0aF":
            text = "%" + chr(hi) + lo
            items.append(("pctdec", f"pctdec {text_nums(text)}", decoded(oracle_pctdec(text)),
                          None, False))
    items += [(label, req, want, None, False) for label, req, want in UNUSUAL]
    return items


def cases(seed, count):
    """(label, request, expected answer, note, mutated) for each input."""
    rng = random.Random(seed)
    fixed = fixed_cases()[:count]
    yield from fixed
    made = len(fixed)
    while made < count:
        n = rng.choice([0, 1, 2, 3, 4, 5, rng.randrange(64), rng.randrange(1024)])
        data = rng.randbytes(n)
        hex_text = binascii.hexlify(data).decode()
        b64_text = base64.b64encode(data).decode()
        frame = data + zlib.crc32(data).to_bytes(4, "little")
        batch = [
            ("hexenc", f"hexenc {nums(data)}", hex_text, None, False),
            ("hexdec", f"hexdec {text_nums(hex_text)}", decoded(data), None, False),
            ("hexdec", f"hexdec {text_nums(hex_text.upper())}", decoded(data), None, False),
            ("b64enc", f"b64enc {nums(data)}", b64_text, None, False),
            ("b64dec", f"b64dec {text_nums(b64_text)}", decoded(data), None, False),
            ("crc", f"crc {nums(data)}", str(zlib.crc32(data)), None, False),
            ("frame", f"frame {nums(data)}", nums(frame), None, False),
            ("unframe", f"unframe {nums(frame)}", decoded(data), None, False),
        ]
        bad_hex = changed(mutate_text, rng, hex_text)
        batch.append(("hexdec", f"hexdec {text_nums(bad_hex)}", decoded(oracle_unhex(bad_hex)), None, True))
        bad_b64 = changed(mutate_text, rng, b64_text)
        py = oracle_b64decode(bad_b64)
        why = None if py is None else b64_difference(bad_b64, py)
        want = "none" if why else decoded(py)
        batch.append(("b64dec", f"b64dec {text_nums(bad_b64)}", want, why, True))
        bad_frame = changed(mutate_bytes, rng, frame)
        batch.append(("unframe", f"unframe {nums(bad_frame)}", decoded(oracle_unframe(bad_frame)), None, True))
        pct_text = oracle_pctenc(data)
        batch += [
            ("pctenc", f"pctenc {nums(data)}", pct_text, None, False),
            ("pctdec", f"pctdec {text_nums(pct_text)}", decoded(data), None, False),
            ("pctdec", f"pctdec {text_nums(lower_escapes(pct_text))}", decoded(data), None, False),
            # Encoded twice, it decodes once: to the first encoding.
            ("pctdec", f"pctdec {text_nums(oracle_pctenc(pct_text.encode()))}",
             decoded(pct_text.encode()), None, False),
        ]
        bad_pct = changed(mutate_pct, rng, pct_text)
        batch.append(("pctdec", f"pctdec {text_nums(bad_pct)}", decoded(oracle_pctdec(bad_pct)), None, True))
        raw = "".join(rng.choice(PCT_POOL) for _ in range(rng.randrange(8)))
        batch.append(("pctdec", f"pctdec {text_nums(raw)}", decoded(oracle_pctdec(raw)), None, False))
        label = rng.choice(PEM_LABELS + BAD_PEM_LABELS[:3])
        pem_data = data[: rng.choice([0, 1, 47, 48, 49, 96, 97, 200, len(data)])]
        batch.append(("pemenc", f"pemenc {text_nums(label)};{nums(pem_data)}",
                      pem_encoded(label, pem_data), None, False))
        pem_text = oracle_pem_encode(label, pem_data)
        if pem_text is not None:
            ends = pem_eols(rng, pem_text)
            batch.append(("pemdec", f"pemdec {text_nums(ends)}", pem_decoded(ends), None, False))
            bad_pem = changed(mutate_pem, rng, ends)
            batch.append(("pemdec", f"pemdec {text_nums(bad_pem)}", pem_decoded(bad_pem), None, True))
        batch = batch[: count - made]
        yield from batch
        made += len(batch)


def run_tool(chunks, answer, timeout=TIMEOUT):
    """Send the text in `chunks` to the tool as it is made, and pass each
    line the tool prints to `answer` as it comes. Return a note on how
    the run failed, or None. Lines end in LF only; the output is read as
    bytes, so a CR left in a line fails the comparison. No right answer
    is longer than one and a half times its request plus 16 bytes
    (`pctenc` writes three characters for a byte the request can give in
    two, such as "0,"), so a tool that writes more than twice what it
    was sent and 64 bytes a line is stopped, not read until memory runs
    out."""
    try:
        proc = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    except OSError as e:
        return f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
    sent = {"bytes": 0, "lines": 0}
    over, no_lf, err, crashed = [], [], bytearray(), []

    def feed():
        try:
            parts, size, lines = [], 0, 0
            for chunk in chunks:
                raw = chunk.encode("utf-8")
                parts.append(raw)
                size += len(raw)
                lines += chunk.count("\n")
                if size >= 1 << 16:
                    # Counted before it is written, so the limit is never short.
                    sent["bytes"] += size
                    sent["lines"] += lines
                    proc.stdin.write(b"".join(parts))
                    parts, size, lines = [], 0, 0
            sent["bytes"] += size
            sent["lines"] += lines
            proc.stdin.write(b"".join(parts))
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass
        except BaseException as e:
            crashed.append(e)
            proc.kill()

    def drain_out():
        line, read = bytearray(), 0
        try:
            while chunk := proc.stdout.read1(1 << 16):
                read += len(chunk)
                limit = 2 * sent["bytes"] + 64 * (sent["lines"] + 1)
                start = 0
                while (end := chunk.find(b"\n", start)) >= 0:
                    line += chunk[start:end]
                    answer(line.decode("utf-8", "backslashreplace"))
                    line.clear()
                    start = end + 1
                line += chunk[start:]
                if read > limit:
                    over.append(limit)
                    proc.kill()
                    return
            if line:
                no_lf.append(True)
                answer(line.decode("utf-8", "backslashreplace"))
        except BaseException as e:
            crashed.append(e)
            proc.kill()

    def drain_err():
        while chunk := proc.stderr.read1(1 << 16):
            err.extend(chunk)
            if len(err) > 1 << 20:
                proc.kill()
                return

    threads = [threading.Thread(target=feed), threading.Thread(target=drain_out),
               threading.Thread(target=drain_err)]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if crashed:
        raise crashed[0]
    if over:
        problem = problem or f"more than {over[0]} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    if no_lf:
        problem = problem or "the last answer has no LF"
    return problem


def oracle():
    return (f"Python {platform.python_version()} `binascii`, `base64`, `zlib` "
            f"(zlib {zlib.ZLIB_RUNTIME_VERSION}), `urllib.parse`; for PEM, a strict encoder and "
            "parser written in tests/run_tests.py from RFC 7468, with `ssl.DER_cert_to_PEM_cert` "
            "and `ssl.PEM_cert_to_DER_cert` for the `CERTIFICATE` label")


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261024)
    ap.add_argument("--count", type=count, default=1_000_000)
    args = ap.parse_args()
    if sys.version_info < (3, 11):
        sys.exit("needs Python 3.11 or later, for binascii.a2b_base64(strict_mode=True)")

    # Always build, so the tests never run an executable older than the code.
    try:
        build = subprocess.run(["lake", "build", "codec"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        built, log = build.returncode == 0, build.stdout + build.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        built, log = False, str(e)
    if not built:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0", "- Failures: 1 (`lake build codec` failed)", ""])
        sys.exit("lake build codec failed:\n" + log)

    # The answers are checked against a second run of the same cases as
    # they come, so neither the cases nor the answers are kept.
    expected = cases(args.seed, args.count)
    by_op = {}
    n = {"inputs": 0, "mutated": 0, PADDING_BITS: 0, EXTRA_PADDING: 0, "malformed": 0,
         "agree": 0, "failed": 0}
    failures = []  # the first 50, in order

    def fail(req, want, got):
        n["failed"] += 1
        if len(failures) < 50:
            failures.append((req, want, got))

    def tally(item):
        label, _, _, note, mutated = item
        n["inputs"] += 1
        by_op[label] = by_op.get(label, 0) + 1
        n["mutated"] += mutated
        if note in (PADDING_BITS, EXTRA_PADDING):
            n[note] += 1

    def check(got):
        item = next(expected, None)
        if item is None:
            fail("(no request)", "nothing", got)
            return
        tally(item)
        if item[0] == "error" and got == "error":
            n["malformed"] += 1
        if got == item[2]:
            n["agree"] += 1
        else:
            fail(item[1], item[2], got)

    problem = run_tool((req + "\n" for _, req, _, _, _ in cases(args.seed, args.count)), check)
    for item in expected:
        tally(item)
        fail(item[1], item[2], "(no answer)")
    # How the whole run failed goes first, where the record shows it.
    if problem:
        failures.insert(0, ("(whole run)", "a clean run", problem))
        n["failed"] += 1
    eof_right = 0
    for req, want in AT_EOF:
        got = []
        eof_problem = run_tool([req], got.append, timeout=60)
        if got == [want] and not eof_problem:
            eof_right += 1
        else:
            fail(req + " (at end of input)", want, f"{got} {eof_problem or ''}".strip())
    pad_bits, extra_pad = n[PADDING_BITS], n[EXTRA_PADDING]

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {n['inputs']}",
        f"- Mutated: {n['mutated']} of the inputs are mutated encodings or frames",
        f"- By operation: " + ", ".join(f"{k} {v}" for k, v in sorted(by_op.items())),
        f"- Malformed requests answered `error`: {n['malformed']} of {by_op.get('error', 0)}",
        f"- Last lines with no LF, sent alone, answered right: {eof_right} of {len(AT_EOF)}",
        f"- Strict base 64 rejections where Python decodes: {pad_bits + extra_pad} "
        f"({pad_bits} with {PADDING_BITS}, {extra_pad} with {EXTRA_PADDING})",
        f"- Failures: {n['failed']}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:120]!r}`: expected `{want[:80]!r}`, Lean printed `{got[:80]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    print(f"{n['agree']}/{n['inputs']} inputs agree, {n['failed']} failures; results in {RESULTS}")
    return 1 if n["failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
