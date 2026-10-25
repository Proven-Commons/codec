#!/usr/bin/env python3
"""Differential tests: the Lean codecs against Python's own.

The oracles are Python's `binascii.hexlify` and `binascii.unhexlify`,
`base64.b64encode` and strict `binascii.a2b_base64`, and `zlib.crc32`.
Inputs come from a recorded seed:

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
"""

import argparse
import base64
import binascii
import itertools
import platform
import random
import subprocess
import sys
import threading
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
        batch = batch[: count - made]
        yield from batch
        made += len(batch)


def run_tool(data, timeout=TIMEOUT):
    """The tool's answer lines for `data`, and a note on how the run
    failed, or None. Lines end in LF only; the output is read as bytes,
    so a CR left in a line fails the comparison. No right answer is
    longer than its request plus 16 bytes, so a tool that writes more
    than twice its input and 64 bytes a line is stopped, not read until
    memory runs out."""
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (data.count("\n") + 1)
    try:
        proc = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    except OSError as e:
        return [], f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out, limit)),
               threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20))]
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
    stdout = bytes(out)
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = stdout.decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines, problem


def oracle():
    return (f"Python {platform.python_version()} `binascii`, `base64`, `zlib` "
            f"(zlib {zlib.ZLIB_RUNTIME_VERSION})")


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

    items = list(cases(args.seed, args.count))
    out, problem = run_tool("".join(req + "\n" for _, req, _, _, _ in items))
    # How the whole run failed goes first, where the record shows it.
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_tool(req, timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))
    by_op = {}
    for label, _, _, _, _ in items:
        by_op[label] = by_op.get(label, 0) + 1
    mutated = sum(1 for item in items if item[4])
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]
    pad_bits = sum(1 for item in items if item[3] == PADDING_BITS)
    extra_pad = sum(1 for item in items if item[3] == EXTRA_PADDING)

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        f"- Mutated: {mutated} of the inputs are mutated encodings or frames",
        f"- By operation: " + ", ".join(f"{k} {v}" for k, v in sorted(by_op.items())),
        f"- Malformed requests answered `error`: {malformed.count('error')} of {by_op.get('error', 0)}",
        f"- Last lines with no LF, sent alone, answered right: {eof_right} of {len(AT_EOF)}",
        f"- Strict base 64 rejections where Python decodes: {pad_bits + extra_pad} "
        f"({pad_bits} with {PADDING_BITS}, {extra_pad} with {EXTRA_PADDING})",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:120]!r}`: expected `{want[:80]!r}`, Lean printed `{got[:80]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    agree = sum(1 for item, got in zip(items, out) if got == item[2])
    print(f"{agree}/{len(items)} inputs agree, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
