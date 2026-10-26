#!/usr/bin/env python3
"""A one-off comparison of the percent-decoder and of PEM with Go's, and
of the check digits with python-stdnum.

Unlike tests/run_tests.py, this is not part of the verified bar and is
not run in CI. It needs Go:

    python3 tests/cross_check.py [--seed N] [--count N]

The texts are the ones tests/run_tests.py gives the percent-decoder,
from the same seed. Each goes to this project's tool and to Go's
`net/url.PathUnescape`. Go reads a character outside US-ASCII as its
UTF-8 bytes, where this decoder refuses it, so texts with such a
character are counted on their own. On every other text the two must
agree.

Then each PEM request tests/run_tests.py makes goes to Go's
`encoding/pem`: `pemenc` to `pem.EncodeToMemory`, and `pemdec` to
`pem.Decode`. Go writes any label, where this encoder refuses one the
RFC's `label` rule does not allow, and Go reads PEM laxly, skipping text
around a block and taking headers and blanks. So each difference is
sorted by kind, and only text this decoder accepts and Go reads
differently, or not at all, counts against it. The counts go to
tests/CROSS-CHECK.md.

Last, each Luhn and IBAN request goes to python-stdnum 2.2, installed
into .lake/oracle-packages if it is not there: `luhn.is_valid` and
`luhn.calc_check_digit`, `iban.calc_check_digits`, and for the IBAN
check `iso7064.mod_97_10.is_valid` on the rearranged text, with the
shape checked as this codec does. Then each IBAN goes to `iban.validate`
too, which also checks each country's BBAN format in the SWIFT
registry, as this codec does not: those refusals are counted on their
own, as are the IBANs stdnum reads after removing spaces and dashes and
upper-casing, and the empty Luhn number, which stdnum refuses.
(stdnum removes spaces, dashes and dots.)
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_tests  # noqa: E402

ROOT = run_tests.ROOT
REPORT = ROOT / "tests" / "CROSS-CHECK.md"
HELPERS = ROOT / "tests" / "cross_check"
BUILD = ROOT / ".lake" / "cross_check"


def stdnum():
    """python-stdnum 2.2, from .lake/oracle-packages, installed there if
    needed."""
    target = ROOT / ".lake" / "oracle-packages"
    sys.path.insert(0, str(target))
    try:
        import stdnum as module
    except ImportError:
        subprocess.run([sys.executable, "-m", "pip", "install", "--quiet", "--target", str(target),
                        "python-stdnum==2.2"], check=True)
        import stdnum as module
    if module.__version__ != "2.2":
        sys.exit(f"python-stdnum {module.__version__} found, 2.2 wanted")
    return module


def check_digit_section(args):
    stdnum()
    from stdnum import iban, luhn
    from stdnum.iso7064 import mod_97_10
    items = [(label, req) for label, req, _, _, _ in run_tests.cases(args.seed, args.count)
             if label in ("luhn", "luhncheck", "iban", "ibancheck")]
    ours, problem = run_tests.run_tool("".join(req + "\n" for _, req in items))
    if problem or len(ours) != len(items):
        sys.exit(f"the tool failed: {problem}")

    def theirs(label, req):
        arg = req.split(" ", 1)[1] if " " in req else ""
        if label == "luhn":
            return str(luhn.is_valid("".join(str(int(n)) for n in arg.split(",") if n))).lower()
        if label == "luhncheck":
            return luhn.calc_check_digit("".join(str(int(n)) for n in arg.split(",") if n))
        if label == "iban":
            text = "".join(map(chr, run_tests_nums(req)))
            return str(bool(run_tests.IBAN_SHAPE.fullmatch(text))
                       and mod_97_10.is_valid(text[4:] + text[:4])).lower()
        country, bban = (bytes(int(n) for n in part.split(",") if n).decode() for part in arg.split(";"))
        try:
            return "ok:" + run_tests.text_nums(iban.calc_check_digits(country + "00" + bban))
        except Exception:
            return "none"

    counts = {"same": 0, "empty": 0, "normalized": 0, "other": []}
    for (label, req), o in zip(items, ours):
        t = theirs(label, req)
        arg = req.split(" ", 1)[1] if " " in req else ""
        if o == t:
            counts["same"] += 1
        elif label == "luhn" and arg == "":
            counts["empty"] += 1
        elif label in ("iban", "ibancheck") and any(chr(n) in " -." or 97 <= n <= 122
                                                    for n in run_tests_nums(req.replace(";", ","))):
            counts["normalized"] += 1
        else:
            counts["other"].append((req, o, t))
    # The whole of stdnum's IBAN check, with the SWIFT registry.
    full = {"same": 0, "registry": 0, "normalized": 0, "other": []}
    for (label, req), o in zip(items, ours):
        if label != "iban":
            continue
        text = "".join(map(chr, run_tests_nums(req)))
        try:
            iban.validate(text)
            t, why = "true", None
        except Exception as e:
            t, why = "false", type(e).__name__
        if o == t:
            full["same"] += 1
        elif o == "true" and why in ("InvalidComponent", "InvalidFormat", "InvalidLength"):
            full["registry"] += 1
        elif any(c in " -." or c.islower() for c in text):
            full["normalized"] += 1
        else:
            full["other"].append((req, o, t))
    lines = [
        "",
        "## Luhn and IBAN",
        "",
        "- python-stdnum 2.2: `luhn.is_valid`, `luhn.calc_check_digit`, "
        "`iban.calc_check_digits`, and `iso7064.mod_97_10.is_valid` for the IBAN check",
        f"- Requests: {len(items)}. The same answer: {counts['same']}. An empty Luhn number, "
        f"which this codec passes and stdnum refuses: {counts['empty']}. IBAN text with a space, "
        f"a dash, a dot or a lower-case letter, which stdnum removes or upper-cases first and this codec "
        f"refuses: {counts['normalized']}. Other differences: {len(counts['other'])}.",
        f"- The same IBANs given to stdnum's whole `iban.validate`: the same answer on "
        f"{full['same']}. It refuses, for a country code or BBAN format not in the SWIFT registry, "
        f"{full['registry']} that pass this codec's check, which does not use the registry. Read "
        f"after stdnum's normalizing: {full['normalized']}. Other differences: {len(full['other'])}.",
        "",
    ]
    lines += [f"- `{r[:100]}`: this project `{o}`, stdnum `{t}`"
              for r, o, t in (counts["other"] + full["other"])[:10]]
    return lines


def run_tests_nums(req):
    arg = req.split(" ", 1)[1] if " " in req else ""
    return [int(n) for n in arg.split(",") if n]


def pem_section(args, version):
    items = [(label, req, want) for label, req, want, _, _ in run_tests.cases(args.seed, args.count)
             if label in ("pemenc", "pemdec")]
    ours, problem = run_tests.run_tool("".join(req + "\n" for _, req, _ in items))
    if problem or len(ours) != len(items):
        sys.exit(f"the tool failed: {problem}")
    subprocess.run(["go", "build", "-o", str(BUILD / "go-pem"), "pem.go"], cwd=HELPERS,
                   check=True, env={**os.environ, "GO111MODULE": "off"})
    go_reqs = [("enc " if label == "pemenc" else "dec ") + req.split(" ", 1)[1]
               for label, req, _ in items]
    go = subprocess.run([str(BUILD / "go-pem")], input="".join(r + "\n" for r in go_reqs),
                        capture_output=True, text=True, check=True).stdout.splitlines()
    if len(go) != len(items):
        sys.exit(f"Go gave {len(go)} answers for {len(items)} PEM requests")
    enc = {"same": 0, "Go writes a label this encoder refuses": 0, "other": []}
    dec = {"same": 0, "Go reads text this decoder refuses": 0, "lone CR": 0, "colon": 0, "other": []}
    for (label, req, _), o, g in zip(items, ours, go):
        if label == "pemenc":
            if o == g:
                enc["same"] += 1
            elif o == "none" and g.startswith("ok:"):
                enc["Go writes a label this encoder refuses"] += 1
            else:
                enc["other"].append((req, o, g))
        else:
            # Go's answer with nothing left over is the same block.
            g_same = g.startswith("ok:") and g.rsplit(";", 1)[1] == "0" and o == g.rsplit(";", 1)[0]
            if g_same or (o == "none" and g == "none"):
                dec["same"] += 1
            elif o == "none":
                dec["Go reads text this decoder refuses"] += 1
            elif o.endswith(";") and ":" in "".join(map(chr, run_tests_nums(req))).split("\n")[0] \
                    and g == "none":
                # Empty data under a label with `:`: Go takes the END line
                # for an RFC 1421 header.
                dec["colon"] += 1
            elif re.search("\r(?!\n)", "".join(map(chr, run_tests_nums(req)))):
                # RFC 7468 allows CR alone as a line end; Go splits lines
                # at LF only.
                dec["lone CR"] += 1
            else:
                dec["other"].append((req, o, g))
    lines = [
        "",
        "## PEM",
        "",
        f"- Go: `encoding/pem`, {version}",
        f"- Encoding requests: {sum(1 for l, _, _ in items if l == 'pemenc')}. The same text from both: "
        f"{enc['same']}. Go writes a label this encoder refuses: "
        f"{enc['Go writes a label this encoder refuses']}. Other differences: {len(enc['other'])}.",
        f"- Decoding requests: {sum(1 for l, _, _ in items if l == 'pemdec')}. The same answer from "
        f"both, with nothing left over in Go: {dec['same']}. Go reads text this decoder refuses: "
        f"{dec['Go reads text this decoder refuses']}. This decoder accepts text with a CR "
        f"alone as a line end, as RFC 7468's `eol` allows, and Go does not, since it ends lines "
        f"at LF only: {dec['lone CR']}. This decoder reads empty data under a label with a `:`, "
        f"and Go takes the END line for a header: {dec['colon']}. Other differences, where this "
        f"decoder accepts text that "
        f"Go reads differently or not at all: {len(dec['other'])}.",
        "",
    ]
    lines += [f"- `{r[:100]}`: this project `{o[:60]}`, Go `{g[:60]}`"
              for r, o, g in (enc["other"] + dec["other"])[:10]]
    return lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261024)
    ap.add_argument("--count", type=int, default=1_000_000)
    args = ap.parse_args()
    build = subprocess.run(["lake", "build", "codec"], cwd=ROOT, capture_output=True,
                           text=True, errors="backslashreplace")
    if build.returncode != 0:
        sys.exit("lake build codec failed:\n" + build.stdout + build.stderr)
    reqs = [req for label, req, _, _, _ in run_tests.cases(args.seed, args.count)
            if label == "pctdec"]
    ours, problem = run_tests.run_tool("".join(r + "\n" for r in reqs))
    if problem or len(ours) != len(reqs):
        sys.exit(f"the tool failed: {problem}")
    BUILD.mkdir(parents=True, exist_ok=True)
    subprocess.run(["go", "build", "-o", str(BUILD / "go-percent"), "percent.go"], cwd=HELPERS,
                   check=True, env={**os.environ, "GO111MODULE": "off"})
    args_text = [r.split(" ", 1)[1] if " " in r else "" for r in reqs]
    go = subprocess.run([str(BUILD / "go-percent")], input="".join(a + "\n" for a in args_text),
                        capture_output=True, text=True, check=True).stdout.splitlines()
    if len(go) != len(reqs):
        sys.exit(f"Go gave {len(go)} answers for {len(reqs)} texts")
    version = subprocess.run(["go", "version"], capture_output=True, text=True).stdout.strip()

    def non_ascii(a):
        return any(int(n) >= 0x80 for n in a.split(",") if n)

    ascii_diffs, other = [], {"same": 0, "differ": 0}
    accepted_non_ascii = 0
    for a, o, g in zip(args_text, ours, go):
        if non_ascii(a):
            other["same" if o == g else "differ"] += 1
            accepted_non_ascii += o.startswith("ok")
        elif o != g:
            ascii_diffs.append((a, o, g))
    lines = [
        "# Cross-check with Go",
        "",
        "Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.",
        "",
        f"- Seed: {args.seed}",
        f"- Texts given to the percent-decoder: {len(reqs)}, of which "
        f"{sum(o.startswith('ok') for o in ours)} it accepts",
        f"- Go: `net/url.PathUnescape`, {version}",
        f"- Texts in US-ASCII: {len(reqs) - sum(other.values())}, differences: {len(ascii_diffs)}",
        f"- Texts with a character outside US-ASCII: {sum(other.values())}, of which this decoder "
        f"accepts {accepted_non_ascii}. Go reads such a character as its UTF-8 bytes, and gives "
        f"the same answer on "
        f"{other['same']} of them (where it finds a bad escape too) and a different one on "
        f"{other['differ']}.",
        "",
    ]
    lines += [f"- `{a}`: this project `{o}`, Go `{g}`" for a, o, g in ascii_diffs[:10]]
    lines += pem_section(args, version)
    lines += check_digit_section(args)
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(reqs)} texts; report in {REPORT}")


if __name__ == "__main__":
    main()
