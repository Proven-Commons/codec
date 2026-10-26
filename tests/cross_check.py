#!/usr/bin/env python3
"""A one-off comparison of the percent-decoder with Go's.

Unlike tests/run_tests.py, this is not part of the verified bar and is
not run in CI. It needs Go:

    python3 tests/cross_check.py [--seed N] [--count N]

The texts are the ones tests/run_tests.py gives the percent-decoder,
from the same seed. Each goes to this project's tool and to Go's
`net/url.PathUnescape`. Go reads a character outside US-ASCII as its
UTF-8 bytes, where this decoder refuses it, so texts with such a
character are counted on their own. On every other text the two must
agree. The counts go to tests/CROSS-CHECK.md.
"""

import argparse
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_tests  # noqa: E402

ROOT = run_tests.ROOT
REPORT = ROOT / "tests" / "CROSS-CHECK.md"
HELPERS = ROOT / "tests" / "cross_check"
BUILD = ROOT / ".lake" / "cross_check"


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
    ours = []
    problem = run_tests.run_tool((r + "\n" for r in reqs), ours.append)
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
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(reqs)} texts; report in {REPORT}")


if __name__ == "__main__":
    main()
