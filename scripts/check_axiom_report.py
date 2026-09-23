#!/usr/bin/env python3
"""Fail if the Lean axiom report omits a declaration or adds a nonstandard axiom.

Usage: lake env lean DGBOZK/Audit.lean | python3 scripts/check_axiom_report.py DGBOZK/Audit.lean
"""

from collections import Counter
from pathlib import Path
import re
import sys


ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
REQUESTED = re.compile(r"(?m)^#print axioms\s+(\S+)\s*$")
REPORTED = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
    r"|does not depend on any axioms)"
)


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: check_axiom_report.py DGBOZK/Audit.lean", file=sys.stderr)
        return 2

    source = Path(sys.argv[1]).read_text(encoding="utf-8")
    report = sys.stdin.read()
    requested = Counter(REQUESTED.findall(source))
    matches = REPORTED.findall(report)
    actual = Counter(name for name, _ in matches)
    failures: list[str] = []

    if not requested:
        failures.append("no #print axioms declarations found in the audit source")
    if missing := requested - actual:
        failures.append(f"missing reports: {dict(missing)}")
    if extra := actual - requested:
        failures.append(f"unexpected reports: {dict(extra)}")

    for name, raw_axioms in matches:
        axioms = {item.strip() for item in raw_axioms.split(",") if item.strip()}
        if unexpected := axioms - ALLOWED:
            failures.append(f"{name}: disallowed axiom(s): {sorted(unexpected)}")

    if failures:
        print("FAIL: Lean axiom audit", file=sys.stderr)
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"PASS: {sum(requested.values())} Lean axiom reports use only the standard allowlist")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
