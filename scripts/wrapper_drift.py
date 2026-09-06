#!/usr/bin/env python3
"""Drift check for the deliberately duplicated nominal byte wrappers.

`H160`, `H256`, `Bytes32`, and `Address` repeat one API by hand. Every declaration name that two or
more wrappers share must keep an identical statement once the type name and its width are
normalised, so an edit to one wrapper cannot silently diverge from the others.
"""

import re
import sys
from pathlib import Path

WRAPPERS = ["H160", "H256", "Bytes32", "Address"]
# Same name, intentionally different statement: `Address.ofU256` truncates to 160 bits, whereas
# `H256.ofU256` and `Bytes32.ofU256` reinterpret the whole word.
EXPECTED_DIFFERENCES = {"toNat_ofU256"}
DIR = Path(__file__).resolve().parent.parent / "Lean4EVM" / "Primitives" / "FixedBytes"


def normalise(text, name):
    text = re.sub(rf"\b{name}\b", "T", text)
    text = re.sub(r"\b(160|256)\b", "W", text)
    text = re.sub(r"\b(20|32)\b", "N", text)
    return " ".join(text.split())


def statements(name):
    """Map each declaration to its normalised statement, i.e. everything before its `:=` or `where`."""
    result = {}
    for block in (DIR / f"{name}.lean").read_text().split("\n\n"):
        lines = [l for l in block.splitlines() if not l.lstrip().startswith("/--")]
        match = re.match(r"(?:@\[[^\]]*\]\s*)?(theorem|def|instance)\s+(\S+)", "\n".join(lines))
        if not match:
            continue
        head = re.split(r"\s:=|\swhere\b", "\n".join(lines), maxsplit=1)[0]
        key = match.group(2) if match.group(1) != "instance" else normalise(head, name)
        result[key] = normalise(head, name)
    return result


def main():
    tables = {name: statements(name) for name in WRAPPERS}
    shared = {key for a in WRAPPERS for b in WRAPPERS if a != b
              for key in tables[a].keys() & tables[b].keys()}
    drift = 0
    for key in sorted(shared - EXPECTED_DIFFERENCES):
        forms = {tables[name][key] for name in WRAPPERS if key in tables[name]}
        if len(forms) > 1:
            drift += 1
            print(f"DRIFT {key}:")
            for form in sorted(forms):
                print(f"  {form}")
    print(f"wrapper drift: {len(shared)} shared declarations, {drift} divergent, "
          f"{len(EXPECTED_DIFFERENCES)} documented exceptions")
    sys.exit(1 if drift else 0)


if __name__ == "__main__":
    main()
