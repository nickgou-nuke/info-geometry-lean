#!/usr/bin/env python3
"""Check the new connection's source inventory, pinned package, and axiom log."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / "verification/peirce-defect-boundaries"
OWNER = "InfoGeometry.OperatorAlgebra.PeirceDerivationConnection"
AUDIT = ROOT / "lean/InfoGeometry/OperatorAlgebra/PeirceDerivationConnectionAudit.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log", type=Path, help="complete output from the Lean audit file")
    args = parser.parse_args()

    if (PACKAGE / "lean-toolchain").read_bytes() != (ROOT / "lean-toolchain").read_bytes():
        raise SystemExit("Root and focused Lean toolchains differ")

    def pins(directory: Path) -> dict[str, tuple]:
        manifest = json.loads((directory / "lake-manifest.json").read_text())
        return {
            package["name"]: tuple(package.get(key) for key in ("type", "url", "rev", "subDir"))
            for package in manifest["packages"] if package["type"] == "git"
        }

    root_pins, focused_pins = pins(ROOT), pins(PACKAGE)
    if "mathlib" not in focused_pins:
        raise SystemExit("Focused package has no Mathlib pin")
    mismatches = [name for name, pin in focused_pins.items() if root_pins.get(name) != pin]
    if mismatches:
        raise SystemExit(f"Focused Git dependency pins differ from root: {mismatches}")

    # Reuse the maintained nested-comment parser and public-declaration reader.
    helpers = runpy.run_path(str(PACKAGE / "audit.py"))
    expected = helpers["owner_declarations"](OWNER)
    source = helpers["strip_comments"](AUDIT.read_text())
    listed = re.findall(r"^#print axioms (\S+)\s*$", source, re.MULTILINE)
    if listed != expected:
        raise SystemExit(f"Audit coverage mismatch: expected {expected}, found {listed}")
    print(f"All {len(focused_pins)} focused Git pins match root; "
          f"source coverage: {len(expected)} public declarations")

    if args.log:
        log = args.log.read_text()
        if re.search(r"(?m)^.*\berror:", log):
            raise SystemExit("Lean reported an error in the axiom log")
        records = re.findall(
            r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
            log,
        )
        reported = [name for name, _ in records]
        used = {axiom.strip() for _, group in records for axiom in group.split(",") if axiom.strip()}
        if len(reported) != len(expected) or set(reported) != set(expected) or used - ALLOWED_AXIOMS:
            raise SystemExit(
                f"Axiom coverage mismatch or unapproved axioms: "
                f"reported={reported}, unapproved={sorted(used - ALLOWED_AXIOMS)}"
            )
        print(f"Lean axiom audit passed; foundational axioms: {sorted(used)}")


if __name__ == "__main__":
    main()
