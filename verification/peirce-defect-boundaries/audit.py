#!/usr/bin/env python3
"""Check owner coverage and Lean-reported foundational axiom dependencies."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "lean/InfoGeometry/OperatorAlgebra/PeirceDefectBoundaryAudit.lean"
OWNERS = (
    'InfoGeometry.Algebra.CommutingInvolutionProjection',
    'InfoGeometry.Algebra.OrthogonalPolynomial',
    'InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicUnitRepresentation',
    'InfoGeometry.OperatorAlgebra.PeirceSpine.ReynoldsProjection',
    'InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceHilbertPositivity',
    'InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceOverlapCounterexamples',
    'InfoGeometry.OperatorAlgebra.PeirceSpine.DefectNoncollapseMatrix',
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def strip_comments(source: str) -> str:
    """Preserve line positions and handle nested Lean block comments."""
    output: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            output.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            output.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end == -1 else end
            output.append(" " * (end - i))
            i = end
        else:
            char = source[i]
            output.append(char if not depth or char == "\n" else " ")
            i += 1
    if depth:
        raise SystemExit("Unclosed Lean block comment")
    return "".join(output)


def owner_declarations(module: str) -> list[str]:
    path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    source = strip_comments(path.read_text())
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", source)
    if forbidden:
        raise SystemExit(f"Forbidden proof constructs in {path}: {forbidden}")
    blocks: list[tuple[str, str]] = []
    heads: list[str] = []
    for line in source.splitlines():
        ns = re.fullmatch(r"namespace\s+(\S+)\s*", line)
        section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(\S+))?\s*", line)
        end = re.fullmatch(r"end(?:\s+(\S+))?\s*", line)
        if ns:
            blocks.append(("namespace", ns[1]))
        elif section:
            blocks.append(("section", section[1] or ""))
        elif end:
            if not blocks:
                raise SystemExit(f"Unmatched end in {path}")
            kind, label = blocks.pop()
            if end[1] and end[1] != label:
                raise SystemExit(f"Mismatched block end in {path}: {end[1]} != {label}")
        else:
            match = re.match(
                r"^\s*(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?"
                r"(private\s+)?(?:def|abbrev|theorem|lemma|structure)\s+([^\s(:]+)", line)
            if match and not match[1]:
                prefix = ".".join(label for kind, label in blocks if kind == "namespace")
                if not prefix:
                    raise SystemExit(f"Unnamespaced declaration in {path}")
                heads.append(prefix + "." + match[2])
    if any(kind != "section" or label for kind, label in blocks):
        raise SystemExit(f"Unclosed namespace/section in {path}: {blocks}")
    return heads



def expected_audit() -> tuple[str, set[str]]:
    chunks = [
        "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n-/\n",
        "".join("import " + module + "\n" for module in OWNERS),
        "\n/-!\n# Peirce defect boundary declaration audit\n\n"
        "This module audits the explicitly declared public definitions and theorems\n"
        "in the seven mathematical owners above. Private helper dependencies\n"
        "are audited transitively. This is a validation target, not an umbrella import.\n"
        "Regenerate with `python3 verification/peirce-defect-boundaries/audit.py --write`.\n"
        "The validator compares actual Lean axiom output with this complete list.\n-/\n",
    ]
    names: set[str] = set()
    for module in OWNERS:
        heads = owner_declarations(module)
        if names.intersection(heads):
            raise SystemExit("Repeated public declaration in audit inventory")
        names.update(heads)
        chunks.append("\n" + "".join("#print axioms " + name + "\n" for name in heads))
    return "".join(chunks), names


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the audit module")
    parser.add_argument("--log", type=Path, help="check the captured Lean audit output")
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    if (package / "lean-toolchain").read_text() != (ROOT / "lean-toolchain").read_text():
        raise SystemExit("Focused and root Lean toolchains differ")
    manifests = [json.loads((directory / "lake-manifest.json").read_text())
                 for directory in (ROOT, package)]
    mathlib_revs = [next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib")
                   for manifest in manifests]
    if mathlib_revs[0] != mathlib_revs[1]:
        raise SystemExit("Focused and root Mathlib revisions differ")
    source, expected = expected_audit()
    if args.write:
        AUDIT.write_text(source)
    if not AUDIT.exists() or AUDIT.read_text() != source:
        raise SystemExit("Audit module is stale; regenerate and compile it")
    print(f"Source coverage: {len(expected)} public declarations in {len(OWNERS)} owners")
    if args.log:
        log = args.log.read_text()
        records = re.findall(
            r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
            log,
        )
        reported = {name for name, _ in records}
        used = {axiom.strip() for _, group in records for axiom in group.split(",") if axiom.strip()}
        if reported != expected or used - ALLOWED_AXIOMS:
            raise SystemExit(
                f"Missing: {sorted(expected - reported)}; unexpected: {sorted(reported - expected)}; "
                f"unapproved axioms: {sorted(used - ALLOWED_AXIOMS)}"
            )
        print(f"Lean axiom audit passed; foundational axioms: {sorted(used)}")


if __name__ == "__main__":
    main()
