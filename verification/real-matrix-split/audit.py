#!/usr/bin/env python3
"""Inventory the selected source heads and check Lean-reported axiom dependencies.

This is a bounded, line-oriented source inventory, not a Lean parser or a
whole-environment declaration enumeration. It covers the explicitly named public
declaration forms used by the seven owners below, including named instances.
Private helpers and generated declarations are not independently enumerated;
their dependencies are included when Lean reports the audited heads' axioms.
Actual Lean compilation and semantic review are separate requirements.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import tomllib

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "lean/InfoGeometry/OperatorAlgebra/RealMatrixSplitAudit.lean"
OWNERS = (
    "InfoGeometry.OperatorAlgebra.WeightedAdjointCompatibility",
    "InfoGeometry.Physics.FiniteMetriplecticDynamics",
    "InfoGeometry.OperatorAlgebra.RealMatrixSplit",
    "InfoGeometry.OperatorAlgebra.RealMatrixSplitGeometry",
    "InfoGeometry.OperatorAlgebra.RealMatrixSplitExamples",
    "InfoGeometry.OperatorAlgebra.RealMetricAdjoint",
    "InfoGeometry.Physics.FiniteMetriplecticMatrixSplit",
)
EXPECTED_DEPENDENCIES = {
    "mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
    "aesop", "Qq", "batteries", "Cli",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|native_decide|unsafe|implemented_by)\b"
)
DECLARATION = re.compile(
    r"^(?:(?:noncomputable|protected|public)\s+)*"
    r"(?P<private>private\s+)?"
    r"(?P<kind>def|abbrev|theorem|lemma|structure|class|inductive|opaque|instance)\b"
    r"(?:\s+\(priority\s*:=\s*[^)]+\))?"
    r"\s+(?P<name>[^\s(:\[{]+)"
)
DECLARATION_START = re.compile(
    r"^(?:(?:noncomputable|protected|public|private)\s+)*"
    r"(?:def|abbrev|theorem|lemma|structure|class|inductive|opaque|instance)\b"
)


def strip_comments(source: str) -> str:
    """Mask nested comments and ordinary string literals, preserving newlines.

    The owner files use no raw string or syntax-quotation declarations. Such
    general Lean syntax is outside this inventory's stated scope.
    """
    output: list[str] = []
    depth = 0
    in_string = False
    i = 0
    while i < len(source):
        if in_string:
            char = source[i]
            if char == "\\" and i + 1 < len(source):
                output.append(" \n" if source[i + 1] == "\n" else "  ")
                i += 2
                continue
            if char == '"':
                in_string = False
            output.append("\n" if char == "\n" else " ")
            i += 1
        elif source.startswith("/-", i):
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
        elif not depth and source[i] == '"':
            in_string = True
            output.append(" ")
            i += 1
        else:
            char = source[i]
            output.append(char if not depth or char == "\n" else " ")
            i += 1
    if depth or in_string:
        raise SystemExit("Unclosed Lean block comment or ordinary string literal")
    return "".join(output)


def owner_declarations(module: str) -> list[str]:
    path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    source = strip_comments(path.read_text(encoding="utf-8"))
    forbidden = FORBIDDEN.findall(source)
    if forbidden:
        raise SystemExit(f"Forbidden proof constructs in {path}: {forbidden}")
    blocks: list[tuple[str, str]] = []
    heads: list[str] = []
    for line_number, raw in enumerate(source.splitlines(), 1):
        line = raw.strip()
        # The selected owners use single-line attribute brackets. Repeated
        # leading attributes are removed before recognizing a declaration head.
        while line.startswith("@["):
            attribute = re.match(r"^@\[[^\n]*?\]\s*", line)
            if attribute is None:
                raise SystemExit(f"Unsupported multiline attribute at {path}:{line_number}")
            line = line[attribute.end():]
        ns = re.fullmatch(r"namespace\s+(\S+)\s*", line)
        section = re.fullmatch(r"(?:noncomputable\s+)?section(?:\s+(\S+))?\s*", line)
        end = re.fullmatch(r"end(?:\s+(\S+))?\s*", line)
        if ns:
            blocks.append(("namespace", ns[1]))
        elif section:
            blocks.append(("section", section[1] or ""))
        elif end:
            if not blocks:
                raise SystemExit(f"Unmatched end at {path}:{line_number}")
            _, label = blocks.pop()
            if end[1] and end[1] != label:
                raise SystemExit(f"Mismatched block end at {path}:{line_number}: {end[1]} != {label}")
        else:
            match = DECLARATION.match(line)
            if match is None:
                if DECLARATION_START.match(line):
                    raise SystemExit(
                        f"Unsupported or anonymous declaration at {path}:{line_number}; "
                        "give instances explicit names and extend the inventory if needed"
                    )
                continue
            if match["private"]:
                continue
            name = match["name"]
            if name in {"where", ":="} or "«" in name or "»" in name:
                raise SystemExit(f"Unsupported declaration name at {path}:{line_number}: {name}")
            prefix = ".".join(label for kind, label in blocks if kind == "namespace")
            if name.startswith("_root_."):
                heads.append(name.removeprefix("_root_."))
            elif prefix:
                heads.append(prefix + "." + name)
            else:
                raise SystemExit(f"Unnamespaced declaration at {path}:{line_number}")
    # A file-scoped anonymous noncomputable section may end at EOF in Lean.
    if any(kind != "section" or label for kind, label in blocks):
        raise SystemExit(f"Unclosed namespace/section in {path}: {blocks}")
    if not heads:
        raise SystemExit(f"No explicit public declarations inventoried in {path}")
    return heads


def expected_audit() -> tuple[str, set[str]]:
    chunks = [
        "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n-/\n",
        "".join("import " + module + "\n" for module in OWNERS),
        "\n/-!\n# Real matrix split declaration audit\n\n"
        "This target audits the explicitly named public declarations, including\n"
        "named instances, in the seven mathematical owners above. It does not\n"
        "enumerate Lean-generated declarations. Dependencies of private helpers\n"
        "are audited transitively through the listed heads.\n\n"
        "Regenerate with `python3 verification/real-matrix-split/audit.py --write`.\n"
        "Source inventory, kernel compilation, axiom checking, and semantic\n"
        "review are separate checks. This target is not an umbrella import.\n-/\n",
    ]
    names: set[str] = set()
    for module in OWNERS:
        heads = owner_declarations(module)
        duplicates = [name for name, count in Counter(heads).items() if count != 1]
        if duplicates or names.intersection(heads):
            raise SystemExit(f"Repeated declaration in audit inventory: {module}")
        names.update(heads)
        chunks.append("\n" + "".join("#print axioms " + name + "\n" for name in heads))
    return "".join(chunks), names


def check_pins(package: Path) -> None:
    if (package / "lean-toolchain").read_bytes() != (ROOT / "lean-toolchain").read_bytes():
        raise SystemExit("Focused and root Lean toolchains differ")
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    focused_manifest = json.loads((package / "lake-manifest.json").read_text())
    config = tomllib.loads((package / "lakefile.toml").read_text())
    if focused_manifest["name"] != config["name"]:
        raise SystemExit("Focused manifest and lakefile package names differ")
    root_pins = {
        p["name"]: (p["url"], p["rev"], p.get("subDir"))
        for p in root_manifest["packages"] if p["type"] == "git"
    }
    focused = focused_manifest["packages"]
    if any(p["type"] != "git" for p in focused):
        raise SystemExit("The focused manifest must contain only pinned Git dependencies")
    names = [p["name"] for p in focused]
    if len(names) != len(set(names)) or set(names) != EXPECTED_DEPENDENCIES:
        raise SystemExit(f"Unexpected focused dependency inventory: {names}")
    for p in focused:
        pin = (p["url"], p["rev"], p.get("subDir"))
        if root_pins.get(p["name"]) != pin:
            raise SystemExit(f"Focused dependency differs from the root Git pin: {p['name']}")
    requirements = config.get("require", [])
    if len(requirements) != 1 or requirements[0]["name"] != "mathlib":
        raise SystemExit("The focused package must require exactly the root-pinned Mathlib")
    requirement = requirements[0]
    if (requirement.get("git"), requirement.get("rev"), requirement.get("subDir")) != root_pins["mathlib"]:
        raise SystemExit("Focused lakefile Mathlib requirement differs from the root Git pin")


def check_axioms(log: str, expected: set[str]) -> None:
    records = re.findall(
        r"'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        log,
    )
    counts = Counter(name for name, _ in records)
    reported = set(counts)
    duplicates = sorted(name for name, count in counts.items() if count != 1)
    used = {axiom.strip() for _, group in records for axiom in group.split(",") if axiom.strip()}
    if reported != expected or used - ALLOWED_AXIOMS or duplicates:
        raise SystemExit(
            f"Missing: {sorted(expected - reported)}; unexpected: {sorted(reported - expected)}; "
            f"duplicate records: {duplicates}; unapproved axioms: {sorted(used - ALLOWED_AXIOMS)}"
        )
    print(f"Lean axiom audit passed: {len(records)} distinct records; foundational axioms: {sorted(used)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the audit module")
    parser.add_argument("--log", type=Path, help="check one captured fresh Lean audit invocation")
    args = parser.parse_args()
    check_pins(Path(__file__).resolve().parent)
    source, expected = expected_audit()
    if args.write:
        AUDIT.write_text(source, encoding="utf-8")
    if not AUDIT.exists() or AUDIT.read_text(encoding="utf-8") != source:
        raise SystemExit("Audit module is stale; regenerate and compile it")
    print(f"Source coverage: {len(expected)} explicit public declarations in {len(OWNERS)} owners")
    if args.log:
        check_axioms(args.log.read_text(encoding="utf-8"), expected)


if __name__ == "__main__":
    main()
