#!/usr/bin/env python3
"""Inventory changed owners and validate their Lean-reported axiom dependencies."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "lean/InfoGeometry/Canonical/SouriauDoubledKreinLipschitzBridgeAudit.lean"
OWNERS = (
    "InfoGeometry.Canonical.ConnesSpectralTripleBridge",
    "InfoGeometry.Canonical.SouriauDoubledKreinLipschitzBridge",
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def strip_comments(source: str) -> str:
    """Remove nested Lean comments while preserving positions and line breaks."""
    result: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            result.append("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            result.append("  ")
            i += 2
        elif not depth and source.startswith("--", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            result.append(" " * (end - i))
            i = end
        else:
            char = source[i]
            result.append(char if not depth or char == "\n" else " ")
            i += 1
    if depth:
        raise SystemExit("Unclosed Lean block comment")
    return "".join(result)


def owner_declarations(module: str) -> list[str]:
    path = ROOT / "lean" / (module.replace(".", "/") + ".lean")
    source = strip_comments(path.read_text())
    forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", source)
    if forbidden:
        raise SystemExit(f"Forbidden proof constructs in {path}: {forbidden}")
    blocks: list[tuple[str, str]] = []
    names: list[str] = []
    for line in source.splitlines():
        text = line.strip()
        start = re.fullmatch(r"(?:noncomputable\s+)?(namespace|section)(?:\s+(\S+))?", text)
        if start:
            blocks.append((start.group(1), start.group(2) or ""))
            continue
        finish = re.fullmatch(r"end(?:\s+(\S+))?", text)
        if finish:
            if not blocks:
                raise SystemExit(f"Unmatched end in {path}: {line}")
            _, name = blocks.pop()
            if finish.group(1) and finish.group(1) != name:
                raise SystemExit(f"Unexpected end in {path}: {line}")
            continue
        decl = re.match(
            r"(?:@\[[^\n]*?\]\s*)?(?:noncomputable\s+)?"
            r"(?:def|abbrev|theorem|lemma|structure|instance)\s+([^\s(:]+)", text
        )
        if decl:
            namespace = ".".join(name for kind, name in blocks if kind == "namespace")
            if not namespace:
                raise SystemExit(f"Expected explicit namespace in {path}: {line}")
            names.append(namespace + "." + decl.group(1))
    return names


def expected_audit() -> tuple[str, set[str]]:
    chunks = [
        "/-\nCopyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: InfoGeometry Engine Contributors\n-/\n",
        "".join("import " + module + "\n" for module in OWNERS),
        "\n/-!\n# Souriau Killing Lipschitz declaration audit\n\n"
        "Every explicit public declaration in the changed mathematical owners is\n"
        "listed below. This includes the pre-existing declarations in the amended\n"
        "Connes owner. Generated structure fields and recursors are not separately\n"
        "inventoried. Regenerate using the focused package's audit.py --write.\n-/\n",
    ]
    names: set[str] = set()
    for module in OWNERS:
        declarations = owner_declarations(module)
        if names.intersection(declarations) or len(set(declarations)) != len(declarations):
            raise SystemExit("Repeated declaration in audit inventory")
        names.update(declarations)
        chunks.append("\n" + "".join("#print axioms " + name + "\n" for name in declarations))
    return "".join(chunks), names


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate the Lean audit module")
    parser.add_argument("--log", type=Path, help="validate captured Lean axiom output")
    args = parser.parse_args()
    package = Path(__file__).resolve().parent
    if (package / "lean-toolchain").read_text() != (ROOT / "lean-toolchain").read_text():
        raise SystemExit("Focused and root Lean toolchains differ")
    manifests = [json.loads((directory / "lake-manifest.json").read_text())
                 for directory in (ROOT, package)]
    pinned = [{entry["name"]: entry.get("rev") for entry in manifest["packages"]}
              for manifest in manifests]
    for name, revision in pinned[1].items():
        if pinned[0].get(name) != revision:
            raise SystemExit(f"Focused dependency differs from root pin: {name}")
    source, expected = expected_audit()
    if args.write:
        AUDIT.write_text(source)
    if not AUDIT.exists() or AUDIT.read_text() != source:
        raise SystemExit("Audit source is stale; regenerate and compile it")
    print(f"Source coverage: {len(expected)} explicit declarations in {len(OWNERS)} owners")
    print("Forbidden proof constructs: none in the changed mathematical owners")
    if args.log:
        records = re.findall(
            r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
            args.log.read_text(),
        )
        reported = {name for name, _ in records}
        used = {a.strip() for _, group in records for a in group.split(",") if a.strip()}
        if reported != expected or used - ALLOWED_AXIOMS:
            raise SystemExit(
                f"Missing: {sorted(expected - reported)}; unexpected: {sorted(reported - expected)}; "
                f"unapproved axioms: {sorted(used - ALLOWED_AXIOMS)}"
            )
        print(f"Lean axiom audit passed: {len(reported)} declarations")
        print(f"Foundational axioms: {sorted(used)}")


if __name__ == "__main__":
    main()
