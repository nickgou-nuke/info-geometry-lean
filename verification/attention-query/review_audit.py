#!/usr/bin/env python3
"""Independently reconcile a completed AttentionDeclarationAudit Lean log.

This script does not compile Lean and cannot certify a compiler invocation's
exit status. The invoking validation transaction must separately record exit
zero and exact source/toolchain identity. This parser rejects partial, repeated,
or internally inconsistent native JSON evidence.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

OWNERS = (
    'InfoGeometry.Canonical.AttentionQueryGeometry',
    'InfoGeometry.Canonical.AttentionQueryKeyReversal',
    'InfoGeometry.Rotary.RotaryAttentionFlow',
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def reconcile(log: Path) -> dict:
    records = []
    for line_number, line in enumerate(log.read_text().splitlines(), 1):
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValueError(f"Non-JSON compiler output at line {line_number}: {line}") from error
        if not isinstance(record, dict):
            raise ValueError(f"Non-object record at line {line_number}")
        records.append(record)
    declarations = [r for r in records if r.get("record") == "declaration"]
    modules = [r for r in records if r.get("record") == "module"]
    summaries = [r for r in records if r.get("record") == "summary"]
    if len(records) != len(declarations) + len(modules) + len(summaries):
        raise ValueError("Unknown record kind")
    if len(summaries) != 1 or records[-1] is not summaries[0]:
        raise ValueError("Expected exactly one final summary")
    if not declarations:
        raise ValueError("No native declarations audited")
    summary = summaries[0]
    if summary.get("status") != "PASS" or summary.get("modules") != list(OWNERS):
        raise ValueError("Summary status or owner list mismatch")
    if set(summary.get("axiom_whitelist", [])) != ALLOWED:
        raise ValueError("Axiom whitelist mismatch")
    names = [r.get("name") for r in declarations]
    if any(not isinstance(n, str) or not n for n in names) or len(set(names)) != len(names):
        raise ValueError("Missing or duplicate declaration names")
    counts: Counter[str] = Counter()
    all_axioms: set[str] = set()
    for record in declarations:
        owner = record.get("module")
        if owner not in OWNERS:
            raise ValueError(f"Unexpected declaration owner: {owner}")
        if record.get("unsafe") is not False or record.get("partial") is not False:
            raise ValueError(f"Unsafe/partial declaration: {record['name']}")
        if record.get("kind") not in {
            "theorem", "definition", "opaque", "inductive", "constructor", "recursor", "quotient"
        }:
            raise ValueError(f"Rejected declaration kind: {record}")
        axioms = record.get("axioms")
        if not isinstance(axioms, list) or any(not isinstance(a, str) for a in axioms):
            raise ValueError(f"Malformed axiom inventory: {record['name']}")
        if len(axioms) != len(set(axioms)) or not set(axioms) <= ALLOWED:
            raise ValueError(f"Rejected axiom inventory: {record['name']}")
        counts[owner] += 1
        all_axioms.update(axioms)
    if set(counts) != set(OWNERS) or len(modules) != len(OWNERS):
        raise ValueError("Incomplete owner coverage")
    module_counts = {r.get("module"): r.get("declarations") for r in modules}
    if len(module_counts) != len(modules) or module_counts != dict(counts):
        raise ValueError("Module counts do not reconcile")
    if summary.get("declarations") != len(declarations):
        raise ValueError("Total declaration count mismatch")
    if set(summary.get("axioms", [])) != all_axioms:
        raise ValueError("Axiom union mismatch")
    return {
        "status": "PASS",
        "scope": "Independent reconciliation of completed native audit output",
        "audit_log_sha256": hashlib.sha256(log.read_bytes()).hexdigest(),
        "declarations": len(declarations),
        "module_counts": dict(counts),
        "axioms": sorted(all_axioms),
        "declaration_names": names,
    }


def main() -> None:
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("audit_log", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(reconcile(args.audit_log), indent=2) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
