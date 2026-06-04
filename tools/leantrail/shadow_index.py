#!/usr/bin/env python3
"""Shadow Index — scan the repository for proof debt and emit a typed inventory.

Usage:
    python3 tools/leantrail/shadow_index.py [--json shadow_manifest.json] [--report ShadowReport.md]
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[2]
LEAN_DIR = REPO / "lean" / "InfoGeometry"

SHADOW_KINDS = {
    "sorryDebt": "explicit `sorry` in proof body",
    "vacuityDebt": "`_True : Prop := True` or equivalent vacuity",
    "wrapperDebt": "certificate/witness/bridge wrapper",
    "missingPremise": "unstated hypothesis dependency",
    "overclaimedBridge": "doc claims theorem, no proof",
    "unrepresentedAnalogy": "physical analogy stated as proved",
    "failedCompilation": "file does not compile",
    "dependencyCycleRisk": "circular dependency suspected",
}

# Keyword domain mapping from KeywordIndex
DOMAINS = [
    "Berezinian", "Pfaffian", "BottPeriodicity", "KANDecomposition",
    "CliffordAlgebra", "AltlandZirnbauer", "GrothendieckGroup",
    "MajoranaBEC", "TomitaTakesaki", "MoebiusOrientifold",
    "SvozilSectorization", "VirasoroCentralCharge", "HodgeKrein",
]

# Vacuity suffixes (from Vacuity Critic)
VACUITY_SUFFIXES = [
    "_True", "_sorryProof", "_certificate", "_valid", "_witness",
    "_bridge", "_surety", "_indemnity", "_attestation", "_covenant",
    "_verity", "_testimony", "_accreditation", "_bond", "_seal",
    "_voucher", "_nexus", "_guaranty",
]


def guess_domain(filepath: str) -> str:
    """Guess which keyword domain a file belongs to."""
    fp = filepath.lower()
    for d in DOMAINS:
        if d.lower() in fp:
            return d
    # Check parent directory
    parts = Path(filepath).parts
    if "Krein" in parts:
        return "HodgeKrein"
    if "Clifford" in parts:
        return "CliffordAlgebra"
    if "Canonical" in parts:
        return "GrothendieckGroup"
    if "OperatorAlgebra" in parts:
        return "TomitaTakesaki"
    return "General"


def scan_file(filepath: Path) -> list[dict[str, Any]]:
    """Scan a single .lean file for shadow debt."""
    rel = str(filepath.relative_to(REPO))
    domain = guess_domain(rel)
    items = []

    try:
        text = filepath.read_text(errors="replace")
    except Exception:
        return items

    lines = text.split("\n")
    in_block = False

    for i, line in enumerate(lines, 1):
        stripped = line.strip()

        # Track block comments
        if in_block:
            if "-/" in stripped:
                in_block = False
            continue
        if stripped.startswith("/-"):
            in_block = True
            continue

        code = line.split("--")[0]
        code_clean = re.sub(r'"[^"]*"', "", code)

        # 1. Explicit sorry
        if re.search(r"(?<![a-zA-Z0-9_.])\bsorry\b", code_clean):
            items.append({
                "declaration": f"{rel}:{i}",
                "kind": "sorryDebt",
                "domain": domain,
                "file": rel,
                "line": i,
                "description": f"Explicit `sorry` at line {i}",
                "avoidance_count": 0,
                "last_attempt": "",
                "status": "open_debt",
            })

        # 2. Vacuity: _True : Prop := ...
        for suffix in VACUITY_SUFFIXES:
            if suffix in code and "Prop" in code:
                items.append({
                    "declaration": f"{rel}:{i}",
                    "kind": "vacuityDebt",
                    "domain": domain,
                    "file": rel,
                    "line": i,
                    "description": f"Vacuous field `{suffix}` at line {i}",
                    "avoidance_count": 0,
                    "last_attempt": "",
                    "status": "open_debt",
                })
                break

        # 3. Wrapper: structure with _True field
        if re.search(r"structure\s+\w+", code_clean) and i < len(lines):
            # Check next few lines for certificate fields
            for j in range(i + 1, min(i + 10, len(lines))):
                next_code = lines[j].split("--")[0]
                if any(s in next_code and "Prop" in next_code for s in VACUITY_SUFFIXES):
                    items.append({
                        "declaration": f"{rel}:{i}",
                        "kind": "wrapperDebt",
                        "domain": domain,
                        "file": rel,
                        "line": i,
                        "description": f"Structure with certificate fields at line {i}",
                        "avoidance_count": 0,
                        "last_attempt": "",
                        "status": "open_debt",
                    })
                    break

    return items


def scan_repository(lean_dir: Path = LEAN_DIR) -> list[dict[str, Any]]:
    """Scan all .lean files in the repository for shadow debt."""
    all_items = []
    for f in sorted(lean_dir.rglob("*.lean")):
        # Skip evaluation files and generated content
        parts = f.relative_to(REPO).parts
        if any(p in parts for p in ["Eval", ".lake", "lake-packages", "_target"]):
            continue
        items = scan_file(f)
        all_items.extend(items)

    return all_items


def compile_check(filepath: Path) -> bool:
    """Check if a single file compiles."""
    try:
        r = subprocess.run(
            ["lake", "env", "lean", str(filepath)],
            capture_output=True, text=True, timeout=60,
            cwd=str(REPO),
        )
        return r.returncode == 0
    except Exception:
        return False


def add_compilation_failures(items: list[dict[str, Any]], lean_dir: Path = LEAN_DIR) -> None:
    """Add shadow items for files that fail compilation."""
    seen_files = {item["file"] for item in items}
    for f in sorted(lean_dir.rglob("*.lean")):
        rel = str(f.relative_to(REPO))
        if rel in seen_files:
            continue
        if not compile_check(f):
            items.append({
                "declaration": rel,
                "kind": "failedCompilation",
                "domain": guess_domain(rel),
                "file": rel,
                "line": 0,
                "description": "File does not compile",
                "avoidance_count": 0,
                "last_attempt": "",
                "status": "open_debt",
            })


def generate_report(items: list[dict[str, Any]]) -> str:
    """Generate a human-readable shadow report."""
    by_kind = defaultdict(list)
    by_domain = defaultdict(list)
    for item in items:
        by_kind[item["kind"]].append(item)
        by_domain[item["domain"]].append(item)

    total = len(items)
    severity = sum(
        {"sorryDebt": 3, "vacuityDebt": 3, "wrapperDebt": 2, "failedCompilation": 4,
         "missingPremise": 2, "overclaimedBridge": 1, "unrepresentedAnalogy": 1,
         "dependencyCycleRisk": 5}.get(item["kind"], 1)
        for item in items
    )

    lines = [
        f"# Shadow Report — {datetime.now().strftime('%Y-%m-%d %H:%M')}",
        "",
        f"**Total shadow items:** {total}",
        f"**Total severity:** {severity}",
        "",
        "## By Kind",
        "",
        "| Kind | Count | Description |",
        "|------|-------|-------------|",
    ]
    for kind, desc in SHADOW_KINDS.items():
        kind_items = by_kind.get(kind, [])
        lines.append(f"| {kind} | {len(kind_items)} | {desc} |")

    lines.extend([
        "",
        "## By Domain",
        "",
        "| Domain | Count |",
        "|--------|-------|",
    ])
    for domain in sorted(by_domain, key=lambda d: -len(by_domain[d])):
        lines.append(f"| {domain} | {len(by_domain[domain])} |")

    lines.extend([
        "",
        "## Bucket Summary",
        "",
        f"**BUCKET 1 (Closed):** 0 by definition — shadow items are open",
        f"**BUCKET 2 (Conditional):** {len(by_kind.get('missingPremise', []))}",
        f"**BUCKET 3 (Open Debt):** {total - len(by_kind.get('missingPremise', []))}",
        "",
        "---",
        f"*Generated by shadow_index.py — {datetime.now().isoformat()}*",
    ])

    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Shadow Index — scan repo for proof debt")
    parser.add_argument("--json", type=Path, default=REPO / "artifacts" / "shadow_manifest.json",
                        help="Output JSON manifest path")
    parser.add_argument("--report", type=Path, default=REPO / "docs" / "ShadowReport.md",
                        help="Output Markdown report path")
    parser.add_argument("--compile-check", action="store_true",
                        help="Also check compilation of all files (slow)")
    args = parser.parse_args()

    print("Scanning repository for shadow debt...")
    items = scan_repository()

    if args.compile_check:
        print("Checking compilation failures (slow)...")
        add_compilation_failures(items)

    # Save JSON
    args.json.parent.mkdir(parents=True, exist_ok=True)
    with open(args.json, "w") as f:
        json.dump({
            "generated": datetime.now().isoformat(),
            "total_items": len(items),
            "items": items,
        }, f, indent=2)
    print(f"Shadow manifest: {args.json} ({len(items)} items)")

    # Save report
    report = generate_report(items)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(report)
    print(f"Shadow report: {args.report}")

    # Quick summary
    by_kind = defaultdict(int)
    for item in items:
        by_kind[item["kind"]] += 1
    for kind, count in sorted(by_kind.items(), key=lambda x: -x[1]):
        print(f"  {kind:25s}: {count}")


if __name__ == "__main__":
    main()
