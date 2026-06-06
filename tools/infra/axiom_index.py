#!/usr/bin/env python3
"""
Axiom indexer — uses tools/infra/axiom_index.lean to scan .olean files.

Usage:
  python3 tools/infra/axiom_index.py                    # all InfoGeometry modules
  python3 tools/infra/axiom_index.py --all               # all built modules
  python3 tools/infra/axiom_index.py Module.Name         # one module
  python3 tools/infra/axiom_index.py --json              # JSON output
"""

import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
OLEAN_DIR = REPO_ROOT / ".lake" / "build" / "lib" / "lean"
INDEX_SCRIPT = REPO_ROOT / "tools" / "infra" / "axiom_index.lean"

CANONICAL = {"propext", "Quot.sound", "Classical.choice"}

SUSPICIOUS_PATTERNS = [
    (re.compile(r"^propext$"), False),
    (re.compile(r"^Quot\.sound$"), False),
    (re.compile(r"^Classical\.choice$"), False),
    (re.compile(r"^sorryAx$"), False),
    (re.compile(r"^propext_"), True),
    (re.compile(r"^Quot\."), True),
    (re.compile(r"^Classical\.(.+)$"), lambda m: m.group(1) != "choice"),
    (re.compile(r"^[A-Z][a-z]+[A-Z]"), True),
    (re.compile(r"\.(axiom|ax)$", re.I), True),
]


def is_suspicious(name: str) -> tuple[bool, str]:
    if name in CANONICAL:
        return False, "canonical"
    if name == "sorryAx":
        return False, "sorry placeholder"
    for pat, test in SUSPICIOUS_PATTERNS:
        m = pat.match(name)
        if m:
            if callable(test):
                return test(m), f"pattern: {pat.pattern}"
            return test, f"pattern: {pat.pattern}"
    return True, "unknown"


def parse_decl_line(line: str) -> dict | None:
    m = re.match(
        r"DECL:(.+):kind=(.+):partial=(true|false):unsafe=(true|false):axiom=(true|false):axioms=#\[(.*)\]",
        line,
    )
    if not m:
        return None
    name = m.group(1)
    kind = m.group(2)
    partial = m.group(3) == "true"
    unsafe = m.group(4) == "true"
    is_axiom = m.group(5) == "true"
    axioms_str = m.group(6)
    axioms = [a.strip() for a in axioms_str.split(",") if a.strip()]
    return {
        "name": name,
        "kind": kind,
        "partial": partial,
        "unsafe": unsafe,
        "is_axiom": is_axiom,
        "axioms": axioms,
        "nonstandard": [a for a in axioms if a not in CANONICAL],
    }


def scan_olean(olean_path: Path) -> tuple[list[dict], str | None]:
    if not olean_path.exists():
        return [], "not found"
    module = str(olean_path.relative_to(OLEAN_DIR).with_suffix("")).replace("/", ".")
    result = subprocess.run(
        ["lake", "env", "lean", "--run", str(INDEX_SCRIPT), str(olean_path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        timeout=120,
    )
    if result.returncode != 0:
        return [], f"lean error: {result.stderr[:300]}"
    decls = []
    for line in result.stdout.split("\n"):
        d = parse_decl_line(line)
        if d:
            decls.append(d)
    return decls, None


def main():
    parser = argparse.ArgumentParser(description="Axiom indexer")
    parser.add_argument("modules", nargs="*")
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--batch", type=int, default=1, help="Process N modules at a time")
    args = parser.parse_args()

    if args.modules:
        paths = []
        for m in args.modules:
            p = OLEAN_DIR / (m.replace(".", "/") + ".olean")
            paths.append(p)
    elif args.all:
        paths = sorted(OLEAN_DIR.rglob("*.olean"))
    else:
        paths = sorted(OLEAN_DIR.rglob("InfoGeometry/**/*.olean"))

    if not paths:
        print("No .olean files found.")
        sys.exit(1)

    print(f"Scanning {len(paths)} module(s)...")

    axiom_usage = Counter()
    axiom_modules: dict[str, set[str]] = defaultdict(set)
    axiomless: list[str] = []
    suspicious: dict[str, list[tuple[str, str, str]]] = defaultdict(list)
    total_decls = 0
    total_nonstd = 0

    for i, p in enumerate(paths):
        decls, err = scan_olean(p)
        module = str(p.relative_to(OLEAN_DIR).with_suffix("")).replace("/", ".")
        if err:
            print(f"  [{i+1}/{len(paths)}] {module}: ERROR {err}")
            continue

        has_nonstandard = False
        for d in decls:
            total_decls += 1
            if d["nonstandard"]:
                total_nonstd += 1
                has_nonstandard = True
            for a in d["axioms"]:
                axiom_usage[a] += 1
                axiom_modules[a].add(module)
                susp, reason = is_suspicious(a)
                if susp:
                    suspicious[a].append((module, d["name"], reason))

        status = "!" if has_nonstandard else "✓"
        nstd = sum(1 for d in decls if d["nonstandard"])
        npart = sum(1 for d in decls if d["partial"])
        nunsafe = sum(1 for d in decls if d["unsafe"])
        print(f"  [{i+1}/{len(paths)}] {module}: {status} {len(decls)} decls, {nstd}✗ {npart}p {nunsafe}u")

        if not has_nonstandard:
            axiomless.append(module)

    # === REPORT ===
    print("\n" + "=" * 70)
    print("AXIOM INDEX REPORT")
    print("=" * 70)

    # Unique axioms
    print(f"\nAll unique axioms ({len(axiom_usage)}):")
    for ax, count in axiom_usage.most_common():
        modules = axiom_modules[ax]
        can = "ⓘ" if ax in CANONICAL else "⚠" if ax in suspicious else " "
        print(f"  {can} {ax}: {count} uses in {len(modules)} modules")

    # Suspicious
    if suspicious:
        print(f"\nSuspicious axioms ({len(suspicious)}):")
        for ax, occ in sorted(suspicious.items()):
            print(f"  ⚠ {ax}:")
            for mod, decl, reason in occ[:3]:
                print(f"      {mod} :: {decl} ({reason})")

    # Axiomless modules
    print(f"\nAxiomless modules ({len(axiomless)} / {len(paths)}):")
    for m in axiomless[:10]:
        print(f"  {m}")
    if len(axiomless) > 10:
        print(f"  ... +{len(axiomless) - 10} more")

    # Summary
    n_nonstd_decls = sum(1 for _ in axiom_usage.elements() if _ not in CANONICAL)
    print(f"\nSummary:")
    print(f"  Modules: {len(paths)}")
    print(f"  Declarations: {total_decls}")
    print(f"  Nonstandard axiom users: {total_nonstd}")
    print(f"  Unique axioms: {len(axiom_usage)}")
    print(f"  Axiomless modules: {len(axiomless)}")

    if args.json:
        print(json.dumps({
            "modules": len(paths),
            "declarations": total_decls,
            "axiom_usage": dict(axiom_usage.most_common()),
            "axiomless": axiomless[:100],
            "suspicious": {k: v[:5] for k, v in suspicious.items()},
        }, indent=2))


if __name__ == "__main__":
    main()
