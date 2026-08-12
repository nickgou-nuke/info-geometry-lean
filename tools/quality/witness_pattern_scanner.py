#!/usr/bin/env python3
"""Scan Lean files for generic Prop witness-packing patterns.

The narrow anti-pattern stores a generic `Prop` in a structure field named
`*_statement` with a companion `*_witness` field.  A broader variant stores
a bare `*_witness : Prop` field directly.  Both are vacuous: the instantiator
can supply `True`, and the Lean kernel checks no mathematical content.

Usage
-----
    # Generate initial baseline (freeze existing debt):
    python3 tools/quality/witness_pattern_scanner.py \\
      --root lean/InfoGeometry \\
      --json-out reports/audit/witness-baseline.json \\
      --print-summary

    # CI gate — fail on new instances beyond frozen baseline:
    python3 tools/quality/witness_pattern_scanner.py \\
      --root lean/InfoGeometry \\
      --baseline reports/audit/witness-baseline.json \\
      --fail-on-new

    # Print human-readable inventory:
    python3 tools/quality/witness_pattern_scanner.py \\
      --root lean/InfoGeometry \\
      --print-summary
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# ── Regexes ──────────────────────────────────────────────────────────

# Matches:  someField_statement : Prop
# Allows optional leading whitespace, field doc comments above, etc.
STATEMENT_RE = re.compile(
    r"^\s+(\w+_statement)\s*(?::.*?)?\s*:\s*Prop\b", re.MULTILINE
)

# Broader: also catches `foo_statement : Prop` with type annotations
# like `(hFoo : ...)` before the colon — rare but possible.
STATEMENT_SIMPLE_RE = re.compile(r"^\s{2,}(\w+_statement)\s*:\s*Prop\b")

# Matches:  someField_witness : Prop
BARE_WITNESS_PROP_RE = re.compile(r"^\s{2,}(\w+_witness)\s*:\s*Prop\b")

# Matches:  someField_witness :
WITNESS_RE = re.compile(r"^\s+(\w+_witness)\s*:", re.MULTILINE)


# ── Comment Stripping ────────────────────────────────────────────────

def strip_lean_comments(text: str) -> str:
    """Remove Lean line and block comments while preserving line numbers."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    in_char = False

    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "\"":
                    in_string = False
                i += 1
            continue

        if in_char:
            out.append(ch)
            if ch == "\\" and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if ch == "'":
                    in_char = False
                i += 1
            continue

        if ch == "-" and nxt == "-":
            out.extend(" " for _ in iter(text[i:].split("\n", 1)[0]))
            i += len(text[i:].split("\n", 1)[0])
            continue

        if ch == "/" and nxt == "-":
            depth = 1
            out.extend("  ")
            i += 2
            continue

        if ch == "\"":
            in_string = True
        elif ch == "'":
            in_char = True
        out.append(ch)
        i += 1

    return "".join(out)


# ── Scanning ─────────────────────────────────────────────────────────

def scan_file(path: Path) -> list[dict]:
    """Find generic Prop witness-packing patterns in a single Lean file."""
    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return []

    lines = strip_lean_comments(text).splitlines()
    hits: list[dict] = []

    for i, line in enumerate(lines):
        m = STATEMENT_SIMPLE_RE.search(line)
        if m:
            statement_field = m.group(1)
            stem = statement_field.removesuffix("_statement")
            expected_witness = f"{stem}_witness"

            # Look for companion witness within next 15 lines
            witness_found = False
            witness_line = None
            for j in range(i + 1, min(i + 16, len(lines))):
                if expected_witness in lines[j]:
                    wm = re.search(rf"\b{re.escape(expected_witness)}\b", lines[j])
                    if wm:
                        witness_found = True
                        witness_line = j + 1
                        break

            hits.append(
                {
                    "file": str(path),
                    "line": i + 1,
                    "kind": "statement",
                    "statement_field": statement_field,
                    "witness_field": expected_witness if witness_found else None,
                    "witness_line": witness_line,
                    "has_companion": witness_found,
                }
            )

        mw = BARE_WITNESS_PROP_RE.search(line)
        if mw:
            witness_field = mw.group(1)
            hits.append(
                {
                    "file": str(path),
                    "line": i + 1,
                    "kind": "bare_witness",
                    "statement_field": witness_field,
                    "witness_field": witness_field,
                    "witness_line": i + 1,
                    "has_companion": False,
                }
            )

    return hits


def scan_directory(root: Path) -> list[dict]:
    """Scan all .lean files under root recursively."""
    all_hits: list[dict] = []
    for f in sorted(root.rglob("*.lean")):
        all_hits.extend(scan_file(f))
    return all_hits


# ── Baseline logic ───────────────────────────────────────────────────

def load_baseline(path: Path) -> set[tuple[str, str]]:
    """Load a frozen baseline as a set of (file, statement_field) keys."""
    if not path.exists():
        return set()
    data = json.loads(path.read_text())
    return {(h["file"], h["statement_field"]) for h in data}


def find_new_instances(
    hits: list[dict], baseline: set[tuple[str, str]]
) -> list[dict]:
    """Return hits not present in the baseline."""
    return [
        h
        for h in hits
        if (h["file"], h["statement_field"]) not in baseline
    ]


# ── Output ───────────────────────────────────────────────────────────

def print_summary(hits: list[dict], new_hits: list[dict] | None = None) -> None:
    """Print a human-readable summary."""
    paired = [h for h in hits if h["kind"] == "statement" and h["has_companion"]]
    orphan = [h for h in hits if h["kind"] == "statement" and not h["has_companion"]]
    bare_witness = [h for h in hits if h["kind"] == "bare_witness"]

    print(f"\n{'='*60}")
    print(f"  Witness-Pack Scanner Results")
    print(f"{'='*60}")
    print(f"  Total generic Prop witness-pack fields found: {len(hits)}")
    print(f"  _statement : Prop fields found: {len(paired) + len(orphan)}")
    print(f"  With companion _witness field (full pair): {len(paired)}")
    print(f"  Without companion (bare Prop field): {len(orphan)}")
    print(f"  Bare _witness : Prop fields: {len(bare_witness)}")
    print()

    if paired:
        print(f"  ── Full pairs ({len(paired)}) ──")
        for h in paired:
            print(
                f"    {h['file']}:{h['line']}  "
                f"{h['statement_field']} / {h['witness_field']}"
            )
        print()

    if orphan:
        print(f"  ── Bare Prop _statement fields ({len(orphan)}) ──")
        for h in orphan:
            print(f"    {h['file']}:{h['line']}  {h['statement_field']}")
        print()

    if bare_witness:
        print(f"  ── Bare Prop _witness fields ({len(bare_witness)}) ──")
        for h in bare_witness:
            print(f"    {h['file']}:{h['line']}  {h['witness_field']}")
        print()

    if new_hits is not None:
        if new_hits:
            print(f"  !! NEW instances (not in baseline): {len(new_hits)}")
            for h in new_hits:
                marker = "PAIR" if h["has_companion"] else h["kind"].upper()
                print(
                    f"    [{marker}] {h['file']}:{h['line']}  "
                    f"{h['statement_field']}"
                )
        else:
            print(f"  ✓ No new instances beyond baseline.")
    print()


# ── Main ─────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Scan Lean files for _statement : Prop / _witness pairs."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("lean/InfoGeometry"),
        help="Root directory to scan (default: lean/InfoGeometry)",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        default=None,
        help="Path to a frozen baseline JSON for comparison",
    )
    parser.add_argument(
        "--json-out",
        type=Path,
        default=None,
        help="Write full scan results as JSON to this path",
    )
    parser.add_argument(
        "--print-summary",
        action="store_true",
        help="Print human-readable summary to stdout",
    )
    parser.add_argument(
        "--fail-on-new",
        action="store_true",
        help="Exit with code 1 if new instances are found beyond baseline",
    )

    args = parser.parse_args()

    # Scan
    hits = scan_directory(args.root)

    # Baseline comparison
    new_hits = None
    if args.baseline:
        baseline = load_baseline(args.baseline)
        new_hits = find_new_instances(hits, baseline)

    # Output
    if args.print_summary or (not args.json_out and not args.fail_on_new):
        print_summary(hits, new_hits)

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(hits, indent=2) + "\n")
        print(f"Wrote {len(hits)} entries to {args.json_out}")

    # CI gate
    if args.fail_on_new and new_hits:
        print(
            f"\n✗ FAIL: {len(new_hits)} new witness-pack instance(s) "
            f"found beyond baseline.",
            file=sys.stderr,
        )
        sys.exit(1)


if __name__ == "__main__":
    main()
