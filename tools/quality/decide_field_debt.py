#!/usr/bin/env python3
"""Enumerate proofs that use `decide` on a goal over a noncomputable field.

Why this exists
---------------
In this pinned Mathlib, `DecidableEq Rat` is *not* computable: kernel reduction
gets stuck at `instDecidableEqRat`.  Consequently

    example : ((1/2 : Rat) + 1/2 = 1) := by decide

fails.  Any proof of the shape `by decide` whose statement mentions `Rat`,
`Real`, `Complex` or another noncomputable-ordered field can therefore never
succeed, no matter how small the term is.

The canonical build currently fails at 467 such sites (83% of all build errors).
They are not false mathematics -- they are proofs written with a tactic that
cannot run on those types.  This script makes that debt enumerable so it can be
worked as a queue instead of rediscovered from compiler output.

`decide` over `Z`, `Nat`, `Fin n` and finite types *is* computable and is
deliberately NOT reported here; that is a legitimate technique.

Usage:
    python3 tools/quality/decide_field_debt.py                # human summary
    python3 tools/quality/decide_field_debt.py --json-out X   # machine ledger
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# Types whose `DecidableEq` is not computable in this Mathlib.
NONCOMPUTABLE_FIELDS = ("ℚ", "ℝ", "ℂ", "Rat", "Real", "Complex")

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<kw>theorem|lemma|example)\s+(?P<name>[^\s:({\[]*)"
)
FIELD_RE = re.compile("|".join(re.escape(f) for f in NONCOMPUTABLE_FIELDS))


def strip_comment(line: str) -> str:
    """Drop a trailing `--` comment, respecting nothing else. Good enough for triage."""
    idx = line.find("--")
    return line if idx < 0 else line[:idx]


def declaration_type(path: Path, decl_start: int) -> str:
    """Collect the statement text of a declaration: from `decl_start` up to the
    first line whose stripped form starts the proof (`:=` / `where`)."""
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    buf: list[str] = []
    for raw in lines[decl_start : decl_start + 40]:
        clean = strip_comment(raw)
        buf.append(clean)
        stripped = clean.strip()
        if stripped.startswith(":= ") or stripped.endswith(":= by") or stripped == ":=":
            break
        if stripped == "where":
            break
    return "\n".join(buf)


def scan(paths: list[Path]) -> list[dict]:
    findings: list[dict] = []
    for path in paths:
        try:
            lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            continue
        in_block_comment = False
        for idx, raw in enumerate(lines):
            # Track /- ... -/ so docstrings do not produce false positives.
            if "/-" in raw and "-/" not in raw:
                in_block_comment = True
            if in_block_comment:
                if "-/" in raw:
                    in_block_comment = False
                continue

            m = DECL_RE.match(raw)
            if not m:
                continue
            stmt = declaration_type(path, idx)
            if not FIELD_RE.search(stmt):
                continue

            # Look for `decide` inside this declaration's proof body.
            body: list[str] = []
            for probe in lines[idx : idx + 60]:
                c = strip_comment(probe)
                if "/-" in c and "-/" not in c:
                    break
                body.append(c)
                s = c.strip()
                if s.startswith("end ") or s.startswith("namespace ") or s.startswith("section "):
                    break
            sites = [
                idx + 1 + off
                for off, c in enumerate(body)
                if re.search(r"(?<![\w.])decide(?![\w])", c)
            ]
            if not sites:
                continue
            findings.append(
                {
                    "file": path.relative_to(ROOT).as_posix(),
                    "decl_line": idx + 1,
                    "decl_name": m.group("name"),
                    "decide_sites": sites,
                    "site_count": len(sites),
                }
            )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json-out", type=Path, default=None)
    parser.add_argument(
        "--root",
        type=Path,
        default=ROOT / "lean",
        help="directory to scan (default: lean/)",
    )
    args = parser.parse_args()

    paths = sorted(
        p
        for p in args.root.rglob("*.lean")
        if ".lake" not in p.parts
        # Skip dot-directories (agent worktrees, caches) so mirrored copies of
        # the corpus are not counted twice.
        and not any(part.startswith(".") for part in p.relative_to(args.root).parts)
    )
    findings = scan(paths)
    total_sites = sum(f["site_count"] for f in findings)

    report = {
        "scanned_files": len(paths),
        "affected_declarations": len(findings),
        "decide_sites": total_sites,
        "noncomputable_field_types": list(NONCOMPUTABLE_FIELDS),
        "rationale": (
            "DecidableEq over Rat/Real/Complex is noncomputable in this Mathlib, "
            "so `by decide` can never close these goals."
        ),
        "findings": findings,
    }

    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(f"scanned files            : {len(paths)}")
    print(f"affected declarations    : {len(findings)}")
    print(f"impossible `decide` sites: {total_sites}")
    if findings:
        by_file: dict[str, int] = {}
        for f in findings:
            by_file[f["file"]] = by_file.get(f["file"], 0) + f["site_count"]
        print("\nworst files:")
        for name, count in sorted(by_file.items(), key=lambda kv: -kv[1])[:20]:
            print(f"  {count:5d}  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
