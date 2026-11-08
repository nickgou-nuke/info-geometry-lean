#!/usr/bin/env python3
"""
No-Wrapper, 3-Bucket Header, and Declaration Docstring Auditor.

Reuses `tools.quality.common` and `tools.quality.audit_docstrings` to verify:
1. Module docstring `/-! ... -/` contains BUCKET 1, BUCKET 2, and BUCKET 3 sections
   (when `--require-buckets` is enabled).
2. Zero `export` namespace shims (`export Foo (...)`).
3. Zero `Prop`-valued `def` surfaces (`def ... : Prop :=`).
4. Zero `:= rfl` / `:= by rfl` trivial theorem wrappers.
5. Zero pass-through tuple/re-export theorem wrappers (every `theorem`/`lemma`
   must contain genuine derivation tactics).
6. Every declaration has a `/-- ... -/` docstring (reusing `audit_docstrings.audit_file`).
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from typing import Iterable, List, Tuple

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.quality.common import iter_lean_files, print_grouped_violations
from tools.quality.audit_docstrings import audit_file as audit_docstrings_file

DERIVATION_TACTIC_RE = re.compile(
    r"\b("
    r"calc|rw|simp|simpa|dsimp|unfold|change|induction|rcases|cases| obtain|"
    r"ext|funext|decide|abel|abel_nf|ring|ring_nf|noncomm_ring|peirce_nf|"
    r"omega|linarith|nlinarith|positivity|norm_num|group|module|"
    r"constructor|intro|rintro|apply|have|let|suffices|contrapose|by_cases|"
    r"subst|revert|generalize|congr"
    r")\b"
)

THEOREM_DECL_RE = re.compile(
    r"^\s*(?:protected\s+|private\s+|noncomputable\s+)*(theorem|lemma)\s+([A-Za-z0-9_']+)",
    re.MULTILINE,
)


def iter_target_files(paths: Iterable[str]) -> List[Path]:
    result: List[Path] = []
    for raw in paths:
        p = Path(raw)
        if p.is_dir():
            result.extend(sorted(iter_lean_files(str(p))))
        elif p.is_file() and p.suffix == ".lean":
            result.append(p)
        else:
            raise FileNotFoundError(f"Target path not found or not a .lean file/dir: {raw}")
    return result


def audit_no_wrappers_file(
    filepath: str,
    require_buckets: bool = True,
    forbid_structures: bool = False,
    check_docstrings: bool = True,
) -> List[Tuple[str, int, str]]:
    violations: List[Tuple[str, int, str]] = []
    text = Path(filepath).read_text(encoding="utf-8")
    lines = text.splitlines()

    if require_buckets:
        for bucket in ("BUCKET 1", "BUCKET 2", "BUCKET 3"):
            if bucket not in text:
                violations.append(
                    (filepath, 1, f"Missing '{bucket}' classification header in module docstring")
                )

    for idx, line in enumerate(lines, start=1):
        code = line.split("--")[0]
        if re.match(r"^\s*export\s+", code):
            violations.append((filepath, idx, "Disallowed `export` namespace wrapper"))
        if re.search(r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*def\s+\w+.*:\s*Prop\s*:=", code):
            violations.append((filepath, idx, "Disallowed `Prop`-valued `def` wrapper"))
        if forbid_structures and re.match(r"^\s*(?:private\s+|protected\s+)*structure\s+", code):
            violations.append((filepath, idx, "Disallowed `structure` wrapper in theorem-only module"))
        if re.search(
            r"^\s*(?:protected\s+|private\s+|noncomputable\s+)*(?:theorem|lemma)\s+\w+.*:=\s*(?:by\s+)?rfl\b",
            code,
        ):
            violations.append((filepath, idx, "Disallowed `:= rfl` trivial theorem wrapper"))

    matches = list(THEOREM_DECL_RE.finditer(text))
    for i, m in enumerate(matches):
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        block = text[start:end]
        decl_kind = m.group(1)
        decl_name = m.group(2)
        line_no = text[:start].count("\n") + 1
        if ":=" in block:
            body = block.split(":=", 1)[1]
            if not DERIVATION_TACTIC_RE.search(body):
                violations.append(
                    (
                        filepath,
                        line_no,
                        f"Pass-through wrapper {decl_kind} '{decl_name}' lacks derivation tactics",
                    )
                )

    if check_docstrings:
        violations.extend(audit_docstrings_file(filepath))

    return violations


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Audit Lean files for wrapper-free genuine lemmas/theorems and 3-bucket headers."
    )
    parser.add_argument(
        "paths",
        nargs="+",
        help="Lean files or directories to audit.",
    )
    parser.add_argument(
        "--no-require-buckets",
        action="store_true",
        help="Skip requiring BUCKET 1/2/3 headers (useful for legacy core modules).",
    )
    parser.add_argument(
        "--forbid-structures",
        action="store_true",
        help="Flag any `structure` declaration in the target files.",
    )
    parser.add_argument(
        "--no-docstrings",
        action="store_true",
        help="Skip per-declaration `/-- ... -/` docstring checks.",
    )
    args = parser.parse_args(argv)

    files = iter_target_files(args.paths)
    all_violations: List[Tuple[str, int, str]] = []
    for f in files:
        all_violations.extend(
            audit_no_wrappers_file(
                str(f),
                require_buckets=not args.no_require_buckets,
                forbid_structures=args.forbid_structures,
                check_docstrings=not args.no_docstrings,
            )
        )

    if all_violations:
        print(f"Found {len(all_violations)} wrapper/docstring violation(s):\n")
        print_grouped_violations(
            all_violations,
            item_formatter=lambda ln, msg: f"  Line {ln}: {msg}",
        )
        return 1

    print(
        f"✓ No-Wrapper & Docstring Audit: {len(files)} file(s) passed cleanly "
        "(0 exports, 0 Prop-defs, 0 rfl wrappers, 0 passthrough wrappers)."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
