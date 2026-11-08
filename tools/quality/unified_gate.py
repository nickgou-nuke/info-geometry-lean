#!/usr/bin/env python3
"""Fail-fast composition of repository placeholder/vacuity/mathfulness/hollow audits."""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_SOURCE_ROOT = "src/InfoGeometry" if (ROOT / "src/InfoGeometry").is_dir() else "lean/InfoGeometry"
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected|scoped|local)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|axiom|opaque)\s+([A-Za-z0-9_'.«»]+)"
)


def extract_live_decls(paths: list[str], out_jsonl: Path) -> None:
    rows: list[str] = []
    for rel_str in paths:
        full = ROOT / rel_str
        if not full.is_file():
            continue
        for idx, line in enumerate(full.read_text(encoding="utf-8", errors="ignore").splitlines(), start=1):
            m = DECL_RE.match(line)
            if m:
                rows.append(
                    json.dumps(
                        {"name": m.group(2), "kind": m.group(1), "file": rel_str, "line": idx}
                    )
                )
    out_jsonl.write_text("\n".join(rows) + ("\n" if rows else ""), encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", help="Optional explicit Lean files or directories to audit")
    ap.add_argument("--root", default=DEFAULT_SOURCE_ROOT, help="Lean source root for full audit")
    ap.add_argument("--changed-from", help="Git base for changed Lean scope")
    ap.add_argument("--changed-to", default="HEAD")
    ap.add_argument("--incremental", action="store_true", help="compatibility alias for changed-range mode")
    ap.add_argument("--base", help="compatibility alias for --changed-from")
    ap.add_argument("--head", help="compatibility alias for --changed-to")
    ap.add_argument("--all", action="store_true", help="audit --root rather than the changed range")
    ns = ap.parse_args()
    changed_from = ns.changed_from or ns.base
    changed_to = ns.head or ns.changed_to
    if ns.paths:
        files = ns.paths
    elif ns.all:
        files = None
    elif changed_from:
        diff = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", changed_from, changed_to, "--", "lean", "src"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
        )
        files = [p for p in diff.stdout.splitlines() if p.endswith(".lean") and (ROOT / p).is_file()]
    else:
        diff = subprocess.run(
            ["git", "diff", "--name-only", "--diff-filter=ACMRTUXB", "HEAD", "--", "lean", "src"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
        )
        files = [p for p in diff.stdout.splitlines() if p.endswith(".lean") and (ROOT / p).is_file()]
    if files == []:
        print("unified gate: no changed Lean files; nothing selected")
        return 0
    scope = files or [ns.root]
    checks = [
        ("placeholder audit", [sys.executable, "tools/quality/placeholder_audit.py", "--strict", "--root", path])
        for path in scope
    ]
    checks.append(
        ("semantic vacuity audit", [sys.executable, "tools/quality/semantic_vacuity_gate.py", "--fail-on", "error", *scope])
    )
    tmp_decls = Path(tempfile.gettempdir()) / "info-geometry-unified-gate-decls.jsonl"
    math = [
        sys.executable,
        "tools/quality/mathfulness_audit.py",
        "--gate",
        "--fail-class",
        "blocked",
        "--fail-class",
        "explicit_axiom",
        "--json-out",
        "/tmp/info-geometry-mathfulness-unified.json",
        "--md-out",
        "/tmp/info-geometry-mathfulness-unified.md",
    ]
    if files is not None:
        extract_live_decls(files, tmp_decls)
        math += ["--decls", str(tmp_decls)]
    else:
        math += ["--file-prefix", ns.root]
    checks.append(("mathfulness audit", math))
    checks.append(
        ("hollow theorem detector", [sys.executable, "tools/quality/detect_hollow_theorems.py", "--strict", *scope])
    )
    for label, command in checks:
        print(f"[unified-gate] {label}", flush=True)
        result = subprocess.run(command, cwd=ROOT, check=False)
        if result.returncode:
            print(f"[unified-gate] FAIL: {label} (exit {result.returncode})", file=sys.stderr)
            return result.returncode
    print("unified gate: all 4 blocking checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
