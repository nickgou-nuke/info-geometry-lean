#!/usr/bin/env python3
"""Canonicalize ExtractGraph proof_graph.json for audits/GEPA-style optimizers.

This emits a derived JSON with stable ordering, deduplicated dependencies, and
lightweight canonical/vacuity hints.  Optionally it also runs the repository's
Lean vacuity linter over matching source files to attach real codebase-level
honesty signals to each module.

The kernel graph is never rewritten.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent
while not (REPO_ROOT / "scripts" / "vacuity-linter.py").exists() and REPO_ROOT.parent != REPO_ROOT:
    REPO_ROOT = REPO_ROOT.parent
if not (REPO_ROOT / "scripts" / "vacuity-linter.py").exists():
    REPO_ROOT = Path(__file__).resolve().parents[3]

DEFAULT_LEAN_ROOT = REPO_ROOT / "proofs"
DEFAULT_VACUITY_LINTER = REPO_ROOT / "scripts" / "vacuity-linter.py"

AUTO_SUFFIX_RE = re.compile(
    r"\.(rec|recOn|casesOn|ctorIdx|ctorElim|ctorElimType|noConfusion|noConfusionType|below|ibelow|brecOn)$"
)
AUTO_FRAGMENT_RE = re.compile(
    r"(\._proof_\d+$|\.eq_\d+$|\.match_\d+$|\.injEq$|\.sizeOf_spec$|\._sizeOf_\d+$|\._flat_ctor$|\.congr_simp$|\.ofNat_ctorIdx$)"
)


def unique_preserve_order(xs: list[str]) -> tuple[list[str], int]:
    seen: set[str] = set()
    out: list[str] = []
    dup_count = 0
    for x in xs:
        if x in seen:
            dup_count += 1
            continue
        seen.add(x)
        out.append(x)
    return out, dup_count


def is_auto_generated(name: str) -> bool:
    return bool(AUTO_SUFFIX_RE.search(name) or AUTO_FRAGMENT_RE.search(name))


def module_name(name: str) -> str:
    return name.split(".", 1)[0] if name else ""


def module_lean_files(lean_root: Path, module: str) -> list[Path]:
    if not module:
        return []
    if not lean_root.exists():
        return []
    matches = sorted({p.resolve() for p in lean_root.rglob(f"{module}.lean")})
    return matches


def run_vacuity_linter(linter: Path, path: Path, timeout: float = 60.0) -> dict[str, Any]:
    if not linter.exists() or not path.exists():
        return {
            "file": str(path),
            "exists": path.exists(),
            "scanned": False,
            "honesty_score": None,
            "vacuity_score": None,
            "findings": [],
            "error": "missing_linter_or_file",
        }
    proc = subprocess.run(
        [sys.executable, str(linter), "--json", str(path)],
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )
    if proc.returncode != 0:
        return {
            "file": str(path),
            "exists": True,
            "scanned": False,
            "honesty_score": None,
            "vacuity_score": None,
            "findings": [],
            "error": (proc.stderr or proc.stdout or "vacuity_linter_failed").strip(),
        }
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {
            "file": str(path),
            "exists": True,
            "scanned": False,
            "honesty_score": None,
            "vacuity_score": None,
            "findings": [],
            "error": "vacuity_linter_returned_non_json",
        }
    payload["file"] = str(path)
    payload["exists"] = True
    payload["scanned"] = True
    return payload


def vacuity_hint(
    name: str,
    kind: str,
    dep_count: int,
    module_vacuity_score: float | None,
    auto: bool,
) -> str:
    if auto:
        return "auto_generated_helper"
    if module_vacuity_score is not None and module_vacuity_score >= 0.7:
        return "module_vacuity_review_required"
    if kind == "theorem" and dep_count == 0:
        return "zero_dep_user_theorem_check_source"
    if kind in {"def", "other", "inductive"} and dep_count == 0:
        return "zero_dep_constructor_or_base_decl"
    if kind == "theorem" and dep_count <= 2:
        return "small_dep_theorem_review_if_capstone"
    if name.endswith("Socket") or ".Socket." in name:
        return "socket_boundary"
    return "ordinary"


def canonicalize(
    records: list[dict[str, Any]],
    *,
    lean_root: Path | None = None,
    vacuity_linter: Path | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    lean_root = DEFAULT_LEAN_ROOT if lean_root is None else lean_root
    vacuity_linter = DEFAULT_VACUITY_LINTER if vacuity_linter is None else vacuity_linter

    module_files_cache: dict[str, list[Path]] = {}
    module_vacuity_cache: dict[str, dict[str, Any]] = {}
    file_vacuity_cache: dict[str, dict[str, Any]] = {}

    def module_vacuity(module: str) -> dict[str, Any]:
        if module in module_vacuity_cache:
            return module_vacuity_cache[module]
        files = module_files_cache.get(module)
        if files is None:
            files = module_lean_files(lean_root, module)
            module_files_cache[module] = files
        reports: list[dict[str, Any]] = []
        for file in files:
            key = str(file)
            report = file_vacuity_cache.get(key)
            if report is None:
                report = run_vacuity_linter(vacuity_linter, file)
                file_vacuity_cache[key] = report
            reports.append(report)
        vac_scores = [float(r["vacuity_score"]) for r in reports if isinstance(r.get("vacuity_score"), (int, float))]
        hon_scores = [float(r["honesty_score"]) for r in reports if isinstance(r.get("honesty_score"), (int, float))]
        findings: list[dict[str, Any]] = []
        for report in reports:
            for finding in report.get("findings", []):
                findings.append({**finding, "file": report.get("file")})
        if vac_scores:
            chosen = max(vac_scores)
            honesty = min(hon_scores) if hon_scores else None
        else:
            chosen = None
            honesty = None
        result = {
            "module": module,
            "lean_files": [str(p) for p in files],
            "files_scanned": len(reports),
            "vacuity_score": chosen,
            "honesty_score": honesty,
            "findings": findings,
        }
        module_vacuity_cache[module] = result
        return result

    out: list[dict[str, Any]] = []
    duplicate_edges = 0
    auto_count = 0
    zero_dep_theorems = 0
    kinds: dict[str, int] = {}
    modules: dict[str, int] = {}

    for r in records:
        name = str(r.get("name", ""))
        kind = str(r.get("kind", "unknown"))
        deps_raw = [str(d) for d in r.get("deps", [])]
        deps, dup_count = unique_preserve_order(deps_raw)
        duplicate_edges += dup_count
        module = module_name(name)
        auto = is_auto_generated(name)
        if auto:
            auto_count += 1
        if kind == "theorem" and not deps and not auto:
            zero_dep_theorems += 1
        kinds[kind] = kinds.get(kind, 0) + 1
        modules[module] = modules.get(module, 0) + 1

        mod_vacuity = module_vacuity(module)
        vac_score = mod_vacuity.get("vacuity_score")
        hon_score = mod_vacuity.get("honesty_score")
        out.append({
            "name": name,
            "module": module,
            "kind": kind,
            "deps": deps,
            "dep_count": len(deps),
            "duplicate_dep_count": dup_count,
            "auto_generated_hint": auto,
            "vacuity_hint": vacuity_hint(name, kind, len(deps), vac_score if isinstance(vac_score, (int, float)) else None, auto),
            "lean_files": mod_vacuity.get("lean_files", []),
            "module_vacuity_score": vac_score,
            "module_honesty_score": hon_score,
            "module_vacuity_findings": mod_vacuity.get("findings", []),
        })

    out.sort(key=lambda r: r["name"])
    vacuity_modules = [r for r in out if isinstance(r.get("module_vacuity_score"), (int, float))]
    unique_vacuity: dict[str, dict[str, Any]] = {}
    for r in vacuity_modules:
        module = r["module"]
        score = float(r["module_vacuity_score"])
        current = unique_vacuity.get(module)
        candidate = {
            "module": module,
            "score": score,
            "findings": len(r.get("module_vacuity_findings", [])),
            "files": r.get("lean_files", []),
        }
        if current is None or score > float(current["score"]):
            unique_vacuity[module] = candidate
    high_risk = sorted(unique_vacuity.values(), key=lambda x: (-float(x["score"]), x["module"]))

    summary = {
        "declarations": len(out),
        "modules": len(modules),
        "kinds": dict(sorted(kinds.items())),
        "duplicate_edges_removed": duplicate_edges,
        "auto_generated_hint_count": auto_count,
        "zero_dep_user_theorem_count": zero_dep_theorems,
        "files_scanned": len(file_vacuity_cache),
        "modules_scanned_for_vacuity": len(module_vacuity_cache),
        "modules_with_vacuity_reports": len(unique_vacuity),
        "top_modules_by_decl_count": sorted(
            ({"module": m, "decls": c} for m, c in modules.items()),
            key=lambda x: (-x["decls"], x["module"]),
        )[:30],
        "top_vacuity_modules": high_risk[:30],
    }
    return out, summary


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path, nargs="?", default=Path("proof_graph.json"))
    ap.add_argument("--out", type=Path, default=Path("tools/lean_graph/out/proof_graph.canonical.json"))
    ap.add_argument("--summary", type=Path, default=Path("tools/lean_graph/out/proof_graph.canonical.summary.json"))
    ap.add_argument("--lean-root", type=Path, default=DEFAULT_LEAN_ROOT)
    ap.add_argument("--vacuity-linter", type=Path, default=DEFAULT_VACUITY_LINTER)
    ap.add_argument("--skip-vacuity-scan", action="store_true")
    args = ap.parse_args()

    records = json.loads(args.input.read_text(encoding="utf-8"))
    if not isinstance(records, list):
        raise SystemExit("expected proof graph JSON array")
    lean_root = None if args.skip_vacuity_scan else args.lean_root
    vacuity_linter = None if args.skip_vacuity_scan else args.vacuity_linter
    canonical, summary = canonicalize(records, lean_root=lean_root, vacuity_linter=vacuity_linter)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(canonical, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    args.summary.write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {len(canonical)} canonical declarations to {args.out}")
    print(f"wrote summary to {args.summary}")
    print(json.dumps(summary, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
