#!/usr/bin/env python3
"""Mathlib grounding pipeline for Lean declarations."""

from __future__ import annotations

import argparse
import json
import os
import re
from pathlib import Path
from typing import Any, Optional


PREFIX_HINTS = {
    "GroupTheory": ["Mathlib.GroupTheory.PresentedGroup", "Mathlib.GroupTheory.Subgroup.Basic"],
    "PresentedGroup": ["Mathlib.GroupTheory.PresentedGroup"],
    "Matrix": ["Mathlib.Data.Matrix.Basic", "Mathlib.Data.Matrix.Notation"],
    "Fin": ["Mathlib.Data.Fin.Operations", "Mathlib.Data.Fin.Tuple"],
    "Complex": ["Mathlib.Data.Complex.Basic", "Mathlib.Data.Complex.Exponential"],
    "Nat": ["Mathlib.Data.Nat.Basic", "Mathlib.Data.Nat.Prime"],
    "Real": ["Mathlib.Data.Real.Basic", "Mathlib.Analysis.SpecialFunctions.Trigonometric"],
    "TL": ["Mathlib.Order.Lattice", "Mathlib.Algebra.BigOperators.Basic"],
    "e0": ["Mathlib.Data.Matrix.Basic"],
    "e1": ["Mathlib.Data.Matrix.Basic"],
    "Clifford55": ["Mathlib.LinearAlgebra.CliffordAlgebra.Basic"],
    "Pin": ["Mathlib.LinearAlgebra.CliffordAlgebra.Pin"],
    "Cartan": ["Mathlib.LieAlgebra.UniversalEnveloping"],
    "Casimir": ["Mathlib.LieAlgebra.CartanSubalgebra"],
    "JonesBraidB3": ["Mathlib.AddTorsor", "Mathlib.Data.Matrix.Basic"],
    "B3PresentedGroup": ["Mathlib.GroupTheory.PresentedGroup", "Mathlib.Data.Matrix.Basic"],
    "Set": ["Mathlib.Data.Set.Basic", "Mathlib.SetTheory.Cardinal.Basic"],
    " FiniteDimensional": ["Mathlib.LinearAlgebra.FiniteDimensional"],
    "Module": ["Mathlib.Algebra.Module.Basic", "Mathlib.LinearAlgebra.FiniteDimensional"],
    "Tensor": ["Mathlib.LinearAlgebra.TensorProduct.Basic"],
    "Lie": ["Mathlib.LieAlgebra"],
}

IMPORT_RE = re.compile(r"^\s*import\s+(.+)$")
MATHLIB_MODULE_RE = re.compile(r"Mathlib(?:\.[A-Za-z0-9_.]+)")


def extract_imports(path: Path) -> list[str]:
    imports: list[str] = []
    if not path.exists():
        return imports
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = IMPORT_RE.match(line)
        if not m:
            continue
        raw = m.group(1)
        imports.extend(part.strip() for part in raw.split(",") if part.strip())
    return imports


def mathlib_from_file(path: Path) -> list[str]:
    text = ""
    if path.exists():
        text = path.read_text(encoding="utf-8", errors="replace")
    return sorted(set(MATHLIB_MODULE_RE.findall(text)))


def normalized_from_decl_name(name: str) -> list[str]:
    candidates: list[str] = []
    key = name.replace(".", " ")
    for hint, prefixes in PREFIX_HINTS.items():
        if hint.lower() in key.lower():
            candidates.extend(prefixes)
    return candidates


def file_hints_from_module(module: str) -> list[Path]:
    parts = module.split(".")
    candidates = []
    current = Path(".")
    for part in parts:
        current = current / part
        candidates.append(current.with_suffix(".lean"))
    return candidates


def load_decl_from_arango(host: str, database: str, user: str, password: str, decl_key: str) -> Optional[dict[str, Any]]:
    try:
        from arango import ArangoClient  # type: ignore
    except ImportError as exc:
        raise SystemExit("python-arango is required for ArangoDB lookup") from exc
    client = ArangoClient(hosts=host)
    db = client.db(database, username=user, password=password)
    doc = db.collection("lean_decls").get(decl_key)
    return doc if isinstance(doc, dict) else None


def repo_files_for_decl(decl_doc: dict[str, Any], repo_root: Path) -> list[Path]:
    rel = decl_doc.get("file") or decl_doc.get("doc", {}).get("file") or ""
    if not rel:
        return []
    candidates = [repo_root / rel]
    if decl_doc.get("name"):
        first = str(decl_doc.get("name")).split(".")[0]
        candidates += [repo_root / f"{first}.lean", repo_root / first / f"{first}.lean"]
    if decl_doc.get("module"):
        first = str(decl_doc.get("module")).split(".")[0]
        candidates += [repo_root / f"{first}.lean", repo_root / first / f"{first}.lean"]
    out: list[Path] = []
    seen: set[str] = set()
    for path in candidates:
        if path.exists() and str(path) not in seen:
            seen.add(str(path))
            out.append(path)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Mathlib grounding pipeline.")
    parser.add_argument("--decl", type=str, default=None, help="Lean declaration key to ground.")
    parser.add_argument("--module", type=str, default=None, help="Lean module name to ground.")
    parser.add_argument("--database", type=str, default=os.getenv("ARANGO_DATABASE") or os.getenv("ARANGO_DB") or "info_geometry")
    parser.add_argument("--host", type=str, default=os.getenv("ARANGO_URL") or "http://localhost:8529")
    parser.add_argument("--user", type=str, default=os.getenv("ARANGO_USERNAME") or os.getenv("ARANGO_USER") or "root")
    parser.add_argument("--password", type=str, default=os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS") or "")
    parser.add_argument("--repo-root", type=Path, default=Path("."), help="Repository root")
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    parser.add_argument("--list-known", action="store_true", help="List known mathlib prefixes")
    args = parser.parse_args()

    if args.list_known:
        for path in sorted({p for ps in PREFIX_HINTS.values() for p in ps}):
            print(path)
        return

    if not args.decl and not args.module:
        raise SystemExit("Either --decl or --module is required")

    decl_doc = load_decl_from_arango(args.host, args.database, args.user, args.password, args.decl) if args.decl else None
    decl_name = "unknown"
    module_name = args.module or args.decl or ""
    candidates: list[dict[str, Any]] = []
    existing_files: list[Path] = []
    existing_imports: list[str] = []

    if isinstance(decl_doc, dict):
        decl_name = decl_doc.get("name") or decl_doc.get("doc", {}).get("name") or decl_name
        module_name = decl_doc.get("module") or decl_doc.get("doc", {}).get("module") or module_name
        existing_files = repo_files_for_decl(decl_doc, args.repo_root)
        existing_imports = sorted({imp for path in existing_files for imp in mathlib_from_file(path)})

    candidates.extend(normalized_from_decl_name(decl_name))
    candidates.extend(normalized_from_decl_name(module_name))
    for path in existing_files:
        candidates.extend(mathlib_from_file(path))
    seen_paths: list[str] = []
    seen_set: set[str] = set()
    for prefix in candidates:
        if prefix not in seen_set:
            seen_set.add(prefix)
            seen_paths.append(prefix)
    candidates_out = []
    for prefix in seen_paths:
        candidates_out.append({
            "mathlib_prefix": prefix,
            "confidence": 1,
            "rationale": "source-of-truth import/hint match",
            "suggested_import": prefix,
            "skeleton": "\n".join([f"import {prefix}", f"-- grounding probe for `{decl_name}` via `{prefix}`"]),
        })

    result = {
        "decl_key": args.decl,
        "decl_name": decl_name,
        "module": module_name,
        "existing_imports": existing_imports,
        "existing_files": [str(path) for path in existing_files],
        "candidates": candidates_out[:20],
    }

    if args.json:
        print(json.dumps(result, indent=2, ensure_ascii=True))
        return

    print(f"decl: {result['decl_name']}")
    print(f"module: {result['module']}")
    print("existing_files:")
    for path in result["existing_files"]:
        print(f"  {path}")
    print("existing_imports:")
    for imp in result["existing_imports"]:
        print(f"  {imp}")
    print("mathlib_candidates:")
    for cand in result["candidates"]:
        print(f"  {cand['mathlib_prefix']}")
        print(f"       skeleton:")
        for line in cand["skeleton"].splitlines():
            print(f"         {line}")


if __name__ == "__main__":
    main()
