#!/usr/bin/env python3
"""Repo-wide maintained-source search for Hestenes/Krein complex-axis surfaces.

Read-only scanner. It prunes generated/cache/vendor directories during traversal
and writes a machine-readable inventory used before proposing any new theorem/code surface.
"""
from __future__ import annotations
from pathlib import Path
import json
import os
import re

REPO = Path(__file__).resolve().parents[3]
ROOT = Path(__file__).resolve().parent
OUT = ROOT / os.environ.get("HK_SEARCH_OUT", "deep_search_inventory.json")
DEFAULT_MAINTAINED_ROOTS = [
    "lean", "lib", "tools", "scripts", "tests", "docs", "external_refs",
    "lakefile.lean", "README.md", "AGENTS.md", "pyproject.toml", "package.json",
]
_roots_env = os.environ.get("HK_SEARCH_ROOTS")
MAINTAINED_ROOTS = [p for p in _roots_env.split(":") if p] if _roots_env else DEFAULT_MAINTAINED_ROOTS
TEXT_EXT = {
    ".lean", ".py", ".sage", ".g", ".gap", ".sing", ".m2", ".v", ".thy",
    ".json", ".md", ".txt", ".aql", ".toml", ".yaml", ".yml", ".sh"
}
SKIP_DIRS = {
    ".git", ".lake", "node_modules", ".venv", ".venv-py312", ".venv_clean",
    ".changes", "build", "dist", "__pycache__", ".mypy_cache", ".pytest_cache",
    ".ruff_cache", ".hermes", "tmp", "artifacts", ".isabelle", ".stack-work"
}
TERMS = [
    "complex_i", "modular_j", "spectral_epsilon", "clockAxis", "HestenesI",
    "complexModule", "complexSMul", "RealKVect", "complexI_smul_eq_K",
    "hestenesScalar", "hestenesCoeff", "CommutesWithHestenesK", "IsPhaseLinear",
    "hestenesCommutator", "modularDerivation", "IsMonogenic",
    "Bivector", "bivector", "doubledIBivector", "doubledI", "Rotor", "rotor",
    "K_sq", "complex_i_sq", "square_neg", "sq_neg", "squares to", "square-minus-one",
    "Cl11", "Cl(1,1)", "splitQ11", "pseudoscalar", "Pseudoscalar",
    "KreinHestenesModularDatum", "modularGenerator", "fundamentalSymmetry"
]
DECL_RE = re.compile(
    r"^\s*(?:@[^\n]*\s*)*"
    r"(?:(?:noncomputable|private|protected|partial)\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|instance)\s+([A-Za-z0-9_'.]+)"
)
TERM_RE = re.compile("|".join(re.escape(t) for t in TERMS), re.IGNORECASE)
NAME_KEYS = ("complex", "hestenes", "krein", "bivector", "rotor", "cl11", "modular", "monogenic", "epsilon", "pseudoscalar")

def candidate_files():
    for root_name in MAINTAINED_ROOTS:
        root = REPO / root_name
        if not root.exists():
            continue
        if root.is_file():
            yield root
            continue
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = [d for d in dirnames if d not in SKIP_DIRS]
            for fn in filenames:
                p = Path(dirpath) / fn
                if p.suffix in TEXT_EXT:
                    yield p

records = []
scanned = 0
for path in candidate_files():
    rel = path.relative_to(REPO)
    try:
        if path.stat().st_size > 1_500_000:
            continue
        text = path.read_text(errors="replace")
    except Exception as exc:
        records.append({"file": str(rel), "error": repr(exc)})
        continue
    scanned += 1
    hits = []
    decls = []
    for i, line in enumerate(text.splitlines(), 1):
        m = TERM_RE.search(line)
        if m:
            hits.append({"line": i, "term": m.group(0), "text": line.strip()[:260]})
        d = DECL_RE.match(line)
        if d:
            decls.append({"line": i, "kind": d.group(1), "name": d.group(2)})
    if hits:
        records.append({
            "file": str(rel),
            "hit_count": len(hits),
            "hits": hits[:80],
            "decls_nearby": [d for d in decls if any(abs(d["line"] - h["line"]) <= 8 for h in hits)][:80],
            "all_matching_decls": [d for d in decls if any(k in d["name"].lower() for k in NAME_KEYS)][:120],
        })

records.sort(key=lambda r: (r.get("hit_count", 0), len(r.get("all_matching_decls", []))), reverse=True)
OUT.write_text(json.dumps({"repo": str(REPO), "scanned_files": scanned, "terms": TERMS, "records": records}, indent=2, ensure_ascii=False))
print(f"DEEP_SEARCH_INVENTORY_OK scanned={scanned} records={len(records)} out={OUT}")
for rec in records[:40]:
    print(f"{rec['hit_count']:4d} {rec['file']}")
