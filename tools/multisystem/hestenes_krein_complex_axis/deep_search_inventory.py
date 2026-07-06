#!/usr/bin/env python3
"""Repo-wide maintained-source search for Hestenes/Krein complex-axis surfaces.

Read-only scanner. It excludes generated/cache/vendor directories and writes a
machine-readable inventory used before proposing any new theorem/code surface.
"""
from __future__ import annotations
from pathlib import Path
import json
import re

REPO = Path(__file__).resolve().parents[3]
ROOT = Path(__file__).resolve().parent
OUT = ROOT / "deep_search_inventory.json"
TEXT_EXT = {
    ".lean", ".py", ".sage", ".g", ".gap", ".sing", ".m2", ".v", ".thy",
    ".json", ".md", ".txt", ".aql", ".toml", ".yaml", ".yml", ".sh"
}
SKIP_PARTS = {
    ".git", ".lake", "node_modules", ".venv", ".venv-py312", ".venv_clean",
    ".changes", "build", "dist", "__pycache__", ".mypy_cache", ".pytest_cache",
    ".ruff_cache", ".hermes", "tmp", "artifacts"
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

records = []
for path in REPO.rglob("*"):
    if not path.is_file():
        continue
    rel = path.relative_to(REPO)
    if any(part in SKIP_PARTS for part in rel.parts):
        continue
    if path.suffix not in TEXT_EXT:
        continue
    try:
        if path.stat().st_size > 1_500_000:
            continue
        text = path.read_text(errors="replace")
    except Exception as exc:
        records.append({"file": str(rel), "error": repr(exc)})
        continue
    lines = text.splitlines()
    hits = []
    decls = []
    for i, line in enumerate(lines, 1):
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
            "hits": hits[:40],
            "decls_nearby": [d for d in decls if any(abs(d["line"] - h["line"]) <= 8 for h in hits)][:40],
            "all_matching_decls": [d for d in decls if any(t.lower() in d["name"].lower() for t in ["complex", "hestenes", "krein", "bivector", "rotor", "cl11", "modular", "monogenic"] )][:80],
        })

records.sort(key=lambda r: (r.get("hit_count", 0), len(r.get("all_matching_decls", []))), reverse=True)
OUT.write_text(json.dumps({"repo": str(REPO), "terms": TERMS, "records": records}, indent=2, ensure_ascii=False))
print(f"DEEP_SEARCH_INVENTORY_OK records={len(records)} out={OUT}")
for rec in records[:30]:
    print(f"{rec['hit_count']:4d} {rec['file']}")
