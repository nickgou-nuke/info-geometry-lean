#!/usr/bin/env python3
"""Detect archetypal patterns that recur across the repository.

An archetype is a formal pattern (operator algebra, proof structure, theorem
signature) that appears in multiple domains with the same algebraic content.

Outputs:
  - artifacts/archetypes/archetypes.json  — detected archetypes
  - artifacts/archetypes/syntheses.json   — synthesis candidates
"""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
INFO_GEOMETRY = REPO / "lean" / "InfoGeometry"

# Known archetypal operator signatures
ARCHETYPE_SIGNATURES: list[dict] = [
    {
        "name": "tri_facet",
        "keywords": ["O_cubed", "O_sq", "d_mul_δ", "δ_mul_d", "Δ_H_zero", "d_add_δ_eq_one"],
        "signature": "O³ = O, d = (I+O)/2, δ = (I-O)/2, Δ_H = 0, D = I",
    },
    {
        "name": "hodge_laplacian",
        "keywords": ["hodgeLaplacian", "future_past_zero", "past_future_zero", "hodge_laplacian_zero"],
        "signature": "Δ_H = dδ + δd = 0, D = d + δ = I",
    },
    {
        "name": "hodge_star",
        "keywords": ["hodgeStar", "hodgeStar_involutive", "stokes_krein_harmonic"],
        "signature": "⋆² = I, ⟨⋆x, ⋆y⟩ = ⟨x, y⟩",
    },
    {
        "name": "tri_facet_projector",
        "keywords": ["exact_projector", "coexact_projector", "harmonic_projector"],
        "signature": "P_ex = (I+O)/2, P_coex = (I-O)/2, P_harm = I - O²",
    },
]


def scan_declarations() -> dict[str, list[str]]:
    """Map theorem/def names to list of files they appear in."""
    decls = defaultdict(list)
    for root, _dirs, files in os.walk(INFO_GEOMETRY):
        for f in files:
            if not f.endswith(".lean"):
                continue
            path = Path(root) / f
            rel = str(path.relative_to(REPO))
            try:
                content = path.read_text(encoding="utf-8")
            except Exception:
                continue
            for m in re.finditer(r'(theorem|def)\s+(\w+)', content):
                decls[m.group(2)].append(rel)
    return dict(decls)


def detect_archetypes(decls: dict[str, list[str]]) -> list[dict]:
    """Detect archetypal patterns from multi-file declarations."""
    archetypes = []
    
    for signature in ARCHETYPE_SIGNATURES:
        name = signature["name"]
        keywords = signature["keywords"]
        
        # Find which keywords appear in which files
        keyword_files: dict[str, set[str]] = {}
        for kw in keywords:
            if kw in decls:
                keyword_files[kw] = set(decls[kw])
        
        if not keyword_files:
            continue
        
        # All files that contain any of these keywords
        all_files = set()
        for files in keyword_files.values():
            all_files.update(files)
        
        # Count how many keywords each file has
        file_scores = {}
        for f in all_files:
            score = sum(1 for kw, files in keyword_files.items() if f in files)
            if score >= 1:
                file_scores[f] = score
        
        # Sort by score
        ranked = sorted(file_scores.items(), key=lambda x: x[1], reverse=True)
        
        archetype = {
            "name": name,
            "signature": signature["signature"],
            "keywords_found": list(keyword_files.keys()),
            "keyword_count": len(keyword_files),
            "total_files": len(all_files),
            "top_files": [{"file": f, "match_count": s} for f, s in ranked[:10]],
        }
        archetypes.append(archetype)
    
    return archetypes


def find_synthesis_candidates(archetypes: list[dict]) -> list[dict]:
    """Generate synthesis candidates from archetype data."""
    candidates = []
    
    for arch in archetypes:
        if arch["total_files"] < 2:
            continue
        
        # Each pair of top files is a synthesis candidate
        top = arch["top_files"][:5]
        for i in range(len(top)):
            for j in range(i + 1, len(top)):
                candidate = {
                    "archetype": arch["name"],
                    "thesis": top[i]["file"],
                    "antithesis": top[j]["file"],
                    "thesis_score": top[i]["match_count"],
                    "antithesis_score": top[j]["match_count"],
                    "signature": arch["signature"],
                    "hash": hashlib.sha256(
                        f'{arch["name"]}:{top[i]["file"]}:{top[j]["file"]}'.encode()
                    ).hexdigest()[:12],
                }
                candidates.append(candidate)
    
    return candidates


def main():
    decls = scan_declarations()
    archetypes = detect_archetypes(decls)
    candidates = find_synthesis_candidates(archetypes)
    
    out_dir = REPO / "artifacts" / "archetypes"
    out_dir.mkdir(parents=True, exist_ok=True)
    
    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "archetype_count": len(archetypes),
        "candidate_count": len(candidates),
        "archetypes": archetypes,
        "synthesis_candidates": candidates,
    }
    
    with open(out_dir / "archetypes.json", "w") as f:
        json.dump(report, f, indent=2)
    
    print(f"Detected {len(archetypes)} archetypes, {len(candidates)} synthesis candidates")
    for arch in archetypes:
        print(f"  {arch['name']}: {arch['keyword_count']} keywords in {arch['total_files']} files")
        for tf in arch["top_files"][:3]:
            print(f"    {tf['file']} ({tf['match_count']} matches)")
    print(f"\nOutput: {out_dir}/")


if __name__ == "__main__":
    main()
