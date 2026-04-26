#!/usr/bin/env python3
"""
⚖️ THE PAULI AUDITOR: Semantic Fidelity & Hollow Theorem Detector.
"Exploration may be Jungian. Closure must be Pauli."

This tool detects 'hollow' theorems that typecheck but carry no substantive 
mathematical content relative to their advertised claim.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from tools.infra.arango_raw_infotree_ingest import ArangoTarget, request_json, db_url
    from tools.pathing import repo_root
else:
    from tools.infra.arango_raw_infotree_ingest import ArangoTarget, request_json, db_url
    from tools.pathing import repo_root

# --- Audit Configuration ---

HOLLOW_DEFECT_SEVERITY = {
    "trivialIdentity": 3,
    "assumptionEcho": 4,
    "vacuousPremise": 5,
    "emptyDomain": 5,
    "definitionSmuggling": 5,
    "stringTheorem": 4,
    "trivialExistence": 3,
    "typeOnlySupport": 2,
    "simpOnlyNoDomainSupport": 2,
    "unresolvedAxiom": 5,
    "semanticNameMismatch": 4,
}

# Key domain terms to check for semantic mismatch
DOMAIN_KEYWORDS = [
    "spectral", "geometric", "stability", "convergence", "entropy",
    "hamiltonian", "curvature", "flow", "morphism", "isomorphism",
    "boundary", "gauge", "holonomy", "measure", "probability"
]

# --- Detection Heuristics ---

def detect_trivial_identity(name: str, theorem_type: str) -> bool:
    """Detects x = x, P <-> P, etc."""
    # Basic regex for alpha = alpha or P <-> P
    # We strip spaces and look for symmetry around = or <->
    clean_type = re.sub(r'\s+', '', theorem_type)
    
    # Matches (anything) = (same thing) or (anything) <-> (same thing)
    match = re.search(r'(.+)(=|<->)\1$', clean_type)
    return bool(match)

def detect_assumption_echo(theorem_type: str) -> bool:
    """Detects P -> ... -> P."""
    # Split by arrows (rough approximation for Lean)
    parts = [p.strip() for p in re.split(r'->|∀|∃', theorem_type)]
    if len(parts) < 2:
        return False
    
    conclusion = parts[-1]
    hypotheses = parts[:-1]
    
    # If the conclusion is identical to one of the hypotheses
    return any(h == conclusion for h in hypotheses if h)

def detect_vacuous_premise(theorem_type: str) -> bool:
    """Detects False -> P or Empty -> P."""
    return "False" in theorem_type or "Empty" in theorem_type

def detect_semantic_mismatch(name: str, theorem_type: str) -> bool:
    """Detects if impressive name has a trivial type."""
    name_lower = name.lower()
    has_big_name = any(kw in name_lower for kw in DOMAIN_KEYWORDS)
    
    # Trivial types: just equality of simple vars, or very short types
    is_short_type = len(theorem_type) < 15
    is_basic_equality = "=" in theorem_type and len(theorem_type.split("=")) == 2
    
    return has_big_name and (is_short_type or is_basic_equality)

def score_hollow_node(node: dict[str, Any]) -> dict[str, Any]:
    """Calculates hollow score and identifies mechanisms."""
    name = str(node.get("name") or "unknown")
    theorem_type = str(node.get("type") or "")
    kind = str(node.get("kind") or "")
    
    findings = []
    score = 0
    
    proof_deps = node.get("proof_dependencies")
    if node.get("sorry", False) or (proof_deps and "sorryAx" in str(proof_deps)):
        findings.append("unresolvedAxiom")
        score += HOLLOW_DEFECT_SEVERITY["unresolvedAxiom"]
        
    if detect_trivial_identity(name, theorem_type):
        findings.append("trivialIdentity")
        score += HOLLOW_DEFECT_SEVERITY["trivialIdentity"]
        
    if detect_assumption_echo(theorem_type):
        findings.append("assumptionEcho")
        score += HOLLOW_DEFECT_SEVERITY["assumptionEcho"]
        
    if detect_vacuous_premise(theorem_type):
        findings.append("vacuousPremise")
        score += HOLLOW_DEFECT_SEVERITY["vacuousPremise"]
        
    if detect_semantic_mismatch(name, theorem_type):
        findings.append("semanticNameMismatch")
        score += HOLLOW_DEFECT_SEVERITY["semanticNameMismatch"]

    # Basic classification based on score
    if score >= 7:
        classification = "severe"
    elif score >= 4:
        classification = "hollow_candidate"
    elif score >= 2:
        classification = "low_content"
    else:
        classification = "substantive"
        
    return {
        "name": name,
        "score": score,
        "findings": findings,
        "classification": classification,
        "type": theorem_type
    }

# --- Detection Filters ---

GENERATED_NAME_PATTERN = re.compile(r'\.(inj|eq_|sizeOf_spec|drec|rec|casesOn|match_|proof_|to_)', re.I)

def is_generated_lemma(name: str) -> bool:
    return bool(GENERATED_NAME_PATTERN.search(name))

# --- ArangoDB Logic ---

def run_fidelity_audit(target: ArangoTarget) -> list[dict[str, Any]]:
    query = """
    FOR doc IN ig_nodes
      FILTER doc.kind IN ['theorem', 'lemma']
      LIMIT 50
      RETURN {
        name: doc.name,
        type: doc.type,
        kind: doc.kind,
        sorry: doc.sorry,
        proof_dependencies: doc.proof_dependencies
      }
    """
    payload = {"query": query}
    print(f"[pauli-auditor] Executing AQL: {query.strip()}")
    res = request_json("POST", db_url(target, "/_api/cursor"), username=target.username, password=target.password, payload=payload)
    
    if isinstance(res, dict):
        nodes = res.get("result", [])
    else:
        nodes = []
        
    print(f"[pauli-auditor] Fetched {len(nodes)} nodes for audit.")
    
    reports = []
    skipped_generated = 0
    skipped_empty_type = 0
    
    for i, n in enumerate(nodes):
        name = str(n.get("name") or "")
        theorem_type = str(n.get("type") or "")
        
        print(f"[{i+1}/{len(nodes)}] Auditing: {name[:60]}...")
        
        if is_generated_lemma(name):
            skipped_generated += 1
            continue
            
        if not theorem_type:
            skipped_empty_type += 1
            continue
            
        report = score_hollow_node(n)
        if report["score"] > 0:
            print(f"  !! Found hollow pattern: {report['findings']} (Score: {report['score']})")
        reports.append(report)
        
    print(f"[pauli-auditor] Skipped {skipped_generated} generated lemmas and {skipped_empty_type} nodes with missing type data.")
    return reports

# --- Reporting ---

def write_reports(reports: list[dict[str, Any]], out_dir: Path):
    out_dir.mkdir(parents=True, exist_ok=True)
    
    # JSON
    json_path = out_dir / "hollow-audit.json"
    with json_path.open("w") as f:
        json.dump(reports, f, indent=2)
        
    # Markdown
    md_path = out_dir / "hollow-audit.md"
    with md_path.open("w") as f:
        f.write("# Pauli Auditor: Semantic Fidelity & Hollow Theorem Report\n\n")
        f.write(f"Generated at: {datetime.now(timezone.utc).isoformat()}\n\n")
        
        counts = Counter(r["classification"] for r in reports)
        f.write("## Summary\n\n")
        f.write(f"- Total Theorems Audited: {len(reports)}\n")
        f.write(f"- Substantive: {counts['substantive']}\n")
        f.write(f"- Low Content: {counts['low_content']}\n")
        f.write(f"- Hollow Candidates: {counts['hollow_candidate']}\n")
        f.write(f"- Severe Defects: {counts['severe']}\n\n")
        
        f.write("## Findings (Hollow Candidates & Severe)\n\n")
        for r in reports:
            if r["score"] >= 4:
                f.write(f"### `{r['name']}`\n")
                f.write(f"- **Score**: {r['score']}\n")
                f.write(f"- **Classification**: `{r['classification']}`\n")
                f.write(f"- **Findings**: {', '.join(r['findings'])}\n")
                f.write(f"- **Type**: `{r['type']}`\n\n")

# --- CLI ---

def main():
    parser = argparse.ArgumentParser(description="Run the Pauli Semantic Fidelity Auditor.")
    parser.add_argument("--url", default=os.getenv("ARANGO_URL", "http://127.0.0.1:8529"))
    parser.add_argument("--db", default=os.getenv("ARANGO_DATABASE", "infogeometry"))
    parser.add_argument("--user", default=os.getenv("ARANGO_USERNAME", "root"))
    parser.add_argument("--password", default=os.getenv("ARANGO_PASSWORD", ""))
    parser.add_argument("--out", type=Path, default=Path("artifacts/dag"))
    
    args = parser.parse_args()
    
    target = ArangoTarget(args.url, args.db, args.user, args.password)
    
    print("[pauli-auditor] Querying ArangoDB for semantic fidelity audit...")
    try:
        reports = run_fidelity_audit(target)
        write_reports(reports, args.out)
        print(f"[pauli-auditor] Audit complete. Findings in {args.out}/hollow-audit.md")
    except Exception as exc:
        print(f"[pauli-auditor] ERROR: {exc}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()
