#!/usr/bin/env python3
"""
ShapeHash-to-Lean Bridge

Queries ArangoDB (port 8530, infogeometry) for top shapeHash clusters,
extracts canonical nodes, and generates Lean proposals for handover/injections/.
"""

import json
import os
import sys
from pathlib import Path
from arango.client import ArangoClient

# ─── Config ───
ARANGO_HOST = "http://127.0.0.1:8530"
ARANGO_DB = "infogeometry"
ARANGO_USER = "root"
ARANGO_PASS = "alexandria_root"
OUT_DIR = Path("/home/goutev/repos/info-geometry-lean/handover/injections/shapehash_bridge")
TOP_N = 20  # number of clusters to process
MIN_COUNT = 5  # minimum cluster size

# ─── Connect ───
client = ArangoClient(hosts=ARANGO_HOST)
db = client.db(ARANGO_DB, username=ARANGO_USER, password=ARANGO_PASS)

# ─── Query: top shapeHash clusters ───
CLUSTER_QUERY = """
FOR doc IN dag_nodes
  FILTER doc.valueFingerprint != null
  COLLECT hash = doc.valueFingerprint.shapeHash INTO group
  LET count = LENGTH(group)
  FILTER count >= @min_count
  SORT count DESC
  LIMIT @top_n
  RETURN {
    hash: hash,
    count: count,
    samples: (FOR g IN group LIMIT 5 RETURN {
      name: g.doc.name,
      module: g.module,
      file: g.file,
      line: g.line,
      kind: g.kind,
      typeFingerprint: g.typeFingerprint,
      valueFingerprint: g.valueFingerprint
    })
  }
"""

# ─── Get full source for a node ───
SOURCE_QUERY = """
FOR doc IN dag_nodes
  FILTER doc.valueFingerprint != null AND doc.valueFingerprint.shapeHash == @hash
  LIMIT 1
  RETURN {
    name: doc.doc.name,
    module: doc.module,
    file: doc.file,
    line: doc.line,
    kind: doc.kind,
    typeFingerprint: doc.typeFingerprint,
    valueFingerprint: doc.valueFingerprint,
    attrs: doc.attrs
  }
"""

def read_lean_source(file_path: str, line: int, context: int = 15) -> str:
    """Read Lean source around the given line."""
    try:
        full_path = Path("/home/goutev/repos/info-geometry-lean") / file_path
        if not full_path.exists():
            # Try without lean/ prefix
            full_path = Path("/home/goutev/repos/info-geometry-lean/lean") / file_path
        if not full_path.exists():
            return f"-- File not found: {file_path}"
        lines = full_path.read_text().splitlines()
        start = max(0, line - context - 1)
        end = min(len(lines), line + context)
        return "\n".join(f"{i+1:4} | {lines[i]}" for i in range(start, end))
    except Exception as e:
        return f"-- Error reading source: {e}"

def generate_proposal(cluster: dict, canonical: dict, source: str) -> str:
    """Generate a Lean proposal document for the cluster."""
    hash_val = cluster['hash']
    count = cluster['count']
    module = canonical['module']
    file_path = canonical['file']
    line = canonical['line']
    kind = canonical['kind']
    name = canonical['name'] or f"anon_{hash_val}_{line}"

    # Determine proposal type
    if "sorry" in str(name).lower() or "cert" in str(name).lower():
        prop_type = "SORRY_CERT_CLUSTER"
        desc = f"Cluster of {count} structurally identical `sorry`/`cert` fields. Canonical at {module}:{line}."
    elif count > 500:
        prop_type = "CROSS_DOMAIN_ISOMORPHISM"
        desc = f"Cluster of {count} nodes across multiple domains sharing identical AST shape. Canonical at {module}:{line}."
    else:
        prop_type = "STRUCTURAL_DUPLICATE"
        desc = f"Cluster of {count} structurally duplicate nodes. Canonical at {module}:{line}."

    proposal = f"""# ShapeHash Cluster Proposal

**Hash:** `{hash_val}`
**Count:** {count}
**Type:** {prop_type}
**Canonical Location:** `{module}:{line}` (`{kind}`: `{name}`)
**Source File:** `{file_path}`

## Description
{desc}

## Canonical Source (Lean)
```lean4
{source}
```

## Cluster Samples
"""
    for i, sample in enumerate(cluster['samples'][:5]):
        proposal += f"\n### Sample {i+1}: `{sample['module']}:{sample['line']}` (`{sample['kind']}`)\n"
        proposal += f"**Name:** `{sample['name'] or 'anonymous'}`\n\n"

    proposal += f"""
## Suggested Action
"""
    if prop_type == "SORRY_CERT_CLUSTER":
        proposal += """1. **Canonize**: Replace all cluster members with a single shared axiom/structure field.
2. **Lean Refactor**: Introduce a shared `class SorryCert` or `structure Cert` in a common namespace.
3. **Import**: All affected files `import` the canonical definition.
4. **Delete**: Remove 3,731 duplicate `_cert : Prop` fields.
"""
    elif prop_type == "CROSS_DOMAIN_ISOMORPHISM":
        proposal += """1. **Unify**: Extract the common lemma statement from the canonical shape.
2. **Generalize**: Parameterize over the domain-specific types (State, Entropy, Weyl, etc.).
3. **Prove Once**: Provide a single proof in a shared `Canonical` module.
4. **Specialize**: Each domain imports and instantiates the general lemma.
"""
    else:
        proposal += """1. **Deduplicate**: Identify if these are genuine duplicates or coincidental shape matches.
2. **Refactor**: If duplicates, consolidate to a single definition.
3. **Document**: If distinct but isomorphic, add cross-references.
"""

    proposal += f"""
---
*Generated by ShapeHash-to-Lean Bridge*
*Cluster hash: `{hash_val}` | Count: {count} | Canonical: {module}:{line}*
"""
    return proposal

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    print(f"Querying top {TOP_N} clusters (min_count={MIN_COUNT})...")
    clusters = list(db.aql.execute(CLUSTER_QUERY, bind_vars={"top_n": TOP_N, "min_count": MIN_COUNT}))
    print(f"Found {len(clusters)} clusters.")

    summary = {
        "generated_at": "2026-06-24",
        "total_clusters": len(clusters),
        "total_nodes": sum(c['count'] for c in clusters),
        "proposals": []
    }

    for cluster in clusters:
        hash_val = cluster['hash']
        print(f"\nProcessing cluster {hash_val} (count={cluster['count']})...")

        # Get canonical node (first sample)
        canonical = cluster['samples'][0]

        # Get full source
        canonical_detail = next(db.aql.execute(SOURCE_QUERY, bind_vars={"hash": hash_val}))
        source = read_lean_source(canonical_detail['file'], canonical_detail['line'])

        # Generate proposal
        proposal_md = generate_proposal(cluster, canonical_detail, source)

        # Write proposal
        safe_hash = str(hash_val).replace('-', 'n')
        out_file = OUT_DIR / f"shapehash_{safe_hash}_{cluster['count']}x.md"
        out_file.write_text(proposal_md)
        print(f"  → Written: {out_file}")

        summary["proposals"].append({
            "hash": hash_val,
            "count": cluster['count'],
            "canonical_module": canonical['module'],
            "canonical_line": canonical['line'],
            "proposal_file": str(out_file.relative_to(OUT_DIR.parent.parent)),
            "type": "SORRY_CERT_CLUSTER" if "sorry" in str(canonical['name']).lower() or "cert" in str(canonical['name']).lower() else ("CROSS_DOMAIN_ISOMORPHISM" if cluster['count'] > 500 else "STRUCTURAL_DUPLICATE")
        })

    # Write summary index
    index_file = OUT_DIR / "INDEX.json"
    index_file.write_text(json.dumps(summary, indent=2))
    print(f"\nSummary index: {index_file}")

    # Also write a human-readable index
    index_md = OUT_DIR / "INDEX.md"
    md_content = "# ShapeHash Bridge Proposals Index\n\n"
    md_content += f"**Generated:** {summary['generated_at']}\n"
    md_content += f"**Total Clusters:** {summary['total_clusters']}\n"
    md_content += f"**Total Nodes Covered:** {summary['total_nodes']}\n\n"
    md_content += "| Hash | Count | Type | Canonical Location | Proposal |\n"
    md_content += "|------|-------|------|-------------------|----------|\n"
    for p in summary['proposals']:
        md_content += f"| `{p['hash']}` | {p['count']} | {p['type']} | `{p['canonical_module']}:{p['canonical_line']}` | [`{p['proposal_file']}`]({p['proposal_file']}) |\n"
    index_md.write_text(md_content)
    print(f"Markdown index: {index_md}")

    print("\n✅ ShapeHash-to-Lean Bridge complete.")
    print(f"Proposals written to: {OUT_DIR}")

if __name__ == "__main__":
    main()