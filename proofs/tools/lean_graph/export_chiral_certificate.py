#!/usr/bin/env python3
"""GEPA Chiral tau-Ideal Stability Certificate — machine-generated audit report.

Usage:  python3 tools/lean_graph/export_chiral_certificate.py
Output: tools/lean_graph/out/chiral_stability_certificate.json
        tools/lean_graph/out/chiral_stability_report.md
"""

from __future__ import annotations
import json, os, sys
from datetime import datetime, timezone
from pathlib import Path

try:
    from arango import ArangoClient
except ImportError:
    print("python-arango required: pip install python-arango", file=sys.stderr)
    sys.exit(1)

OUT_DIR = Path(__file__).resolve().parent / "out"
OUT_DIR.mkdir(exist_ok=True)
DB_HOST = os.getenv("ARANGO_URL") or os.getenv("ARANGO_ENDPOINT") or os.getenv("ARANGO_HOST", "http://localhost:8529")
DB_USER = os.getenv("ARANGO_USERNAME") or os.getenv("ARANGO_USER", "root")
DB_PASS = os.getenv("ARANGO_PASSWORD") or os.getenv("ARANGO_PASS", "")
DB_NAME = os.getenv("ARANGO_DATABASE") or os.getenv("ARANGO_DB", "info_geometry")


def connect():
    return ArangoClient(hosts=DB_HOST).db(DB_NAME, username=DB_USER, password=DB_PASS)


def run_queries(db):
    result = {
        "certificate": "chiral-tau-ideal-stability",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "database": DB_NAME,
    }
    # 1. 4-Cell Matrix
    result["four_cell_matrix"] = list(db.aql.execute("""
        FOR decl IN lean_decls
          FILTER decl.name IN [
            "ChiralTLDescent.chiral_left_tau_ideal",
            "ChiralTLDescent.chiral_kernel_is_left_tau_ideal",
            "ChiralTLDescent.chiral_right_tau_ideal",
            "ChiralTLDescent.chiral_right_kernel_tau_ideal"
          ]
          SORT decl.name
          RETURN {
            name: decl.name, kind: decl.kind,
            referenced_by: LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1),
            depends_on: LENGTH(FOR e IN references FILTER e._from == decl._id RETURN 1)
          }
    """))
    # 2. Dependency Spine
    result["dependency_spine"] = list(db.aql.execute("""
        FOR v, e IN 1..5 OUTBOUND "lean_decls/ChiralTLDescent_chiral_left_tau_ideal" references
          COLLECT name = v.name, depth = MIN(LENGTH(e))
          SORT depth, name
          RETURN {name, depth}
    """))
    # 3. Top Lemmas
    result["top_lemmas"] = list(db.aql.execute("""
        FOR edge IN references
          COLLECT target = edge._to WITH COUNT INTO c
          SORT c DESC LIMIT 20
          LET doc = DOCUMENT(target)
          RETURN {name: doc.name, used_by: c}
    """))
    # 4. Sockets
    result["socket_inventory"] = list(db.aql.execute("""
        FOR decl IN lean_decls
          FILTER decl.kind IN ["def","structure","axiom","opaque"]
          FILTER LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1) == 0
          SORT decl.module, decl.name
          RETURN {module: decl.module, name: decl.name, kind: decl.kind}
    """))
    # 5. Vacuity
    result["vacuity_scan"] = {"sorry_admit_count": next(iter(db.aql.execute("""
        FOR node IN syntax_nodes
          FILTER node.kind == "atom" AND node.value IN ["sorry","admit"]
          COLLECT WITH COUNT INTO c
          RETURN c
    """)), 0)}
    # 6. Module Inventory
    result["module_inventory"] = list(db.aql.execute("""
        FOR decl IN lean_decls
          FILTER decl.module IN [
            "ChiralTLDescent","BraidIdealDescent","ChiralTensorRecoupling",
            "JonesBraidB3","B3PresentedGroup","YangBaxterQSwap",
            "ChiralB3PresentedBridge","ChiralCausalCone","TLChain",
            "YangBaxterQuotientDescent","ChiralTensorMatrixBridge"
          ]
          COLLECT module = decl.module INTO group
          LET thms = LENGTH(FOR d IN group FILTER d.decl.kind == "theorem" RETURN 1)
          LET defs = LENGTH(FOR d IN group FILTER d.decl.kind == "def" RETURN 1)
          SORT module
          RETURN {module, theorems: thms, defs: defs}
    """))
    # 7. Graph Counts
    result["graph_counts"] = {
        col: db.collection(col).count()
        for col in ["lean_decls","syntax_nodes","references","ast_child","has_syntax"]
    }
    # 8. Transitive Users
    result["transitive_users"] = list(db.aql.execute("""
        FOR v IN 1..5 INBOUND "lean_decls/ChiralTLDescent_chiral_left_tau_ideal" references
          COLLECT name = v.name SORT name RETURN name
    """))
    # 9. Cross-Module Paths
    result["cross_module_paths"] = list(db.aql.execute("""
        FOR a IN lean_decls FILTER a.module == "ChiralTLDescent"
          FOR b IN lean_decls FILTER b.module == "BraidIdealDescent"
            FOR v, e IN 1..5 OUTBOUND a._id references
              FILTER v._id == b._id
              SORT a.name, LENGTH(e) LIMIT 20
              RETURN {from: a.name, to: b.name, path_length: LENGTH(e)}
    """))
    # 10. Proof Complexity
    result["proof_complexity"] = list(db.aql.execute("""
        FOR decl IN lean_decls
          FILTER decl.name IN [
            "ChiralTLDescent.chiral_left_tau_ideal",
            "ChiralTLDescent.chiral_kernel_is_left_tau_ideal",
            "ChiralTLDescent.chiral_right_tau_ideal",
            "ChiralTLDescent.chiral_right_kernel_tau_ideal"
          ]
          LET root = FIRST(FOR e IN has_syntax FILTER e._from == decl._id RETURN DOCUMENT(e._to))
          LET nc = LENGTH(FOR v IN 1..50 OUTBOUND root ast_child RETURN 1)
          SORT decl.name
          RETURN {name: decl.name, ast_nodes: nc}
    """))
    return result


def write_json(data):
    p = OUT_DIR / "chiral_stability_certificate.json"
    p.write_text(json.dumps(data, indent=2, default=str))
    return p


def write_md(data):
    p = OUT_DIR / "chiral_stability_report.md"
    c = data["graph_counts"]
    v = data["vacuity_scan"]
    cells = data["four_cell_matrix"]
    md = f"""# Chiral tau-Ideal Stability Certificate
**Generated**: {data["generated_at"]}
**Database**: `{data["database"]}`

## Graph Counts
| Collection | Count |
|---|---|
| lean_decls | {c["lean_decls"]} |
| syntax_nodes | {c["syntax_nodes"]} |
| references | {c["references"]} |
| ast_child | {c["ast_child"]} |
| has_syntax | {c["has_syntax"]} |

## 4-Cell tau-Ideal Matrix
| Cell | Kind | Ref By | Deps |
|---|---|---|---|
"""
    for cell in cells:
        n = cell["name"].replace("ChiralTLDescent.","")
        md += f"| `{n}` | {cell['kind']} | {cell['referenced_by']} | {cell['depends_on']} |\n"
    md += f"""
## Vacuity Scan
- sorry/admit atoms: **{v['sorry_admit_count']}**

## Core Lemmas (Top 10)
| Lemma | Used By |
|---|---|
"""
    for lemma in data["top_lemmas"][:10]:
        md += f"| `{lemma['name']}` | {lemma['used_by']} |\n"
    md += "\n## Key Module Inventory\n| Module | Theorems | Defs |\n|---|---|---|\n"
    for m in data["module_inventory"]:
        md += f"| `{m['module']}` | {m['theorems']} | {m['defs']} |\n"
    md += "\n## Socket / Boundary Inventory\n| Kind | Name |\n|---|---|\n"
    for s in data["socket_inventory"]:
        md += f"| `{s['kind']}` | `{s['module']}.{s['name']}` |\n"
    md += "\n## Proof Complexity (AST Nodes)\n| Cell | AST Nodes |\n|---|---|\n"
    for cplx in data["proof_complexity"]:
        n = cplx["name"].replace("ChiralTLDescent.","")
        md += f"| `{n}` | {cplx['ast_nodes']} |\n"
    md += f"\n## Transitive Users ({len(data['transitive_users'])} total)\n"
    for u in data["transitive_users"][:20]:
        md += f"- `{u}`\n"
    md += f"\n## Cross-Module Paths (ChiralTLDescent -> BraidIdealDescent)\n| From | To | Len |\n|---|---|---|\n"
    for x in data["cross_module_paths"][:10]:
        md += f"| `{x['from']}` | `{x['to']}` | {x['path_length']} |\n"
    p.write_text(md)
    return p


def main():
    print("export_chiral_certificate: connecting...", file=sys.stderr)
    db = connect()
    print("export_chiral_certificate: running queries...", file=sys.stderr)
    data = run_queries(db)
    jp = write_json(data)
    mp = write_md(data)
    print(f"  JSON: {jp}", file=sys.stderr)
    print(f"  MD:   {mp}", file=sys.stderr)
    cells = data["four_cell_matrix"]
    print(f"  Cells: {len(cells)}  Vacuity: {data['vacuity_scan']['sorry_admit_count']}  "
          f"Decls: {data['graph_counts']['lean_decls']}  "
          f"Refs: {data['graph_counts']['references']}  "
          f"Sockets: {len(data['socket_inventory'])}", file=sys.stderr)


if __name__ == "__main__":
    main()
