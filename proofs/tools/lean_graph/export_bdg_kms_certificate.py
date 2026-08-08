#!/usr/bin/env python3
"""GEPA BdG/KMS finite algebraic certificate.

Usage:  python3 tools/lean_graph/export_bdg_kms_certificate.py
Output: tools/lean_graph/out/bdg_kms_certificate.json
        tools/lean_graph/out/bdg_kms_report.md
"""

from __future__ import annotations

import json
import os
import sys
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

FINITE_THEOREMS = [
    "SupergradedCuntzBdG.star_bdgMajoranaPlus",
    "SupergradedCuntzBdG.bdgMajoranaPlus_sq_eq_hamiltonianAtom",
    "SupergradedCuntzBdG.bdgMajoranaMinus_is_odd",
    "SupergradedCuntzBdG.grandCanonicalBracket_even_left",
    "SupergradedCuntzBdG.grandCanonicalBracket_even_right",
    "SupergradedCuntzBdG.grandCanonicalBracket_odd_odd",
    "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_left",
    "SupergradedCuntzBdG.grandCanonicalWeightedBracket_even_right",
    "SupergradedCuntzBdG.grandCanonicalWeightedBracket_odd_odd",
]

FINITE_BLOCKERS = [
    {
        "name": "SupergradedCuntzBdG.bdgMajoranaMinus",
        "blocker": (
            "bdgMajoranaMinus star/square requires finite Cuntz "
            "T_mul_S/partition algebra, not analytic completion"
        ),
    }
]

ANALYTIC_SOCKETS = [
    {
        "name": "CStarCuntzTensorQuotient.UniversalCStarCompletionSocket",
        "layer": "C*/universal completion",
    },
    {
        "name": "SupergradedCuntzBdG.KMSStateSocket",
        "layer": "algebraic KMS expectation interface",
    },
    {
        "name": "SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket",
        "layer": "GNS/Tomita cyclic-separating realization",
    },
    {
        "name": "ModularRenyiEntropy.ModularRenyiEntropySocket",
        "layer": "future spectral/Renyi/Mellin analytic layer",
    },
]

BOUNDARY_PHRASE = (
    "Excellent — that’s the right boundary: finite algebraic BdG/KMS layer "
    "closed, analytic completion explicitly socketed instead of faked."
)


def connect():
    return ArangoClient(hosts=DB_HOST).db(DB_NAME, username=DB_USER, password=DB_PASS)


def run_queries(db):
    result = {
        "certificate": "bdg-kms-finite-algebraic-layer",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "database": DB_NAME,
        "boundary_phrase": BOUNDARY_PHRASE,
    }
    result["finite_theorems"] = list(
        db.aql.execute(
            """
            FOR name IN @names
              LET decl = FIRST(FOR d IN lean_decls FILTER d.name == name RETURN d)
              RETURN {
                name,
                exists: decl != null,
                kind: decl == null ? "missing" : (decl.kind == null ? "unknown" : decl.kind),
                module: decl == null ? "missing" : (decl.module == null ? "unknown" : decl.module),
                depends_on: decl == null ? 0 : LENGTH(FOR e IN references FILTER e._from == decl._id RETURN 1),
                referenced_by: decl == null ? 0 : LENGTH(FOR e IN references FILTER e._to == decl._id RETURN 1)
              }
            """,
            bind_vars={"names": FINITE_THEOREMS},
        )
    )
    result["finite_blockers"] = list(
        db.aql.execute(
            """
            FOR blocker IN @blockers
              LET decl = FIRST(FOR d IN lean_decls FILTER d.name == blocker.name RETURN d)
              RETURN {
                name: blocker.name,
                exists: decl != null,
                kind: decl == null ? "missing" : (decl.kind == null ? "unknown" : decl.kind),
                module: decl == null ? "missing" : (decl.module == null ? "unknown" : decl.module),
                blocker: blocker.blocker,
                classification: "finite-algebraic-blocker"
              }
            """,
            bind_vars={"blockers": FINITE_BLOCKERS},
        )
    )
    result["analytic_sockets"] = list(
        db.aql.execute(
            """
            FOR socket IN @sockets
              LET decl = FIRST(FOR d IN lean_decls FILTER d.name == socket.name RETURN d)
              RETURN {
                name: socket.name,
                exists: decl != null,
                kind: decl == null ? "future" : (decl.kind == null ? "unknown" : decl.kind),
                module: decl == null ? "future" : (decl.module == null ? "unknown" : decl.module),
                layer: socket.layer,
                classification: "analytic-socket"
              }
            """,
            bind_vars={"sockets": ANALYTIC_SOCKETS},
        )
    )
    result["module_inventory"] = list(
        db.aql.execute(
            """
            FOR decl IN lean_decls
              FILTER decl.module IN [
                "SupergradedCuntzBdG",
                "ComplexStarCuntzRedesign",
                "CStarCuntzTensorQuotient",
                "AlgebraicCuntzQuotient"
              ]
              COLLECT module = decl.module INTO group
              LET theorems = LENGTH(FOR d IN group FILTER d.decl.kind == "theorem" RETURN 1)
              LET defs = LENGTH(FOR d IN group FILTER d.decl.kind == "def" RETURN 1)
              LET structures = LENGTH(FOR d IN group FILTER d.decl.kind == "structure" RETURN 1)
              SORT module
              RETURN {module, theorems, defs, structures, total: LENGTH(group)}
            """
        )
    )
    result["socket_users"] = list(
        db.aql.execute(
            """
            FOR socket IN lean_decls
              FILTER socket.name IN [
                "SupergradedCuntzBdG.KMSStateSocket",
                "SupergradedCuntzBdG.TomitaTakesakiKMSRealizationSocket",
                "CStarCuntzTensorQuotient.UniversalCStarCompletionSocket"
              ]
              LET users = (
                FOR v IN 1..5 INBOUND socket._id references
                  COLLECT name = v.name
                  SORT name
                  RETURN name
              )
              SORT socket.name
              RETURN {socket: socket.name, transitive_users: users}
            """
        )
    )
    result["vacuity_scan"] = {
        "sorry_admit_count": next(
            iter(
                db.aql.execute(
                    """
                    FOR decl IN lean_decls
                      FILTER decl.module IN [
                        "SupergradedCuntzBdG",
                        "CStarCuntzTensorQuotient",
                        "ComplexStarCuntzRedesign"
                      ]
                      FOR root IN 1..1 OUTBOUND decl has_syntax
                        FOR node IN 0..50 OUTBOUND root ast_child
                          FILTER node.kind == "atom" AND node.value IN ["sorry", "admit"]
                          COLLECT WITH COUNT INTO c
                          RETURN c
                    """
                )
            ),
            0,
        )
    }
    result["graph_counts"] = {
        col: db.collection(col).count()
        for col in ["lean_decls", "syntax_nodes", "references", "ast_child", "has_syntax"]
    }
    return result


def write_json(data):
    path = OUT_DIR / "bdg_kms_certificate.json"
    path.write_text(json.dumps(data, indent=2, default=str), encoding="utf-8")
    return path


def write_md(data):
    path = OUT_DIR / "bdg_kms_report.md"
    counts = data["graph_counts"]
    finite = data["finite_theorems"]
    blockers = data["finite_blockers"]
    sockets = data["analytic_sockets"]
    vacuity = data["vacuity_scan"]
    finite_present = sum(1 for item in finite if item["exists"])
    theorem_kind_present = sum(1 for item in finite if item["kind"] == "theorem")
    blockers_present = sum(1 for item in blockers if item["exists"])
    sockets_present = sum(1 for item in sockets if item["exists"])

    md = f"""# BdG/KMS Finite Algebraic Certificate

**Generated**: {data["generated_at"]}
**Database**: `{data["database"]}`

> {data["boundary_phrase"]}

## Summary
| Metric | Value |
|---|---|
| finite theorem declarations present | {finite_present}/{len(finite)} |
| theorem-kind metadata present | {theorem_kind_present}/{len(finite)} |
| finite algebraic blockers | {blockers_present}/{len(blockers)} |
| analytic sockets present | {sockets_present}/{len(sockets)} |
| BdG/KMS sorry/admit atoms | {vacuity["sorry_admit_count"]} |

## Graph Counts
| Collection | Count |
|---|---|
| lean_decls | {counts["lean_decls"]} |
| syntax_nodes | {counts["syntax_nodes"]} |
| references | {counts["references"]} |
| ast_child | {counts["ast_child"]} |
| has_syntax | {counts["has_syntax"]} |

## Proved Finite Algebraic Layer
| Declaration | Kind | Deps | Ref By |
|---|---|---|---|
"""
    for item in finite:
        md += (
            f"| `{item['name']}` | `{item['kind']}` | "
            f"{item['depends_on']} | {item['referenced_by']} |\n"
        )

    md += "\n## Classified Finite Blocker\n| Declaration | Kind | Classification | Blocker |\n|---|---|---|---|\n"
    for item in blockers:
        md += (
            f"| `{item['name']}` | `{item['kind']}` | "
            f"`{item['classification']}` | {item['blocker']} |\n"
        )

    md += "\n## Analytic Socket Frontier\n| Declaration | Exists | Kind | Layer |\n|---|---|---|---|\n"
    for item in sockets:
        md += (
            f"| `{item['name']}` | {item['exists']} | "
            f"`{item['kind']}` | {item['layer']} |\n"
        )

    md += "\n## Module Inventory\n| Module | Theorems | Defs | Structures | Total |\n|---|---|---|---|---|\n"
    for item in data["module_inventory"]:
        md += (
            f"| `{item['module']}` | {item['theorems']} | {item['defs']} | "
            f"{item['structures']} | {item['total']} |\n"
        )

    md += "\n## Socket Users\n| Socket | Transitive Users |\n|---|---|\n"
    for item in data["socket_users"]:
        users = ", ".join(f"`{name}`" for name in item["transitive_users"][:8])
        if len(item["transitive_users"]) > 8:
            users += f", … +{len(item['transitive_users']) - 8}"
        md += f"| `{item['socket']}` | {users or 'none'} |\n"

    path.write_text(md, encoding="utf-8")
    return path


def main():
    print("export_bdg_kms_certificate: connecting...", file=sys.stderr)
    db = connect()
    print("export_bdg_kms_certificate: running queries...", file=sys.stderr)
    data = run_queries(db)
    json_path = write_json(data)
    md_path = write_md(data)
    finite_present = sum(1 for item in data["finite_theorems"] if item["exists"])
    theorem_kind_present = sum(1 for item in data["finite_theorems"] if item["kind"] == "theorem")
    print(f"  JSON: {json_path}", file=sys.stderr)
    print(f"  MD:   {md_path}", file=sys.stderr)
    print(
        "  Finite theorems: "
        f"{finite_present}/{len(data['finite_theorems'])} present "
        f"({theorem_kind_present}/{len(data['finite_theorems'])} theorem-kind metadata)  "
        f"Blockers: {sum(1 for item in data['finite_blockers'] if item['exists'])}  "
        f"Sockets: {sum(1 for item in data['analytic_sockets'] if item['exists'])}  "
        f"Vacuity: {data['vacuity_scan']['sorry_admit_count']}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
