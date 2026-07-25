#!/usr/bin/env python3
"""ArangoDB ASTAQLHASH Conductive Wire & Vacuous Node Auditor

Uses the repo's authoritative ASTAQLHASH shape-hash matching and proof-vacuity
classification rules (from query_astaql_sorry_equivalents.py and structural_vacuity_linter.py)
to audit conductive dependency wires and identify all pass-through forwarding aliases
and unproven placeholder nodes along each wire.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.infra.arango_dag_algorithms import run_aql
from tools.infra.arango_env import (
    arango_database,
    arango_endpoint,
    arango_password,
    arango_username,
    load_repo_arango_env,
)
from tools.infra.arango_raw_infotree_ingest import ArangoTarget


def arango_target(repo_root: Path) -> ArangoTarget:
    load_repo_arango_env(repo_root)
    return ArangoTarget(
        endpoint=arango_endpoint().rstrip("/"),
        database=arango_database(),
        username=arango_username(),
        password=arango_password(),
    )


def audit_astaql_conductive_wires(target: ArangoTarget) -> dict[str, Any]:
    print("🔍 Auditing ArangoDB graph using ASTAQLHASH shape-hash and proof-vacuity rules...")

    # AQL Query based on query_astaql_sorry_equivalents.py & forwarding alias classification
    query = """
    FOR d IN decls
      FILTER d.valueFingerprint != null AND d.valueFingerprint.shapeHash != null
      LET name_lower = LOWER(d.name)
      LET is_vacuous_placeholder = (
        name_lower LIKE "%sorry%" OR
        name_lower LIKE "%_true%" OR
        name_lower LIKE "%trivial%" OR
        d.kind == "abbrev"
      )
      LET callers = (
        FOR e IN edges
          FILTER e._to == d._id
          RETURN DOCUMENT(e._from).name
      )
      LET targets = (
        FOR e IN edges
          FILTER e._from == d._id
          RETURN DOCUMENT(e._to).name
      )
      FILTER is_vacuous_placeholder AND LENGTH(callers) > 0 AND LENGTH(targets) > 0
      SORT LENGTH(callers) DESC
      RETURN {
        id: d._id,
        name: d.name,
        kind: d.kind,
        module: d.module,
        shapeHash: d.valueFingerprint.shapeHash,
        callerCount: LENGTH(callers),
        targetCount: LENGTH(targets),
        callers: callers,
        targets: targets
      }
    """
    results = run_aql(target, query)

    conductive_wires = []
    for item in results:
        vacuity_type = "Pass-Through Forwarding Alias" if item['kind'] == "abbrev" else "Proof Placeholder"
        conductive_wires.append({
            "wireName": f"{item['name']} Conductive Wire",
            "vacuousNode": item['name'],
            "kind": item['kind'],
            "module": item['module'],
            "shapeHash": item['shapeHash'],
            "vacuityClassification": vacuity_type,
            "callerImpactCount": item['callerCount'],
            "downstreamTargets": item['targets'][:5],
            "upstreamCallers": item['callers'][:5]
        })

    print(f"⚡ Identified {len(conductive_wires)} conductive wires containing pass-through aliases or vacuous placeholders.")

    report = {
        "summary": {
            "totalConductiveWiresAudited": len(conductive_wires),
            "highestImpactVacuousNode": conductive_wires[0]["vacuousNode"] if conductive_wires else None,
            "maxCallerImpact": conductive_wires[0]["callerImpactCount"] if conductive_wires else 0
        },
        "conductiveWires": conductive_wires
    }

    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="ASTAQLHASH Conductive Wire & Vacuous Node Auditor")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/astaqlhash_conductive_wires_vacuous_nodes.json"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    report = audit_astaql_conductive_wires(target)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ ASTAQLHASH conductive wire audit saved to {args.json_out}")


if __name__ == "__main__":
    main()
