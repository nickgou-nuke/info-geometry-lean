#!/usr/bin/env python3
"""ArangoDB Conductive Wire Vacuous Node Auditor

Scans all conductive dependency wires in the ArangoDB declaration graph
and identifies all vacuous nodes (mathless pass-throughs, AST node count < 10,
or trivial structural wrappers) along each wire.
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


def audit_conductive_wires_vacuous_nodes(target: ArangoTarget) -> dict[str, Any]:
    print("🔍 Auditing conductive wires and identifying vacuous nodes along each wire...")

    # Query all conductive wires where an intermediate node has AST size < 10
    query = """
    FOR d IN decls
      FILTER d.valueFingerprint != null
         AND d.valueFingerprint.nodeCount != null
         AND d.valueFingerprint.nodeCount < 10
      LET callers = (
        FOR e IN edges
          FILTER e._to == d._id
          RETURN {id: e._from, name: DOCUMENT(e._from).name}
      )
      LET targets = (
        FOR e IN edges
          FILTER e._from == d._id
          RETURN {id: e._to, name: DOCUMENT(e._to).name}
      )
      FILTER LENGTH(callers) > 0 AND LENGTH(targets) > 0
      SORT LENGTH(callers) + LENGTH(targets) DESC
      RETURN {
        vacuousNodeId: d._id,
        vacuousNodeName: d.name,
        kind: d.kind,
        module: d.module,
        astNodeCount: d.valueFingerprint.nodeCount,
        shapeHash: d.valueFingerprint.shapeHash,
        callerCount: LENGTH(callers),
        targetCount: LENGTH(targets),
        callers: callers[*].name,
        targets: targets[*].name
      }
    """
    results = run_aql(target, query)

    # Group by conductive wire signature (targets -> vacuous -> callers)
    conductive_wires = []
    for item in results:
        conductive_wires.append({
            "wireName": f"{item['vacuousNodeName']} Wire",
            "vacuousNode": item['vacuousNodeName'],
            "module": item['module'],
            "astSize": item['astNodeCount'],
            "impact": item['callerCount'],
            "downstreamTargets": item['targets'][:5],
            "upstreamCallers": item['callers'][:5]
        })

    print(f"⚡ Found {len(conductive_wires)} conductive wires containing vacuous nodes.")

    report = {
        "summary": {
            "totalConductiveWiresWithVacuousNodes": len(conductive_wires),
            "highestImpactVacuousNode": conductive_wires[0]["vacuousNode"] if conductive_wires else None,
            "maxImpactCallers": conductive_wires[0]["impact"] if conductive_wires else 0
        },
        "conductiveWires": conductive_wires
    }

    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Conductive Wire Vacuous Node Auditor")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/vacuous_nodes_along_conductive_wires.json"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    report = audit_conductive_wires_vacuous_nodes(target)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Vacuous node audit saved to {args.json_out}")


if __name__ == "__main__":
    main()
