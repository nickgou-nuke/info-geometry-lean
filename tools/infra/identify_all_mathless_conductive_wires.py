#!/usr/bin/env python3
"""ArangoDB Complete Mathless Conductive Wire Identifier

Scans the entire declaration graph in ArangoDB to locate all conductive dependency
wires containing one or more mathless intermediate nodes (pass-through wrappers,
zero-math alias definitions, or trivial structural wrappers).
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


def identify_all_mathless_conductive_wires(target: ArangoTarget) -> dict[str, Any]:
    print("🔍 Scanning ArangoDB graph for all conductive wires containing mathless nodes...")

    # Query all mathless intermediate declarations (AST node count < 10 with both callers and targets)
    mathless_wire_query = """
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
        id: d._id,
        name: d.name,
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
    mathless_wires = run_aql(target, mathless_wire_query)

    print(f"⚡ Identified {len(mathless_wires)} conductive wires containing mathless pass-through nodes.")

    report = {
        "summary": {
            "total_mathless_conductive_wires": len(mathless_wires),
            "highest_impact_wire": mathless_wires[0]["name"] if mathless_wires else None,
            "max_callers_for_wire": mathless_wires[0]["callerCount"] if mathless_wires else 0,
        },
        "mathless_conductive_wires": mathless_wires
    }

    return report


def main() -> None:
    parser = argparse.ArgumentParser(description="Complete Mathless Conductive Wire Identifier")
    parser.add_argument("--json-out", type=Path, default=Path("artifacts/dag/all_mathless_conductive_wires.json"))
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[2]
    target = arango_target(repo_root)

    report = identify_all_mathless_conductive_wires(target)

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2))
    print(f"✅ Full mathless conductive wire catalog saved to {args.json_out}")


if __name__ == "__main__":
    main()
