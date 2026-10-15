#!/usr/bin/env python3
"""Report name-seeded structural candidates; never a mathematical vacuity verdict."""
from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
for path in (REPO_ROOT, REPO_ROOT / "src"):
    sys.path.insert(0, str(path))

from igf.config import (load_repo_arango_env, arango_endpoint, arango_database,
                        arango_username, arango_password)
from igf.graph.arango_http import ArangoHttpTarget, execute_aql

QUERY = """
FOR doc IN dag_nodes
  FILTER IS_STRING(doc.valueFingerprint.shapeHash)
    AND doc.valueFingerprint.shapeHash != '' AND IS_STRING(doc.name)
  COLLECT fingerprint = doc.valueFingerprint.shapeHash INTO group = doc.name
  LET seeds = (FOR name IN group
    FILTER LIKE(name, '%_True') OR LIKE(name, '%_sorryProof') OR LIKE(name, '%sorry%')
    RETURN name)
  FILTER LENGTH(seeds) > 0
  SORT fingerprint
  RETURN {shapeHash: fingerprint, total_nodes: LENGTH(group),
          all_nodes: group, seed_names: seeds}
"""


def run_vacuity_linter() -> int:
    load_repo_arango_env()
    target = ArangoHttpTarget(arango_endpoint().rstrip('/'), arango_database(),
                             arango_username(), arango_password())
    clusters = execute_aql(target, QUERY)
    for cluster in clusters:
        if (not isinstance(cluster, dict)
                or not isinstance(cluster.get('total_nodes'), int)
                or not isinstance(cluster.get('all_nodes'), list)):
            raise ValueError('Malformed structural candidate row')
    report = {
        'schema': 'ig.structural-vacuity-candidates.v2',
        'evidence_class': 'name_seeded_hash_candidates_not_mathematical_verdict',
        'review_required': 'Inspect Lean owner definitions and hypotheses; hash matches do not prove vacuity.',
        'clusters': clusters,
        'candidate_nodes': sum(c['total_nodes'] for c in clusters),
    }
    path = REPO_ROOT / 'reports/structural_vacuity_report.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(f"Reported {len(clusters)} heuristic structural candidate groups: {path}")
    return 0


if __name__ == '__main__':
    try:
        sys.exit(run_vacuity_linter())
    except Exception as exc:
        print(f'structural_vacuity_linter: audit failed ({type(exc).__name__}); no complete report',
              file=sys.stderr)
        sys.exit(1)
