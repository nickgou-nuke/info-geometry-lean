# LeanTrail Conformance Report

- Created: `2026-04-16T17:05:13.987378+00:00`
- Baseline: `/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/graph_snapshot_pathstate_smoke.json` (snapshot)
- Candidate: `/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/graph_snapshot_pathstate_smoke.json` (snapshot)
- Overall pass: `True`

## Checks

| Check | Pass | Details |
|---|---|---|
| `node_count_drift` | `True` | `{"baseline": 18567, "candidate": 18567, "drift_pct": 0.0, "max_allowed": 0.0}` |
| `edge_count_drift` | `True` | `{"baseline": 217945, "candidate": 217945, "drift_pct": 0.0, "max_allowed": 0.0}` |
| `node_kind_counts` | `True` | `{"Declaration": {"baseline": 17945, "candidate": 17945, "drift_pct": 0.0}, "Module": {"baseline": 622, "candidate": 622, "drift_pct": 0.0}}` |
| `edge_kind_counts` | `True` | `{"coheres_with": {"baseline": 33686, "candidate": 33686, "drift_pct": 0.0}, "contains": {"baseline": 17945, "candidate": 17945, "drift_pct": 0.0}, "depends_type": {"baseline": 68373, "candidate": 68373, "drift_pct": 0.0}, "depends_value"...` |
| `node_id_overlap` | `True` | `{"baseline_only_count": 0, "baseline_only_sample": [], "candidate_only_count": 0, "candidate_only_sample": []}` |
| `edge_key_overlap` | `True` | `{"baseline_only_count": 0, "baseline_only_sample": [], "candidate_only_count": 0, "candidate_only_sample": []}` |
| `scc_signature` | `True` | `{"baseline": {"component_count": 18567, "largest_component": 1, "top_components": [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]}, "candidate": {"component_count": 18567, "largest_component": 1, "top_components": [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]}}` |
| `path_query_match` | `True` | `{"comparable": 3, "match_ratio": 1.0, "matched": 3, "min_required": 1.0, "queries": [{"baseline": {"found": false, "path_len": 0}, "candidate": {"found": false, "path_len": 0}, "comparable": true, "from": "InfoGeometry.Canonical.Relative...` |
| `required_path_locks` | `True` | `{"locked": 1, "required": 1, "rows": [{"from": "InfoGeometry.Analytic.deriv2_logSumExp_eq_softmaxVariance", "lawful_only": true, "locked": true, "path_len": 2, "state_policy": "locked-only", "to": "InfoGeometry.Analytic.logSumExp"}]}` |
| `coherence_hotspot_jaccard` | `True` | `{"baseline_top": ["InfoGeometry.Canonical.AnalyticalIndex.SinkhornRicciIndexInvariant.mk_components", "InfoGeometry.Canonical.DrazinSupercharge.central_supercharge_theorem", "InfoGeometry.Canonical.HyperbolicRotor.rotor_lane_head_null_ca...` |
| `holonomy_hotspot_jaccard` | `True` | `{"baseline_top": ["InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle", "InfoGeometry.Canonical.CertifiedInverseKernel", "InfoGeometry.Canonical.ConformalUnification.CertifiedConformalInference", "InfoGeometry.Canonical.C...` |

## Summary

```json
{
  "check_count": 11,
  "failed_checks": [],
  "node_drift_pct": 0.0,
  "edge_drift_pct": 0.0,
  "path_match_ratio": 1.0,
  "coherence_jaccard": 1.0,
  "holonomy_jaccard": 1.0,
  "baseline_metadata": {
    "created_at": "2026-04-16T16:46:26.206607+00:00",
    "source": "leantrail.normalizer",
    "commit_sha": "056132a5ce3b4c619c86f9f1eb6c0cedbbb27818",
    "toolchain": "leanprover/lean4:v4.28.0",
    "artifact_version": 3,
    "scope": "full",
    "include_modules": [],
    "dag_meta": {
      "typeCount": 657,
      "timestamp": "2026-04-15T22:06:28.722846+00:00",
      "schemaVersion": 3,
      "nsFilter": "InfoGeometry",
      "nodeCount": 17945,
      "morphismCount": 1054,
      "importRoot": "InfoGeometry.All",
      "edgeCount": 149817,
      "oleanHash": "43f327054d34dbf35f81d2319cd264a7f27409ac136f9bcdd5ee0e74d0837ff0",
      "sourceHash": "dda7b3bb8b14fc41467b968847112aa84eb7b8750b3a59094304f745679a812f"
    },
    "counts": {
      "nodes": 18567,
      "edges": 217945,
      "depth_rows": 18,
      "path_endpoints": {
        "source": 6904,
        "sink": 585,
        "internal": 10359,
        "isolated": 97
      },
      "failed_transition_edges": 2709,
      "locked_edges": 1
    },
    "path_state_sources": {
      "failed_transitions_file": "/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/failed_transitions.jsonl",
      "path_locks_file": "/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/path_locks.jsonl"
    }
  },
  "candidate_metadata": {
    "created_at": "2026-04-16T16:46:26.206607+00:00",
    "source": "leantrail.normalizer",
    "commit_sha": "056132a5ce3b4c619c86f9f1eb6c0cedbbb27818",
    "toolchain": "leanprover/lean4:v4.28.0",
    "artifact_version": 3,
    "scope": "full",
    "include_modules": [],
    "dag_meta": {
      "typeCount": 657,
      "timestamp": "2026-04-15T22:06:28.722846+00:00",
      "schemaVersion": 3,
      "nsFilter": "InfoGeometry",
      "nodeCount": 17945,
      "morphismCount": 1054,
      "importRoot": "InfoGeometry.All",
      "edgeCount": 149817,
      "oleanHash": "43f327054d34dbf35f81d2319cd264a7f27409ac136f9bcdd5ee0e74d0837ff0",
      "sourceHash": "dda7b3bb8b14fc41467b968847112aa84eb7b8750b3a59094304f745679a812f"
    },
    "counts": {
      "nodes": 18567,
      "edges": 217945,
      "depth_rows": 18,
      "path_endpoints": {
        "source": 6904,
        "sink": 585,
        "internal": 10359,
        "isolated": 97
      },
      "failed_transition_edges": 2709,
      "locked_edges": 1
    },
    "path_state_sources": {
      "failed_transitions_file": "/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/failed_transitions.jsonl",
      "path_locks_file": "/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/path_locks.jsonl"
    }
  }
}
```
