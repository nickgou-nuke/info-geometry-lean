# LeanTrail Blueprint (Repo-Integrated)

> Status: `maintained local guide`
> Audited: 2026-05-02
> Note: Current for this subsystem, but subordinate to repo-wide authority docs and code.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

LeanTrail is a Lean-native semantic explorer scaffold for the InfoGeometry repo.
It is designed to reuse maintained DAG/process artifacts and expose a typed
query surface for graph exploration and bridge-candidate workflow.

## Architecture

```text
Lean source + lake build
  -> extractor-service (optional refresh lane)
  -> normalizer-service
  -> graph snapshot cache + query store
  -> query API
  -> LeanTrail UI + Lean RPC adapter hook
```

## Data Sources

- `artifacts/dag/index/meta.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/index/edges.jsonl`
- `artifacts/dag/representation-depth-tags.json`
- `artifacts/dag/process-flow/process-events.jsonl`

## Canonical Schema Surface

- `leantrail/schemas/leantrail_graph_snapshot.schema.json`
- `leantrail/schemas/leantrail_bridge_request.schema.json`

Normalized node attributes include:

- `id`, `name`, `kind`, `module`, `file`, `line`
- `rep_depth`, `role`, `module_family`
- `commit_sha`, `toolchain`, `artifact_version`

Normalized edge attributes include:

- `src`, `dst`, `kind`, `weight`, `evidence_ref`

## API Surface (MVP)

- `GET /search?q=...`
- `GET /decl/{name}`
- `GET /neighborhood/{name}?radius=2`
- `GET /path?from=...&to=...&lawful_only=true&state_policy=any`
- `GET /proofstate?file=...&line=...&col=...`
- `GET /coherence/hotspots`
- `GET /holonomy/hotspots?limit=25&alpha=1.5&beta=2.0&gamma=3.0&min_score=0.0`
- `POST /bridge-candidate`

`POST /bridge-candidate` validates request payloads, then emits typed packets to
`artifacts/dag/process-flow/bridge-candidates/`, aligning with the existing
`equivalence | obstruction | discard` candidate-map discipline.

## Holonomy Report Lane

Holonomy hotspots can be generated as an artifact:

```bash
python3 tools/infra/holonomy_auditor.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --out artifacts/leantrail/holonomy_report.json
```

The current implementation prefers explicit telemetry fields when available
(`attrs.holonomy.tactic_steps`, `context_expansion`, `metavariable_flux`).
If telemetry is missing, it computes proxy values from dependency/anomaly edges.

## Conformance Lane

Cross-analyzer or cross-mode parity can be checked by comparing two LeanTrail
snapshots:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot_candidate.json \
  --json-out artifacts/leantrail/conformance_report.json \
  --md-out artifacts/leantrail/conformance_report.md \
  --fail-on-violation
```

Snapshot vs GraphML adapter:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/graph_snapshot.graphml \
  --candidate-format graphml \
  --fail-on-violation
```

Snapshot vs Neo4j CSV adapter:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/neo4j \
  --candidate-format neo4j-csv \
  --fail-on-violation
```

Snapshot vs Arango JSON adapter:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/arango \
  --candidate-format arango-json \
  --fail-on-violation
```

Lock-gate check:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot.json \
  --required-locked-paths leantrail/config/required_locks.json \
  --fail-on-violation
```

The report includes:

- node and edge drift percentages
- node/edge kind distribution comparison
- overlap on node ids and edge keys
- dependency SCC signature parity
- shortest-path query parity (default canonical seeds or custom `--path-queries`)
- hotspot overlap (`coherence`, `holonomy`) via Jaccard

Managed wrapper:

```bash
lake script run leantrailConformance \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot_candidate.json
```

## External Analyzer Adapter Exports

Export the canonical LeanTrail snapshot for external tools:

```bash
python3 tools/leantrail/export.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --to all
```

`all` includes GraphML, Neo4j CSV, and Arango JSON directories.

Managed wrapper:

```bash
lake script run leantrailExport \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --to all
```

## Arango Carrier Ingestion

Load adapter output into ArangoDB:

```bash
python3 tools/leantrail/arango_ingest.py \
  --input-dir artifacts/leantrail/arango \
  --endpoint http://127.0.0.1:8529 \
  --database infogeometry \
  --username root \
  --password "$ARANGO_PASSWORD" \
  --json-out artifacts/leantrail/arango_ingest_report.json
```

Managed wrapper:

```bash
lake script run leantrailArangoIngest \
  --input-dir artifacts/leantrail/arango
```

## Arango Physics Query Surface

Local (carrier-side) surprisal evaluation:

```bash
python3 tools/leantrail/arango_physics_evaluator.py \
  --mode local \
  --input artifacts/leantrail/arango \
  --input-format arango-json \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --radius 2 \
  --json-out artifacts/leantrail/arango_physics_report.json
```

Live Arango AQL mode:

```bash
python3 tools/leantrail/arango_physics_evaluator.py \
  --mode arango-http \
  --endpoint http://127.0.0.1:8529 \
  --database infogeometry \
  --username root \
  --password "$ARANGO_PASSWORD" \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --radius 2
```

Baseline/candidate gradient (`ΔS`) is available in local mode via
`--candidate-input`. Path scoring can enforce
`--path-state-policy any|exclude-failed|locked-only`.

Managed wrapper:

```bash
lake script run leantrailArangoPhysicsEval \
  --mode local \
  --input artifacts/leantrail/arango \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
```

## Failure Memory Lane

Harvest process-flow defects into LeanTrail failed transitions:

```bash
python3 tools/leantrail/failure_harvester.py \
  --defects artifacts/dag/process-flow/defects.jsonl \
  --out artifacts/leantrail/failed_transitions.jsonl \
  --merge-existing
```

Build-log ingest can be attached with `--build-log` (repeatable) or
`--build-stdout` / `--build-stderr`.

Managed wrapper:

```bash
lake script run leantrailFailureHarvest \
  --defects artifacts/dag/process-flow/defects.jsonl \
  --out artifacts/leantrail/failed_transitions.jsonl
```

`scripts/quality/strict-check.sh` now invokes the same harvester automatically
on strict failure, mining stdout/stderr into failed transitions memory.

## Path Bind/Lock Lane

Register a `bound` or `locked` path record:

```bash
python3 tools/leantrail/path_lock_registry.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --src InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --dst InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle \
  --state locked \
  --state-policy exclude-failed \
  --proof-ref lean/InfoGeometry/Canonical/RelativePotentialCore.lean
```

Managed wrapper:

```bash
lake script run leantrailPathLock \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --src InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --dst InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle \
  --state locked
```

## Hole Packet Lane

Build ranked hole packets (find -> grade -> propose -> kernel-only close contract):

```bash
python3 tools/leantrail/hole_packets.py \
  --failed-transitions artifacts/leantrail/failed_transitions.jsonl \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --conformance-report artifacts/leantrail/conformance_lock_gate.json \
  --out artifacts/leantrail/hole_packets.jsonl \
  --md-out artifacts/leantrail/hole_packets.md
```

Managed wrapper:

```bash
lake script run leantrailHolePackets \
  --failed-transitions artifacts/leantrail/failed_transitions.jsonl
```

Path traversal policies:

- `state_policy=any`
- `state_policy=exclude-failed`
- `state_policy=locked-only`

## Runbook

Build snapshot:

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json
```

Incremental patch/prune update (local developer lane):

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json \
  --incremental \
  --incremental-radius 1
```

Incremental mode:

- detects changed Lean modules from `git diff` + untracked files;
- expands to an impacted module neighborhood using declaration-edge adjacency;
- rebuilds only impacted modules and merges the patch into the existing
  snapshot.

CI policy: use full rebuilds for deterministic artifact completeness.

Run API:

```bash
python3 -m leantrail.api.server \
  --repo-root . \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --host 127.0.0.1 \
  --port 8765
```

## Guardrails

- Graph shape is diagnostic evidence, not theorem closure.
- Lean kernel remains the authority for truth.
- Bridge claims must resolve to packet outcomes: equivalence, obstruction, or discard.
