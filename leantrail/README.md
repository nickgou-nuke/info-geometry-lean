# LeanTrail

LeanTrail is a Lean-native semantic explorer scaffold for this repository.
It is intentionally sourced from elaborated DAG/process artifacts, not static
text parsing.

Its role is navigation, retrieval, and conformance around the checked Lean corpus. LeanTrail is not a proof engine and it does not outrank the Lean kernel or native audit layer.

## Goals

- semantic-first indexing from `artifacts/dag/*`
- repo-native typing (`rep_depth`, owner/translator/coherence/capstone signals)
- reproducible snapshots bound to commit and toolchain
- Sourcetrail-style graph navigation surface with Lean-proofstate hook points

## Layout

- `leantrail/backend/extractor.py` — optional refresh pipeline runner (locked build + DAG exports)
- `leantrail/backend/normalizer.py` — canonical node/edge normalization
- `leantrail/backend/indexer.py` — snapshot builder CLI
- `leantrail/backend/store.py` — in-memory graph query engine
- `leantrail/backend/query_api.py` — endpoint-facing query surface
- `leantrail/backend/rpc_adapter.py` — proofstate bridge stub (contract preserved)
- `leantrail/api/server.py` — minimal HTTP API server
- `leantrail/schemas/` — JSON schemas for snapshot and bridge-candidate requests
- `leantrail/ui/` — initial UI placeholder

## Build Snapshot

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json
```

Incremental patch/prune update (local dev):

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json \
  --incremental \
  --incremental-radius 1
```

This mode uses the previous snapshot as baseline, detects changed Lean modules
from git/worktree state, computes an impacted module neighborhood, then only
rebuilds and merges the impacted subgraph.

Optional refresh before normalization:

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json \
  --refresh
```

For CI/release runs, prefer full rebuild (no `--incremental`) for deterministic
coverage.

## Run API

```bash
python3 -m leantrail.api.server \
  --repo-root . \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --host 127.0.0.1 \
  --port 8765
```

## Endpoints (MVP)

- `GET /search?q=...`
- `GET /decl/{name}`
- `GET /neighborhood/{name}?radius=2`
- `GET /path?from=...&to=...&lawful_only=true&state_policy=any`
- `GET /proofstate?file=...&line=...&col=...`
- `GET /coherence/hotspots`
- `GET /holonomy/hotspots`
- `POST /bridge-candidate`

`POST /bridge-candidate` writes typed candidate-map packets under
`artifacts/dag/process-flow/bridge-candidates/` and validates against the
bridge packet contract.

## Holonomy Auditor

Build a declaration-level holonomy report from the LeanTrail snapshot:

```bash
python3 tools/infra/holonomy_auditor.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --out artifacts/leantrail/holonomy_report.json
```

`holonomy_score` uses:

- `alpha * tactic_steps`
- `beta * context_expansion`
- `gamma * metavariable_flux`

When explicit telemetry is absent, the auditor falls back to structural proxies
derived from dependency and anomaly edges. This keeps the surface useful before
full InfoTree-level telemetry is wired.

## Snapshot Conformance

Compare two snapshots (for example full rebuild vs incremental patch/prune, or
canonical snapshot vs exported/reimported analyzer view):

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot_candidate.json \
  --json-out artifacts/leantrail/conformance_report.json \
  --md-out artifacts/leantrail/conformance_report.md \
  --fail-on-violation
```

Compare canonical snapshot against GraphML export:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/graph_snapshot.graphml \
  --candidate-format graphml \
  --fail-on-violation
```

Compare canonical snapshot against Neo4j CSV export:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/neo4j \
  --candidate-format neo4j-csv \
  --fail-on-violation
```

Compare canonical snapshot against Arango JSON export:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --baseline-format snapshot \
  --candidate artifacts/leantrail/arango \
  --candidate-format arango-json \
  --fail-on-violation
```

Enforce required locked paths:

```bash
python3 tools/leantrail/conformance.py \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot.json \
  --required-locked-paths leantrail/config/required_locks.json \
  --fail-on-violation
```

The checker evaluates:

- node/edge count drift
- node/edge kind distributions
- node/edge overlap keys
- dependency SCC signature parity
- shortest-path query parity on canonical seeds (or custom query file)
- coherence and holonomy hotspot overlap (Jaccard)

Managed entrypoint:

```bash
lake script run leantrailConformance \
  --baseline artifacts/leantrail/graph_snapshot.json \
  --candidate artifacts/leantrail/graph_snapshot_candidate.json
```

## External Analyzer Exports

Export canonical snapshot to GraphML and Neo4j CSV:

```bash
python3 tools/leantrail/export.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --to all
```

`--to all` currently emits:

- `graph_snapshot.graphml`
- `neo4j/{nodes.csv,edges.csv,metadata.json}`
- `arango/{ig_nodes.jsonl,ig_edges.jsonl,metadata.json}`

Managed entrypoint:

```bash
lake script run leantrailExport \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --to all
```

## Arango Ingestion

Ingest `arango-json` export into ArangoDB collections:

```bash
python3 tools/leantrail/arango_ingest.py \
  --input-dir artifacts/leantrail/arango \
  --endpoint http://127.0.0.1:8529 \
  --database infogeometry \
  --username root \
  --password "$ARANGO_PASSWORD" \
  --json-out artifacts/leantrail/arango_ingest_report.json
```

Managed entrypoint:

```bash
lake script run leantrailArangoIngest \
  --input-dir artifacts/leantrail/arango
```

## Arango Physics Evaluator

Evaluate a local surprisal surface from exported `arango-json`:

```bash
python3 tools/leantrail/arango_physics_evaluator.py \
  --mode local \
  --input artifacts/leantrail/arango \
  --input-format arango-json \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --radius 2 \
  --json-out artifacts/leantrail/arango_physics_report.json \
  --md-out artifacts/leantrail/arango_physics_report.md
```

Evaluate directly against ArangoDB via AQL:

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

Baseline/candidate local gradient (`ΔS`):

```bash
python3 tools/leantrail/arango_physics_evaluator.py \
  --mode local \
  --input artifacts/leantrail/arango_baseline \
  --candidate-input artifacts/leantrail/arango_candidate \
  --path-state-policy exclude-failed \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
```

Managed entrypoint:

```bash
lake script run leantrailArangoPhysicsEval \
  --mode local \
  --input artifacts/leantrail/arango \
  --center InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity
```

## Failure Harvester

Harvest process-flow defects into failed transition memory:

```bash
python3 tools/leantrail/failure_harvester.py \
  --defects artifacts/dag/process-flow/defects.jsonl \
  --out artifacts/leantrail/failed_transitions.jsonl \
  --merge-existing
```

Also ingest strict/lake build logs:

```bash
python3 tools/leantrail/failure_harvester.py \
  --defects artifacts/dag/process-flow/defects.jsonl \
  --build-stdout reports/build/stdout.log \
  --build-stderr reports/build/stderr.log \
  --out artifacts/leantrail/failed_transitions.jsonl \
  --merge-existing
```

Managed entrypoint:

```bash
lake script run leantrailFailureHarvest \
  --defects artifacts/dag/process-flow/defects.jsonl \
  --out artifacts/leantrail/failed_transitions.jsonl
```

`scripts/quality/strict-check.sh` also runs this harvester automatically on failure,
capturing strict-check stdout/stderr into failure memory.

## Path Lock Registry

Bind/lock a path with source-sink metadata:

```bash
python3 tools/leantrail/path_lock_registry.py \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --src InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --dst InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle \
  --state locked \
  --state-policy exclude-failed \
  --proof-ref lean/InfoGeometry/Canonical/RelativePotentialCore.lean
```

Managed entrypoint:

```bash
lake script run leantrailPathLock \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --src InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity \
  --dst InfoGeometry.Canonical.RelativePotentialCore.relativeLogDensity_cocycle \
  --state locked
```

## Hole Packet Builder

Build ranked closure holes from failure memory + conformance surfaces:

```bash
python3 tools/leantrail/hole_packets.py \
  --failed-transitions artifacts/leantrail/failed_transitions.jsonl \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --conformance-report artifacts/leantrail/conformance_lock_gate.json \
  --out artifacts/leantrail/hole_packets.jsonl \
  --md-out artifacts/leantrail/hole_packets.md
```

Managed entrypoint:

```bash
lake script run leantrailHolePackets \
  --failed-transitions artifacts/leantrail/failed_transitions.jsonl
```

## Guardrails

- Graph structure is evidence, not proof.
- LeanTrail is a memory and navigation surface, not a theorem authority.
- Lean kernel remains closure authority.
- Bridge claims must close as `equivalence | obstruction | discard`.
- Path traversal can enforce edge states:
  - `state_policy=any`
  - `state_policy=exclude-failed`
  - `state_policy=locked-only`
