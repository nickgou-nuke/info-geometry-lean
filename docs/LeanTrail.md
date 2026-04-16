# LeanTrail Blueprint (Repo-Integrated)

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
- `GET /path?from=...&to=...&lawful_only=true`
- `GET /proofstate?file=...&line=...&col=...`
- `GET /coherence/hotspots`
- `POST /bridge-candidate`

`POST /bridge-candidate` validates request payloads, then emits typed packets to
`artifacts/dag/process-flow/bridge-candidates/`, aligning with the existing
`equivalence | obstruction | discard` candidate-map discipline.

## Runbook

Build snapshot:

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json
```

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
