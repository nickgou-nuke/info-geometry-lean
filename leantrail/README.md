# LeanTrail

LeanTrail is a Lean-native semantic explorer scaffold for this repository.
It is intentionally sourced from elaborated DAG/process artifacts, not static
text parsing.

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

Optional refresh before normalization:

```bash
python3 -m leantrail.backend.indexer \
  --repo-root . \
  --snapshot-out artifacts/leantrail/graph_snapshot.json \
  --refresh
```

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
- `GET /path?from=...&to=...&lawful_only=true`
- `GET /proofstate?file=...&line=...&col=...`
- `GET /coherence/hotspots`
- `POST /bridge-candidate`

`POST /bridge-candidate` writes typed candidate-map packets under
`artifacts/dag/process-flow/bridge-candidates/` and validates against the
bridge packet contract.

## Guardrails

- Graph structure is evidence, not proof.
- Lean kernel remains closure authority.
- Bridge claims must close as `equivalence | obstruction | discard`.
