# LeanTrail Blueprint

LeanTrail is the semantic explorer lane for this repository.
It is Sourcetrail-style in UX, but Lean-native in evidence: it consumes DAG and
process-flow artifacts produced from elaborated Lean data.

## Implemented Scaffold

The scaffold now exists under:

- `leantrail/backend/extractor.py`
- `leantrail/backend/normalizer.py`
- `leantrail/backend/indexer.py`
- `leantrail/backend/store.py`
- `leantrail/backend/query_api.py`
- `leantrail/backend/rpc_adapter.py`
- `leantrail/api/server.py`
- `leantrail/schemas/leantrail_graph_snapshot.schema.json`
- `leantrail/schemas/leantrail_bridge_request.schema.json`
- `leantrail/ui/index.html`

Use [LeanTrail.md](LeanTrail.md) for run commands and endpoint-level details.

## Contract

- graph shape is diagnostic evidence, not theorem truth;
- Lean kernel remains closure authority;
- bridge claims emitted from LeanTrail must resolve as `equivalence`,
  `obstruction`, or `discard` packets.
