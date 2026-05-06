# txt2kg Hive ingest

This is the repo-native adaptation of NVIDIA's `txt2kg` playbook for the
Alexandria/Hive theorem-factory memory layer.

It processes a local library of papers, arXiv text/PDFs, Black Books, notes, or
chat-history exports into:

- retrieval-only chunks;
- retrieval-only subject/predicate/object triples;
- deterministic graph node/edge rows;
- context-light-cone seed packets;
- predigestion claim packets;
- optional Hive tasks;
- optional Arango collections.

Authority boundary:

```text
txt2kg triples propose.
Hive tasks schedule.
Arango navigates.
Lean proves.
Audits admit.
```

## Local file-only run

```bash
lake script run txt2kgHiveIngest -- \
  --input docs/black_books \
  --output-dir artifacts/alexandria/txt2kg_hive/black_books \
  --source-kind blackbook \
  --extractor heuristic \
  --risk source_text \
  --emit-hive-tasks \
  --task-kind map_claim_to_owner_surface
```

## Local Ollama/vLLM-style extraction

The NVIDIA playbook uses OpenAI-compatible local endpoints for Ollama/vLLM.
This adapter follows that convention:

```bash
lake script run txt2kgHiveIngest -- \
  --input /path/to/library \
  --output-dir artifacts/alexandria/txt2kg_hive/library \
  --source-kind auto \
  --extractor ollama \
  --ollama-endpoint http://localhost:11434/v1 \
  --ollama-model llama3.1:8b \
  --risk source_text \
  --emit-hive-tasks
```

Use `--extractor auto` to try the local LLM endpoint first and fall back to the
deterministic heuristic extractor if the endpoint is unavailable.

## Optional Arango hydration

```bash
lake script run txt2kgHiveIngest -- \
  --input /path/to/library \
  --output-dir artifacts/alexandria/txt2kg_hive/library \
  --source-kind auto \
  --extractor auto \
  --emit-hive-tasks \
  --ingest-arango
```

This writes retrieval-only collections:

```text
txt2kg_sources
txt2kg_chunks
txt2kg_triples
txt2kg_entities
txt2kg_relationships
```

These collections are not proof authority.

## Context-light-cone seeds

Every run also writes:

```text
context_light_cone_seed.jsonl
```

These packets are the handoff point from unconscious graph retrieval to the
SCC-first context/light-cone lane.  They require descent back to raw Lean before
any theorem work:

```text
txt2kg seed
  -> SCC anchor
  -> upstream/downstream cone
  -> raw Lean witness descent
  -> proposal packet
  -> Lean/build/audit gates
```

Forbidden authority jumps:

```text
graph_is_proof
triple_is_theorem
hive_task_is_admission
```

## Smoke test

```bash
python3 -m py_compile tools/alexandria/txt2kg_hive_ingest.py
```

```bash
python3 tools/alexandria/txt2kg_hive_ingest.py \
  --input /tmp/txt2kg_fixture.md \
  --output-dir /tmp/txt2kg_hive_smoke \
  --extractor heuristic \
  --risk source_text \
  --emit-hive-tasks
```
