# Alexandria Skill

Alexandria is the repository's semantic digestion and retrieval lane for Black Books, theorem notes, and other research prose.

It is distinct from the operational DAG / raw infotree Arango lane.

## Purpose

Use Alexandria when the task is to:
- digest prose corpora into semantic chunks
- organize theorem, proof, hypothesis, and concept neighborhoods
- build retrieval packets for Alcheme, Socratic dialogue, or theorem distillation
- explore semantic neighborhoods before formal closure

Do not use Alexandria as the truth authority. Lean source and successful builds remain the only truth gate.

## Surfaces

- `tools/alexandria/semantic_ingest.py`
  - turns markdown/text into section-aware semantic chunks
- `tools/alexandria/arango_ingest.py`
  - ingests Alexandria JSONL artifacts into the second Arango instance
- `tools/alexandria/retrieve_context.py`
  - basic lexical plus adjacency retrieval
- `tools/alexandria/graph_context_rank.py`
  - graph reranking from lexical seed chunks
  - supports cuGraph-compatible NetworkX backend activation
- `configs/alexandria/docker-compose.yml`
  - second ArangoDB instance, default port `8530`

## Current schema

Document collections:
- `alexandria_documents`
- `alexandria_sections`
- `alexandria_chunks`
- `alexandria_entities`

Edge collections:
- `alexandria_document_section_edges`
- `alexandria_section_chunk_edges`
- `alexandria_chunk_entity_edges`
- `alexandria_chunk_adjacent_edges`
- `alexandria_entity_relation_edges`

## Standard flow

### 1. Digest a corpus

```bash
python3 tools/alexandria/semantic_ingest.py \
  --input docs/black_books/00w_drazin_penrose_lightcone_projectors_and_casimir_gravity.md \
  --input docs/black_books/00g_local_symmetry_weyl_gauge_and_recent_arxiv_threads.md \
  --output artifacts/alexandria/drazin_weyl_slice
```

### 2. Optional, ingest into the second Arango instance

```bash
python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/alexandria/drazin_weyl_slice
```

### 3. Build a retrieval packet

Basic retrieval:

```bash
python3 tools/alexandria/retrieve_context.py \
  --query "constructive drazin local weyl symmetry" \
  --input-dir artifacts/alexandria/drazin_weyl_slice
```

Graph reranking:

```bash
/home/goutev/arango-graph-venv/bin/python tools/alexandria/graph_context_rank.py \
  --query "constructive drazin local weyl symmetry penrose projector weyl compatible" \
  --input-dir artifacts/alexandria/drazin_weyl_slice \
  --use-gpu
```

## GPU graph runtime

The compatible graph runtime lives in:
- `/home/goutev/arango-graph-venv`

Use the safe backend variables instead of `NX_CUGRAPH_AUTOCONFIG=True`:

```bash
NETWORKX_BACKEND_PRIORITY_ALGOS=cugraph \
NETWORKX_BACKEND_PRIORITY_GENERATORS=cugraph \
NETWORKX_FALLBACK_TO_NX=true \
NETWORKX_CACHE_CONVERTED_GRAPHS=true \
/home/goutev/arango-graph-venv/bin/python tools/alexandria/graph_context_rank.py ...
```

`graph_context_rank.py --use-gpu` also applies those variables before importing `networkx`.

## Current limitations

- entity extraction is still light
- relation extraction is mostly adjacency plus shared-entity co-linking
- retrieval is currently lexical + graph walk, not full embedding/vector search
- theorem/proof/hypothesis typing is heuristic

## Next upgrades

- richer entity extraction for symbols, modules, theorem names, hypotheses
- relation extraction with confidence tags
- vector embedding storage and hybrid vector+graph recall
- Socratic dossier rendering from the ranked packet
- crystallized theorem alignment layer on top of Alexandria memory
