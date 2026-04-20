# Alexandria Library Pipeline

Alexandria is the second Arango lane for semantic digestion and retrieval.

It is intentionally separate from the operational DAG / infotree export pipeline.

## Role separation

- primary Arango lane: operational DAG, infotree ingestion, graph process memory
- Alexandria lane: semantic chunking, theorem/proof/hypothesis library, hybrid retrieval packets

## Components

- `tools/alexandria/semantic_ingest.py` parses text/markdown into semantic chunks
- `tools/alexandria/arango_ingest.py` creates Alexandria collections and ingests records
- `tools/alexandria/retrieve_context.py` builds raw hybrid context packets from vector-like lexical similarity plus graph adjacency
- `configs/alexandria/docker-compose.yml` launches a second ArangoDB instance on port 8530 by default

## First-pass schema

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

## Intended use

1. Start the second Arango instance.
2. Digest Blackbook-style markdown/text corpora into theorem-aware chunks.
3. Store chunks, extracted entities, adjacency, and lightweight semantic signals.
4. Build raw context packets for Alcheme, Socratic dialogue, and later theorem crystallization.

## Start ArangoDB

```bash
cd configs/alexandria
cp .env.example .env
docker compose up -d
```

## Ingest a corpus

```bash
python3 tools/alexandria/semantic_ingest.py \
  --input docs/black_book_payload_chapter.md \
  --output artifacts/alexandria/blackbook_payload

python3 tools/alexandria/arango_ingest.py \
  --input-dir artifacts/alexandria/blackbook_payload
```

## Retrieve a context packet

```bash
python3 tools/alexandria/retrieve_context.py \
  --query "constructive drazin local weyl symmetry" \
  --input-dir artifacts/alexandria/blackbook_payload
```

## Notes

This first pass uses theorem-aware semantic splitting plus lexical similarity and explicit graph adjacency.
It is designed to be extended later with embeddings, vector indexes, and crystallized theorem overlays.
