# OpenClaw Lean Brain Adapter

`tools/infra/openclaw_lean_brain_ingest.py` indexes Lean source corpora into an
OpenClaw-compatible ArangoDB memory graph.

The upstream OpenClaw schema is mirrored:

- vertices: `memories`, `entities`, `sessions`, `daily_logs`
- edges: `memory_edges`, `entity_edges`
- graph: `brain_graph`

This is a retrieval and navigation layer only. Lean source files, compiled
declarations, and existing repo graph artifacts remain the proof authority.

## Safe Probes

Index only a few local files without touching Arango:

```bash
python3 tools/infra/openclaw_lean_brain_ingest.py \
  --dry-run \
  --root lean \
  --max-files 5
```

Probe repo Lean, detected Mathlib roots, and external refs:

```bash
python3 tools/infra/openclaw_lean_brain_ingest.py \
  --dry-run \
  --root lean \
  --include-mathlib \
  --include-external-refs \
  --max-files 20
```

## Ingest

Write to the default OpenClaw database `openclaw_brain`:

```bash
python3 tools/infra/openclaw_lean_brain_ingest.py \
  --root lean \
  --include-mathlib \
  --include-external-refs \
  --batch-size 1000
```

Use an isolated prefixed graph for tests:

```bash
python3 tools/infra/openclaw_lean_brain_ingest.py \
  --root lean \
  --collection-prefix test_openclaw \
  --drop-existing
```

## Corpus Discovery

The default local root is `lean`.

`--include-mathlib` uses the first valid checkout found in this order:

- `.lake/packages/mathlib`
- `external_refs/atlas-lean/.lake/packages/mathlib`
- `external_refs/mathlib`

Use repeated `--mathlib-root` flags only when deliberately indexing multiple
Mathlib checkouts.

`--include-external-refs` scans `external_refs` and skips nested `.lake`
directories unless `--include-nested-lake` is set. This avoids accidental
duplicate indexing of dependency checkouts.

## Embeddings

The default `--embedding-mode hash` uses deterministic feature hashing with
dimension `384`. It is stable and local, but it is lexical, not a neural
sentence-transformer embedding.

Use `--embedding-mode none` if the OpenClaw runtime will generate embeddings
with its own model later.

## Authority Boundary

Every inserted memory row carries:

```text
authority = navigation_context_only_not_proof_authority
```

Graph proximity, vector search, and imported external modules are candidate
context only. Kernel-checked Lean declarations decide truth.
