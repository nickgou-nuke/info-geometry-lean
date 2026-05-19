# InfoGeometry GraphRAG seed overlay

This directory contains the content-addressable GraphRAG seed layer for the
InfoGeometry Lean repository.

IGX is only a partial shallow implementation of the larger VAST/robust tooling
system. Treat everything here as a fragmentary retrieval-and-audit substrate,
not as a complete platform.

It is an overlay on the existing DAG/Expr Arango surface:

```text
lean/DAG/ExprArangoExport.lean
  -> artifacts/expr-graph/arango/ig_nodes.jsonl
  -> artifacts/expr-graph/arango/ig_edges.jsonl
  -> tools/infra/arango_expr_graph_ingest.py
```

The GraphRAG overlay does not replace Lean, the DAG subsystem, or the expression
graph ingest.  It adds:

```text
ig_hashes
ig_concepts
ig_principles
ig_phases
ig_builds
```

and additional edge kinds in `ig_edges`:

```text
has_hash
same_hash_as
reifies
calibrates
guards
depends_on_principle
chronology
build_mentions
owner_of
imports
```

## Bootstrap

```bash
arangosh --server.database InfoGeometry \
  --javascript.execute tools/infra/graphrag/arango_graphrag_bootstrap.js
```

The bootstrap is idempotent.  It creates missing collections, indexes, the
`InfoGeometryTheoryGraph` named graph, and seed concept/principle rows.

## Files

```text
arango_graphrag_bootstrap.js
  Idempotent Arango bootstrap for KM/hash overlay collections and indexes.

graphrag_queries.aql
  Seed AQL snippets for hash lookup, concept linking, duplicate theorem
  detection, lineage traversal, and Type III leakage audit.

lean_graph_record_schema.json
  JSON schema for overlay records produced by future sidecars.

sample_module_export.json
  Example record bundle for the affine O55 closure theorem.

lean_to_json_sidecar_design.md
  Sidecar design notes for de Bruijn hash extraction and logicVector generation.
```

## Hash discipline

Cryptographic de Bruijn hashes are exact logical addresses, not vector embeddings.

Use them for:

```text
exact equality
content addressing
duplicate theorem statement detection
owner hygiene
```

Use `logicVector` for approximate theorem discovery.  A `logicVector` is a
deterministic dense feature-hash vector derived from the multiset of
sub-expression hashes.

## Public lineage, not private chain-of-thought

The graph stores public audit lineage:

```text
design decisions
module chronology
theorem dependencies
architectural principles
certificate boundaries
```

It must not store private scratchpad reasoning or unverifiable internal
reasoning transcripts.

## First query to wire into GraphRAG

```text
Why is the O(5,5) / Cl(5,5) affine extension witness-gated rather than an automatic theorem?
```

Expected graph route:

```text
concept_o55_affine_closure
-> affine_closure_requires_O55 declaration
-> principle_witness_gated_affine_o55
-> principle_lean_is_authority
```

## Next implementation step

Add a Lean sidecar or extend `ExprArangoExport.lean` to emit hash overlay rows:

```text
ig_hashes.jsonl
ig_hash_edges.jsonl
ig_concept_edges.jsonl
```

The sidecar must record `normalization`, `leanVersion`, `mathlibVersion`, and
`quality` for every hash row.
