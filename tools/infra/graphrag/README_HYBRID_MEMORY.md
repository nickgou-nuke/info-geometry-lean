# InfoGeometry Hybrid GraphRAG Memory

This overlay combines five retrieval surfaces:

```text
exact hashes
graph incidence
RDF-style triples
text search
vector search
```

It is a navigation and audit layer over the existing ExprArango / wire-topology
exports.  It is not proof authority.

IGX is only a partial shallow implementation of the larger VAST/robust tooling
system; the layered memory here is a fragmentary retrieval substrate, not the
final platform.

## Layer contract

```text
Lean kernel / compiled declarations
  -> proof authority

ig_nodes / ig_edges
  -> raw expression and declaration graph

ig_wires / ig_gates / ig_wire_edges
  -> dual wire/gate topology

ig_hashes / ig_logic_tokens / ig_decl_topologies
  -> exact symbolic identity and topology buckets

ig_text_index_docs / ig_hybrid_docs
  -> lexical and docstring retrieval

ig_logic_vectors / ig_embedding_docs
  -> approximate dense retrieval candidates
```

Hashes are exact symbolic addresses.  They are not cosine vectors.

Vectors are approximate retrieval features.  Every vector result must be
explained by exact hashes, shared logic tokens, graph incidence, or Lean source
descent before it can inform an implementation decision.

## Physical graph vs logical projections

Do not split the canonical ExprArango export into separate physical collections
by default.  The physical graph is:

```text
ig_nodes
ig_edges
```

The common entity collections are logical projections:

```text
expr_nodes      := ig_nodes WHERE graphKind = "expr"
decl_nodes      := ig_nodes WHERE graphKind = "decl"
binder_nodes    := ig_nodes WHERE graphKind = "expr"
                   AND exprTag IN ["lam", "forallE", "letE"]
bound_by_edges  := ig_edges WHERE kind = "bind" AND role = "bound_by"
const_ref_edges := ig_edges WHERE kind = "const_ref"
```

This preserves compatibility with `ExprArangoExport.lean` and the existing
ingest tools.  RDF, text, vector, and dual-wire collections are overlays or
projections, not replacements for the raw graph.

## Optional projection collections

The existing repo already has the raw and dual graph collections.  This overlay
only assumes these optional collections when a deployment wants hybrid memory:

```text
ig_rdf_triples
ig_hybrid_docs
ig_embedding_docs
```

`ig_rdf_triples` is an edge collection.  It stores RDF-style predicates as
Arango-native edges:

```json
{
  "_from": "ig_wires/wire_...",
  "_to": "ig_gates/gate_...",
  "predicate": "passes_through_gate",
  "incidenceHash": "sha256:...",
  "deBruijnIdx": 0
}
```

`ig_hybrid_docs` is a text-search document collection for names, docstrings,
pretty types, canonical expression strings, and source snippets.

`ig_embedding_docs` stores dense vectors for vector indexes.  It should also
store the exact hashes that explain the vector hit:

```json
{
  "_key": "emb_decl_...",
  "kind": "decl",
  "decl": "InfoGeometry.Canonical.Example.theorem",
  "module": "InfoGeometry.Canonical.Example",
  "embedding": [0.01, -0.2],
  "deBruijnHash": "sha256:...",
  "shapeHash": "sha256:...",
  "alphaLocalHash": "sha256:...",
  "hashes": ["sha256:..."]
}
```

## Query atlas

The AQL snippets are in:

```text
tools/infra/graphrag/hybrid_memory_queries.aql
```

They cover:

```text
hash bucket -> declaration/topology descent
exact hash OR vector-near retrieval
RDF predicate traversal
text-search -> topology pivot
same words + same hash + same wire context
forbidden Type III / StandardForm leakage audit
vector hit explanation via shared exact tokens
translation candidate -> raw Lean owner descent
```

## Vector index note

ArangoDB vector support is deployment/version dependent.  Create vector indexes
only after `ig_embedding_docs.embedding` is populated and the server has vector
index support enabled.

Use exact-token explanation after vector retrieval:

```text
vector hit
  -> shared logic tokens
  -> shared topology hashes
  -> wire/gate incidence
  -> Lean source descent
```

## Audit rule

The hybrid layer can say:

```text
this declaration is similar
this declaration shares a hash
this declaration has a suspicious gate
this declaration is near a forbidden region
```

It cannot say:

```text
this theorem is proved
this interpretation is globally valid
this vector neighbor is a safe rewrite
```

Those claims require Lean owners and targeted Lean/lake validation.

## Production audit starting point

Start with the raw `ig_nodes` / `ig_edges` leakage audit before using dense
vectors.  Query `6b` in:

```text
tools/infra/graphrag/hybrid_memory_queries.aql
```

walks from declaration roots through AST/constant-reference edges and flags
Type III / StandardForm / Tomita / KMS declarations that mention configured
trace, determinant, or density constants without a configured witness constant.

This is heuristic.  The follow-up is always:

```text
raw graph hit
  -> Lean owner surface
  -> explicit finite/core/cocycle/readout witness check
  -> targeted Lean/lake validation
```
