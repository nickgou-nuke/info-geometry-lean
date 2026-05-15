# InfoGeometry Dual-Map Atlas

This document defines the first GraphRAG atlas layer over the existing
ExprArango and wire-topology export.

It does not create a parallel KM graph.  It uses the repo's existing derived
collections:

```text
ig_wires
ig_gates
ig_wire_edges
ig_decl_topologies
ig_hashes
ig_logic_tokens
ig_logic_vectors
```

## Interpretation

The atlas uses the dual wire/gate view:

```text
de Bruijn wires / fibers / pattern hashes  -> dual nodes
constants / binders / applications         -> gates or junctions
ig_wire_edges                              -> incidence relations
```

This is a line-graph view of the exported Lean expression topology.  It is an
audit and navigation representation only.  The Lean kernel and compiled
declarations remain the proof authority.

## Seed region

The first region is stored in:

```text
tools/infra/graphrag/seeds/spacetime_closure_region.json
```

It names the 15-module spacetime-closure corridor:

```text
Drazin/Hodge projector-arrow algebra
Souriau/KMS modular energy accounting
Hestenes-Krein real geometry and vacuum readout
Connes-Wilson / Moebius projective holonomy
D4-Hurwitz / O55 affine arithmetic socket
```

## Query file

The dual-map AQL snippets are stored in:

```text
tools/infra/graphrag/dual_map_queries.aql
```

The main query surfaces are:

```text
declaration -> wires/gates/incidence
deBruijnHash -> occurrence/fiber wires
wire -> neighboring gates
gate -> neighboring wires
declaration -> isomorphic topology candidates
declaration pair -> shared wire-token explanation
module -> sparse logic-neighborhood candidates
seed modules -> region atlas summary
Type III / StandardForm trace-det gate audit
concept -> declaration -> wire/gate descent
```

## Operational sequence

Generate the raw expression graph:

```bash
lake env lean --run lean/DAG/ExprArangoExport.lean \
  InfoGeometry.Audit InfoGeometry artifacts/expr-graph/arango 0 true
```

Ingest the raw expression graph into ArangoDB:

```bash
python3 tools/infra/arango_expr_graph_ingest.py \
  --input-dir artifacts/expr-graph/arango \
  --database infogeometry
```

Materialize the dual wire topology:

```bash
python3 tools/infra/build_dual_graph.py \
  --input-dir artifacts/expr-graph/arango \
  --output-dir artifacts/expr-graph/wire-topology
```

Ingest the derived wire topology:

```bash
python3 tools/infra/arango_wire_topology_ingest.py \
  --input-dir artifacts/expr-graph/wire-topology \
  --database infogeometry
```

Then run snippets from:

```text
tools/infra/graphrag/dual_map_queries.aql
```

## Audit rule

Wire-topology similarity is not proof.  Treat every result as one of:

```text
navigation candidate
duplication candidate
category-error candidate
owner-surface candidate
```

Any theorem-level claim still needs descent to raw Lean owners and validation by
Lean/lake.
