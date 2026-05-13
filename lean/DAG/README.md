# DAG Subsystem

`lean/DAG/` is the Lean-side graph export layer for this repository.
It is not the sole owner of architectural grammar anymore; depth legality now starts in:
- [lawful-flow-glossary.md](../../docs/lawful-flow-glossary.md) for constitutive boundary/defect tag semantics
- [Architecture.lean](../InfoGeometry/Meta/Architecture.lean)
- [Audit.lean](../InfoGeometry/Audit.lean)

For the current repo-wide status of operational docs, generated artifacts, and
compatibility wrappers, see [docs/RepositoryMemoryMap.md](../../docs/RepositoryMemoryMap.md).

The DAG subsystem exists because this repository is one theory spread across many representation surfaces.
Its job is to externalize memory about ownership, adjacency, transport, and coherence so that context can be recovered after local state is lost.
It is an audit layer for morphisms, not an alternate source of mathematical truth.

## Why This Is Not Just Metadata

The exported declaration graph is not merely bookkeeping around the Lean codebase.
It is a finite, explicit object induced by kernel-checked declarations and their dependency structure.

That makes higher-level analysis legitimate on the graph representation itself:
- homological summaries such as cycles and Betti-style structure
- spectral summaries such as Laplacians and gap-like bottlenecks
- categorical and exactness-oriented views over recognized morphism structure
- causal and process-flow summaries over roots, shells, defects, and transport corridors

This is useful because the graph can expose global structural facts that ordinary file-by-file reading cannot surface by itself.
It remains subordinate to Lean source:
- Lean source and the native audit decide what is true
- graph invariants help reveal how the checked theory is organized, stressed, and routed

## File Inventory

### Core Graph Construction

| File | Purpose |
|------|---------|
| `Basic.lean` | `EdgeKind` enum, `Graph α`, `HydratedGraph α` types; `buildGraphFromEnv()` extracts declarations and edges from the Lean environment; `collectExprConsts()` recursively finds constants in expressions |
| `SCC.lean` | Tarjan's algorithm for strongly connected component decomposition |
| `Hydrate.lean` | Chains Tarjan → SCC-to-DAG → topological sort → dominator computation into `HydratedGraph` |
| `Topo.lean` | BFS in-degree topological sort on the compressed SCC DAG |
| `Dominators.lean` | Bitset-based dominator computation for impact and vulnerability analysis |
| `Util.lean` | Shared helpers (array operations, name utilities) |

### Analysis

| File | Purpose |
|------|---------|
| `Analysis.lean` | `pathCountFrom`, `distanceMap`, `influenceFrom`, `vulnerabilityOf`, `rootSet`, `capstoneSet` |
| `Impact.lean` | Forward/reverse BFS reachability lifted from SCC level back to declaration level |
| `Betti.lean` | Betti-number / homological rank computations on the graph |
| `TwoComplex.lean` | 2-complex (cell complex) structure over the DAG |

### Export Pipelines

| File | Output | Description |
|------|--------|-------------|
| `Indexer.lean` | `full_graph.json`, `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl`, `types.jsonl`, `structural-topology.json` | Main export pipeline; `DeclNode`, `DepEdge`, `Morphism`, `TypeNode` records; recognizes morphisms (Hom/Equiv/Iso/Map patterns) |
| `SkeletonExport.lean` | `skeleton.json` | Vulnerability-ranked theorem skeleton (`SkeletonRow`: name, vulSrcs, vulPaths) |
| `StructuralExport.lean` | `structural-topology.json` | SCC-level metadata: depth spread, dominators, root witnesses, layer membership |
| `ProcessFlowExport.lean` | `process-flow/*.jsonl` | Rich v4 schema: 8 dependency roles, boundary/locality/polarity/defect classifications, `DerivationalRole`; writes the constitutive process-flow export consumed by downstream Python derivations |
| `ExprArangoExport.lean` | `ig_nodes.jsonl`, `ig_edges.jsonl`, `metadata.json` | Expression-level Arango export (declarations + Expr DAG) with De Bruijn `bvar` annotations and explicit `bound_by` edges; tolerates unresolved binders by marking records as `quality="broken"` |
| `BlockExport.lean` | block-level JSON | File slicing: `Block` (text span, produced decls, deps, spine tags, tactics, docstrings) with `ScopeFrame` nesting |
| `RepresentationDepthExport.lean` | `representation-depth-tags.json` | Lean-enforced depth grammar tags projected onto the declaration DAG |
| `KernelEquivalenceExport.lean` | `lean-kernel-equivalence.jsonl` | Native certificate exporter for candidate declaration pairs; imports the requested module and promotes a pair only when `Lean.Meta.isDefEq` verifies the requested type/value mode |
| `TripleSystem.lean` | — | Lean-native core definition of typed subject-predicate-object incidence systems and triple homomorphisms |
| `TripleHomomorphismExport.lean` | `triple-homomorphism-audit.json`, `missing-triples.jsonl` | Finite Lean-native checker for JSONL/RDF-style triple homomorphism candidates; verifies that every mapped source triple exists in the target triple set |
| `RootOrderExport.lean` | root-order JSON | True root ordering for causal reports |
| `ExportDecls.lean` | declaration metadata | Lightweight declaration export |
| `ExportForwardGraph.lean` | forward adjacency JSON | Forward edge-list graph export |
| `ServerExport.lean` | server-compatible JSON | Export format for external server consumption |
| `JsonInstances.lean` | — | `ToJson`/`FromJson` instances for `Graph`, `HydratedGraph`, `EdgeKind`, `Name` |
| `ConeCommand.lean` | command output | Interactive declaration-cone commands: bounded `#deps_dot`, `#deps_json`, and `#cone_json` for causal-diamond prompt context |

### Search Infrastructure

| File | Purpose |
|------|---------|
| `SearchCore.lean` | Basic substring search (case-insensitive/case-sensitive), name collection |
| `Search.lean` | Query tokenization (camelCase, underscore, hyphen splitting), token-weighted ranking |
| `SearchRank.lean` | Single/multi-query search with preview caps |
| `FinalSearch.lean` | Multi-query batch environment search |
| `QueryEngine.lean` | Structured query evaluation and filtering over graph metadata |

### Algebraic / Categorical Extensions

| File | Purpose |
|------|---------|
| `CategoryBridge.lean` | Maps declarations to `CategoryTheory.Quiver`; verifies morphism composition in `MetaM` |
| `Functor.lean` | Functorial structure between graph layers |
| `ExactMorphism.lean` | Exact-sequence detection in morphism chains |
| `Isomorphism.lean` | Iso detection and equivalence tracking |
| `LiftNaturality.lean` | Naturality verification for lifted morphisms |
| `KernelExtract.lean` | Kernel/cokernel extraction from exact sequences |
| `SubgraphMatch.lean` | Subgraph pattern matching |
| `FindFinrank.lean` | Finite-rank detection |
| `Disassembler.lean` | Expression-level disassembly for edge extraction |
| `GlobalDisassembler.lean` | Environment-wide disassembly pass |
| `SemanticServerRpc.lean` | RPC interface for semantic graph queries |

### Tests

| File | Purpose |
|------|---------|
| `SearchCoreTests.lean` | Unit tests for search infrastructure |
| `CategoryBridgeTest.lean` | Integration tests for category bridge |
| `ExactMorphismTest.lean` | Tests for exact morphism detection |
| `IntegrationTest.lean` | End-to-end DAG pipeline tests |

## Graph Layers

Keep these graph views distinct:
1. declaration DAG: atomic declaration-to-declaration dependency truth
2. structural topology: SCC condensation, layers, dominators, witness paths
3. source-sink correspondence: packet and carrier incidence built downstream in Python
4. semantic export: heavy-file block structure for frontier work
5. representation-depth overlays: Lean-enforced depth grammar projected onto the authoritative DAG
6. process-flow export: edge-local transport evidence, bounded path candidates, and localized defect rows

## Authoritative Export Path

The declaration graph is refreshed with:

```bash
python3 tools/infra/refresh_decl_graph.py
```

which runs the Lean-side indexer and writes:
- `artifacts/dag/full_graph.json`
- `artifacts/dag/index/decls.jsonl`
- `artifacts/dag/index/edges.jsonl`
- `artifacts/dag/index/morphisms.jsonl`
- `artifacts/dag/index/types.jsonl`
- `artifacts/dag/structural-topology.json`

Downstream Python tooling then derives source-sink, causal, theorem-surface, semantic quotient, and representation-depth reports.
Those reports should agree with the Lean-native audit, not replace it.

Candidate equivalence promotion must go through the Lean/kernel lane:

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

The input JSONL rows are `{ "sourceDecl": "...", "targetDecl": "..." }`.
The output records `kernelTypeDefEq`, `kernelValueDefEq`, `leanVerified`,
`safeForAutoRewrite`, and `verificationTier`.  Python-derived hashes, role
tokens, graph SCCs, and vector neighborhoods may propose candidate pairs, but
they are not allowed to set `leanVerified`; only this Lean-native exporter or a
future Lean-native checker with the same kernel authority may do that.

For finite RDF/Arango-style triple preservation, use the Lean-native triple
homomorphism checker:

```bash
lake env lean --run lean/DAG/TripleHomomorphismExport.lean \
  artifacts/triples/source.jsonl \
  artifacts/triples/target.jsonl \
  artifacts/triples/maps.jsonl \
  artifacts/triples/triple-homomorphism-audit.json \
  artifacts/triples/missing-triples.jsonl
```

This checker validates the finite preservation condition:

```text
(s, p, o) in source
  implies
(F_Obj(s), F_Rel(p), F_Obj(o)) in target
```

It is the native preservation gate for exported triple rows.  It does not
replace theorem checking: theorem-level equivalence still goes through
`KernelEquivalenceExport` or another Lean/kernel certificate path.

For a small Lean-native causal cone around one declaration, import the command
surface:

```lean
import DAG.ConeCommand

#deps_dot Some.Theorem
#deps_json Some.Theorem
#cone_json Some.Theorem
```

The interactive commands are bounded by default.  They emit the
syntactic/kernel declaration graph with orientation `dependency -> user`.
They are prompt/audit context only: graph proximity is not proof, and Lean
kernel checking remains the proof authority.

Keep graph orientations distinct:
- declaration DAG and hydrated topology: `declaration/component -> dependency`;
- cone DOT/JSON command view: `dependency -> user`, for causal-flow readability;
- `lean-graph` adapter: `node.references = dependencies`, matching
  `lean-graph`'s extracted-data schema.

For Arango-backed prompt packets, emit JSON/Markdown with:

```bash
python3 tools/infra/arango_causal_chiral_cone_prompt.py \
  --decl InfoGeometry.Some.Module.some_theorem \
  --json-out artifacts/cones/some_theorem.json \
  --md-out artifacts/cones/some_theorem.md
```

Then render a local visual inspection page before giving the packet to an LLM:

```bash
python3 tools/infra/visualize_causal_chiral_cone_packet.py \
  --json-in artifacts/cones/some_theorem.json \
  --html-out artifacts/cones/some_theorem.html
```

The HTML view is an offline SVG/debug surface for the causal diamond and its
Hodge/chiral/Dirac/process overlays.  It is deliberately downstream of Arango
and upstream of the LLM prompt.

To inspect hydrated SCC DAG slices in the external `lean-graph` viewer, project
the hydrated topology into `lean-graph`'s simple JSON schema:

```bash
lake script run leanGraphSlice \
  --apex InfoGeometry.Singular.Drazin.IsDrazinInverse \
  --backward-depth 2 \
  --forward-depth 1 \
  --max-nodes 180 \
  --out artifacts/lean-graph/hydrated-drazin-cone.json
```

or for a module/prefix slice:

```bash
lake script run leanGraphSlice \
  --prefix InfoGeometry.Arithmetic.PrimitiveSouriauZeta \
  --max-nodes 180 \
  --out artifacts/lean-graph/hydrated-primitive-souriau-zeta.json
```

Then open the generated JSON in `external_refs/lean-graph/target/debug/lean-graph`
via `File -> Open extracted data`.
The adapter also writes a `.meta.json` sidecar recording source artifact,
orientation, slice mode, parameters, and reference-closure validation.

The constitutive process-flow layer is exported with:

```bash
lake env lean --run lean/DAG/ProcessFlowExport.lean InfoGeometry.Audit artifacts/dag/process-flow
python3 tools/infra/generate_process_flow_report.py
```

This layer is for:
- edge-local transport evidence
- event aggregation over observed edges
- bounded ancestry/path candidates
- localized defect evidence
- derived comparison and cocycle reports downstream

The process-flow export writes:
- `artifacts/dag/process-flow/flow-edges.jsonl`
- `artifacts/dag/process-flow/process-events.jsonl`
- `artifacts/dag/process-flow/lawful-path-candidates.jsonl`
- `artifacts/dag/process-flow/defects.jsonl`

The downstream Python report step then derives:
- `artifacts/dag/process-flow/flow-cocycles.jsonl`
- `artifacts/dag/process-flow/comparison-candidates.jsonl`

The direct Arango expression graph is exported with:

```bash
lake env lean --run lean/DAG/ExprArangoExport.lean DAG.Basic DAG artifacts/expr-graph/arango-smoke 50 true
```

For the full repo namespace surface:

```bash
lake env lean --run lean/DAG/ExprArangoExport.lean InfoGeometry.Audit InfoGeometry artifacts/expr-graph/arango 0 true
```

Then ingest to Arango:

```bash
python3 tools/leantrail/arango_ingest.py \
  --input-dir artifacts/expr-graph/arango \
  --database infogeometry \
  --nodes-collection ig_nodes \
  --edges-collection ig_edges \
  --drop-existing
```

`ExprArangoExport` writes one node collection (`ig_nodes`) and one edge collection (`ig_edges`), with:
- decl nodes (`graphKind="decl"`)
- expr nodes (`graphKind="expr"`, `exprTag`, `deBruijnIdx`)
- structural edges (`kind="ast"`, `role=fn|arg|type|body|value|expr`)
- binding edges (`kind="bind"`, `role="bound_by"`)
- declaration root edges (`kind="decl_root"`)
- constant reference edges (`kind="const_ref"`)

## Processing Pipeline

```
Lean Environment
    │
    ▼  buildGraphFromEnv()
  Graph α  (nodes + forward adjacency)
    │
    ▼  Tarjan SCC  (SCC.lean)
  Component arrays
    │
    ▼  hydrate()  (Hydrate.lean)
  HydratedGraph α  (SCC DAG + topo order + dominators + predecessors)
    │
    ├─▶ Analysis.lean  (path counts, distance, influence, vulnerability)
    ├─▶ Impact.lean    (forward/reverse reachability)
    ├─▶ Indexer.lean   (DeclNode / DepEdge / Morphism / TypeNode → JSON)
    ├─▶ StructuralExport.lean  (SCC-level topology → JSON)
    ├─▶ SkeletonExport.lean    (vulnerability skeleton → JSON)
    └─▶ ProcessFlowExport.lean (transport evidence → JSONL)
         │
         ▼  (consumed by Python)
    tools/infra/*.py  →  reports/dag/*
```

## Trust Order

If graph-derived surfaces disagree, trust:
1. Lean source and the native audit under `lean/InfoGeometry/Meta/` and `lean/InfoGeometry/Audit.lean`
2. `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
3. `artifacts/dag/structural-topology.json`
4. `artifacts/dag/source-sink-bipartite.json`
5. `reports/dag/*`

## Current Anchor Corridor

The current long chain that should remain visible in the declaration DAG and the causal reports is:
- `PositiveMeasure -> Projective.Normalize -> PositiveRayCore -> RelativePotentialCore -> RelativePotentialCountBridge -> RelativeSurprisalOperatorLift`

The important point is not only depth. It is that the chain now contains a real owned cocycle at each adjacent rise:
- representative normalization cocycle
- count specialization cocycle
- raw operator cocycle
- averaged modular-Hamiltonian cocycle

The DAG layer should preserve that owner corridor and distinguish it from thinner reprojection tails above it.

## Intended Use

Use the DAG subsystem for:
- causal order and rooted structure
- owner and dependency analysis
- theorem-surface and shell pressure analysis
- representation-depth legality and bicategorical reporting
- process-flow transport and coherence pressure reporting

Use it to recover memory and choose the next file to read.
Do not use it to delete mathematics without reading the owner code.

Do not use a single hotspot heuristic as the whole theory map.

## Current Codebase Status

Status pointer refreshed: 2026-04-16 (Europe/Sofia). See [../../docs/CODEBASE_STATUS.md](../../docs/CODEBASE_STATUS.md) for the current build/audit state.
