# DAG Subsystem README

This directory implements a graph-theoretic analysis engine for Lean environments and elaborated proof artifacts.

The DAG subsystem is not only a dependency exporter. It includes:
- environment-to-graph extraction,
- SCC condensation,
- topological and dominator analysis,
- influence/vulnerability metrics,
- expression disassembly,
- structural isomorphism hashing,
- simplicial-complex style topological invariants,
- block-level slicing over elaborated command snapshots,
- JSON export and server RPC integration.

## 1) Conceptual Model

At the center are two graph forms:

1. `Graph alpha` in `Basic.lean`
- Nodes are declarations or synthetic entities.
- Edges are typed by `EdgeKind` (`type` or `value`).

2. `HydratedGraph alpha` in `Basic.lean` + `Hydrate.lean`
- Adds SCC decomposition, condensed DAG, predecessor map, topological order, and dominator sets.

This gives a progression:

Environment -> Graph -> SCC DAG -> Metrics/Queries/Exports

## 2) Layered Architecture

### Layer A: Graph Kernel
- `Basic.lean`: graph structures and extraction from Lean `Environment`.
- `Util.lean`: dependency walkers and generated-name filtering helpers.
- `SCC.lean`: Tarjan SCC decomposition.
- `Topo.lean`: topological sorting.
- `Dominators.lean`: dominator analysis (bit-vector implementation).
- `Hydrate.lean`: composes the above into `HydratedGraph`.

### Layer B: Graph Analysis
- `Analysis.lean`: path counts, distance maps, influence and vulnerability summaries, skeleton extraction.
- `Impact.lean`: forward and reverse reachability from a chosen node.

### Layer C: Expression Shape and Topology
- `Disassembler.lean`: transforms `Expr` into explicit node/edge shape graph.
- `Isomorphism.lean`: Weisfeiler-Lehman rounds for structural hash comparison.
- `TwoComplex.lean`: build 2-complex, boundary operators, Euler characteristic, Betti-1.
- `Betti.lean`: end-to-end expression homology pipeline.

### Layer D: Search and Query
- `SearchCore.lean`: shared search primitives (name collection, substring query, case-insensitive predicate).
- `Search.lean`: tokenized/fuzzy ranking and hybrid fallback search.
- `SearchRank.lean`: lightweight ranked substring search utility.
- `FinalSearch.lean`: multi-query runner with preview caps.
- `QueryEngine.lean`: small monadic expression-traversal DSL.

### Layer E: Export and Serving
- `ExportDecls.lean`: declaration inventory + dependencies.
- `ExportForwardGraph.lean`: forward graph JSON export.
- `GlobalDisassembler.lean`: stream disassembly to JSONL files.
- `JsonInstances.lean`: JSON codecs.
- `BlockExport.lean`: command-block slicing, tactic morphisms, block DAG, quiver emitters.
- `ServerExport.lean`: RPC methods over editor snapshots.
- `SkeletonExport.lean`: "true skeleton" export via vulnerability ranking.

### Auxiliary
- `Functor.lean`: categorical morphism recognition and commutative-square search.
- `Indexer.lean`: patched indexing pipeline with morphism extraction and graph JSON.
- `FindFinrank.lean`, `dump_graph_prefix.lean`, `KernelExtract.lean`: utility and legacy/support modules.

## 3) Example Workflow

This example builds a practical theory map and then isolates core statements.

### Step 1: Export the forward declaration graph

```bash
lake env lean --run lean/DAG/ExportForwardGraph.lean \
  InfoGeometry docs-map/module_graph.json InfoGeometry
```

### Step 2: Extract the vulnerability-ranked skeleton

```bash
lake env lean --run lean/DAG/SkeletonExport.lean \
  InfoGeometry InfoGeometry docs-map/skeleton.json
```

### Step 3: Slice minimal source context for a target declaration

```bash
lake env lean --run lean/DAG/BlockExport.lean \
  --slice <Target.Name> lean/InfoGeometry/Canonical/Projective.lean
```

The resulting slice keeps only blocks needed to derive `<Target.Name>`, plus ambient context blocks when applicable.

## 4) "Sources, Sinks, Chains" in This DAG Subsystem

At module-import topology level:
- Primary hub: `Basic.lean` (foundation imported by most modules).
- Secondary hub: `Util.lean`.
- Major orchestrators: `BlockExport.lean`, `Hydrate.lean`, `Functor.lean`.

Representative dependency chains:

1. Extraction and hydration chain
- `Basic` -> `SCC` + `Topo` + `Dominators` -> `Hydrate`

2. Structural risk chain
- `Hydrate` -> `Analysis` -> `SkeletonExport`

3. Expression topology chain
- `Disassembler` -> `TwoComplex` -> `Betti`

4. Categorical/shape chain
- `Disassembler` + `Isomorphism` + `QueryEngine` -> `Functor`

5. Editor slicing chain
- `BlockExport` -> `ServerExport`

## 5) Test-First Development Policy for DAG Refactors

Use this policy for each canonicalization/generalization step:

1. Add or update targeted tests first.
2. Run only impacted modules/tests.
3. Implement minimal refactor.
4. Re-run the same tests.
5. Run broader DAG build.

Current first-step canonicalization (implemented):
- Introduced `SearchCore.lean`.
- Refactored `Search.lean`, `SearchRank.lean`, and `FinalSearch.lean` to consume shared search helpers.
- Added `SearchCoreTests.lean` for deterministic behavior checks.

## 6) Near-Term Implementation Plan

### Phase 1 (done)
- Shared search core extraction.
- Search module deduplication.

### Phase 2
- Canonical expression dependency fold extraction for:
  - `Util.collectDeps`,
  - `Basic.collectExprConsts`,
  - `Indexer.collectConsts`.

### Phase 3
- Unify local/global expression disassembly logic (`Disassembler` and `GlobalDisassembler`).

### Phase 4
- Consolidate context-block heuristics shared by `BlockExport` and `ServerExport`.

### Phase 5
- Optional umbrella/API normalization in `DAG.lean`.

## 7) Build/Validation Commands

Run focused checks:

```bash
lake build DAG.SearchCore DAG.SearchCoreTests DAG.Search DAG.SearchRank DAG.FinalSearch
```

Run broader DAG build:

```bash
lake build DAG
```

## 8) Notes on Scope

- This DAG subsystem tracks declaration-level and expression-level structures.
- It does not replace theorem proving; it analyzes theory topology, dependencies, and structural shape.
- For large exports, JSON/JSONL outputs are designed to feed downstream tools (graph databases, dashboards, audits).
