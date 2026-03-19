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

## 0) What This Subsystem Gives You

There are three different views of the theory, and they should not be mixed:

1. Declaration DAG
- Nodes are declarations.
- Edges are type/value dependencies.
- Use this for whole-library topology, dominators, SCCs, and coarse bottleneck analysis.

2. Block export / causal provenance
- Nodes are source command blocks.
- The exporter records which declarations each block produced.
- This is the right layer for source-level attribution and semantic slicing.

3. Semantic block graph
- Built from block export, but filtered to `primaryProduces`.
- This removes generated `_proof_*`, `match_*`, and auxiliary elaborator noise from the semantic presentation layer while keeping causal provenance intact underneath.

The practical rule is:

Declaration graph for global topology.
Semantic block graph for human-facing theory structure.

## 1) Current Trust Model

The repository now has two export paths with different trust levels:

1. In-process block export (`DAG.BlockExport.exportFile`)
- Fast and useful for small/medium files.
- Good for local slicing, quiver emission, and block-level experiments.

2. External semantic block export (`tools/semantic_block_export.py` + `DAG.ServerExport`)
- Launches a separate `lean --server` process.
- Uses RPC over editor snapshots.
- This is the authoritative path for large Mathlib-heavy modules.

For large canonical modules, the trusted path is:

Python orchestrator -> stdlib `lean --server` -> `@[server_rpc_method]` in `DAG.ServerExport` -> semantic block JSON

This process boundary matters. It avoids host/guest `[init]` collisions that can appear when trying to elaborate heavy files in-process.

## 2) Conceptual Model

At the center are two graph forms:

1. `Graph alpha` in `Basic.lean`
- Nodes are declarations or synthetic entities.
- Edges are typed by `EdgeKind` (`type` or `value`).

2. `HydratedGraph alpha` in `Basic.lean` + `Hydrate.lean`
- Adds SCC decomposition, condensed DAG, predecessor map, topological order, and dominator sets.

This gives a progression:

Environment -> Graph -> SCC DAG -> Metrics/Queries/Exports

## 3) Layered Architecture

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
- `ServerExport.lean`: RPC methods over editor snapshots, including semantic block export.
- `SemanticServerRpc.lean`: explicit builtin RPC registration shim for server integration.
- `SkeletonExport.lean`: "true skeleton" export via vulnerability ranking.

### Auxiliary
- `Functor.lean`: categorical morphism recognition and commutative-square search.
- `Indexer.lean`: patched indexing pipeline with morphism extraction and graph JSON.
- `LiftNaturality.lean`: shared lift-pattern recognizer for naturality diagnostics/promoters.
- `FindFinrank.lean`, `KernelExtract.lean`: utility and support modules.

## 4) Repository Structure Around DAG

- `lean/DAG`
  Importable engine modules.

- `lean/scripts/DAG/Exploration`
  Thin Lean executables and report generators.

- `tools/semantic_block_export.py`
  External Python LSP/RPC orchestrator for trusted semantic block export.

- `tmp/`
  Scratch harnesses and one-off helper modules that should not live in the `DAG` library.

The distinction is intentional:

`lean/DAG` is reusable library code.
`lean/scripts/DAG/...` is executable/report surface.

## 5) Primary Workflows

### Workflow A: Whole-module declaration topology

Use this when you want SCCs, dominators, and declaration-level skeletons over an import closure.

Step 1: export the forward declaration graph

```bash
lake env lean --run lean/DAG/ExportForwardGraph.lean \
  InfoGeometry docs-map/module_graph.json InfoGeometry
```

Step 2: extract the vulnerability-ranked skeleton

```bash
lake env lean --run lean/DAG/SkeletonExport.lean \
  InfoGeometry InfoGeometry docs-map/skeleton.json
```

Use this path for:
- articulation hubs,
- SCC condensation,
- vulnerability/influence rankings,
- high-level architecture audits.

### Workflow B: Source-level block slicing

Use this when you want the minimal source blocks needed for a target declaration.

```bash
lake env lean --run lean/DAG/BlockExport.lean \
  --slice <Target.Name> lean/InfoGeometry/Canonical/Projective.lean
```

The resulting slice keeps only blocks needed to derive `<Target.Name>`, plus ambient context blocks when applicable.

### Workflow C: Trusted semantic block export for a single heavy file

Use this for large canonical files where in-process elaboration is too fragile or too noisy.

```bash
python3 tools/semantic_block_export.py \
  lean/InfoGeometry/Canonical/GrandSynthesis.lean \
  reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --server-mode stdlib \
  --inject-rpc-import \
  --skip-wait-for-diagnostics \
  --timeout 900 \
  --transcript reports/dag/GrandSynthesis.semantic-block.stdlib.transcript.jsonl \
  --stderr-log reports/dag/GrandSynthesis.semantic-block.stdlib.stderr.log
```

This path yields:
- `rawBlocks`, `rawDecls`
- `rawPrimaryBlocks`
- `semanticBlockNodes`, `semanticBlockEdges`
- `semanticSkeletonNodes`
- filtered `blocks`
- filtered `skeleton`

The important operational flags are:
- `--server-mode stdlib`
  Use the standard Lean server process rather than a repo-linked custom server binary.
- `--inject-rpc-import`
  Inject `import DAG.ServerExport` into the virtual open document so the RPC method is available.
- `--skip-wait-for-diagnostics`
  Avoid blocking on diagnostic completion; the RPC itself waits on snapshots.

### Workflow D: Naturality / categorical diagnostics

Use this after tagging the semantic spine with `@[spine_morphism]` and `@[spine_functor]`.

```bash
lake env lean --run lean/scripts/DAG/Exploration/HarvestDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/LiftNaturalityDiagnostics.lean
lake env lean --run lean/scripts/DAG/Exploration/NaturalityPromoter.lean
lake env lean --run lean/scripts/DAG/Exploration/SquarePromoter.lean
```

These tools are report-only by design. They identify:
- strict unary morphism coverage,
- lift naturality seeds,
- grouped functor obligations,
- strict commutative-square candidates.

## 6) Semantic Block Export Invariants

The semantic block export now preserves a deliberate split:

- causal/dependency substrate sees `primary + aux`
- semantic presentation sees `primary` only

Concretely:
- `auxProduces` stay in `decls`, `producer`, and dependency roll-up logic
- `primaryProduces` drive semantic block nodes and semantic skeleton selection
- `primarySpineTags` gives per-primary declaration semantic tags
- `spineTags` is a deduplicated block-level summary cache

This is the key invariant that lets generated lemmas continue to carry dependency pressure without polluting the human-facing graph.

## 7) "Sources, Sinks, Chains" in This DAG Subsystem

At module-import topology level:
- Primary hub: `Basic.lean` (foundation imported by most modules).
- Secondary hub: `Util.lean`.
- Major orchestrators: `BlockExport.lean`, `Hydrate.lean`, `Functor.lean`, `ServerExport.lean`.

Representative dependency chains:

1. Extraction and hydration chain
- `Basic` -> `SCC` + `Topo` + `Dominators` -> `Hydrate`

2. Structural risk chain
- `Hydrate` -> `Analysis` -> `SkeletonExport`

3. Expression topology chain
- `Disassembler` -> `TwoComplex` -> `Betti`

4. Categorical/shape chain
- `Disassembler` + `Isomorphism` + `QueryEngine` -> `Functor`

5. Trusted semantic export chain
- `ServerExport` -> `SemanticServerRpc` -> `tools/semantic_block_export.py`

## 8) How To Read the Outputs

For declaration-level exports:
- `graph.json` or module graph JSON shows full dependency pressure.
- `skeleton.json` shows the vulnerability-ranked core.

For semantic block exports:
- `*.semantic-block.stdlib.json` is the main artifact.
- `*.stderr.log` should usually be empty.
- `*.transcript.jsonl` is the debugging/trust trace for the external server run.

Interpretation rule:
- if `semanticBlockNodes = 0` on a façade module, that is often correct
- if a heavy non-façade file returns `0`, suspect export failure
- if `stderr` is empty and `transcript` shows file progress, the server path itself is healthy

## 9) Test-First Development Policy for DAG Refactors

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

## 10) Near-Term Implementation Plan

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

### Phase 6
- Typed frontier extraction over semantic block graphs.
- Diffusion / restart-walk over purified semantic web.
- LLM-facing frontier packets for candidate bridge statements.

## 11) Build/Validation Commands

Run focused checks:

```bash
lake build DAG.SearchCore DAG.SearchCoreTests DAG.Search DAG.SearchRank DAG.FinalSearch
```

Run semantic export tooling:

```bash
lake build semanticBlockExport semanticBlockServer
lake build scripts.DAG.Exploration.HarvestDiagnostics
lake build scripts.DAG.Exploration.LiftNaturalityDiagnostics
lake build scripts.DAG.Exploration.NaturalityPromoter
```

Run broader DAG build:

```bash
lake build DAG
```

Run umbrella canonical validation:

```bash
lake build InfoGeometry.Canonical.All
```

## 12) Notes on Scope

- This DAG subsystem tracks declaration-level and expression-level structures.
- It does not replace theorem proving; it analyzes theory topology, dependencies, and structural shape.
- For large exports, JSON/JSONL outputs are designed to feed downstream tools (graph databases, dashboards, audits).
- LLM usage should sit on top of the purified semantic graph, not on raw repository text.
- The right output from an LLM in this pipeline is:
  candidate bridge statements, missing frontier lemmas, and critique of closure gaps.
  The Lean kernel still decides what is true.
