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

There are four different views of the theory, and they should not be mixed:

1. Declaration DAG
- Nodes are declarations.
- Edges are type/value dependencies.
- Use this for whole-library topology, dominators, SCCs, and coarse bottleneck analysis.

2. Source-sink bipartite correspondence artifact
- Nodes are typed atomic packets and hydrated readable carriers.
- Incidence edges preserve bundle ids, motif signatures, witness counts, compression scores, and canonical path examples.
- Use this for source-sink compression, path-packet transport, and projection from atomic theorem truth into readable module carriers.

3. Block export / causal provenance
- Nodes are source command blocks.
- The exporter records which declarations each block produced.
- This is the right layer for source-level attribution and semantic slicing.

4. Semantic block graph
- Built from block export, but filtered to `primaryProduces`.
- This removes generated `_proof_*`, `match_*`, and auxiliary elaborator noise from the semantic presentation layer while keeping causal provenance intact underneath.
- It now also carries `primaryDeps`, explicit semantic block edges, and enough metadata for frontier diffusion in Python.

The practical rule is:

Declaration graph for global topology and atomic truth.
Bipartite correspondence artifact for generation, compression, and bundle transport.
Semantic block graph for human-facing theory structure.

## 0.5) Hierarchy And Status

The repository currently has four graph/export lanes, and they should be kept separate:

1. Authoritative declaration-DAG lane
- [Indexer.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/Indexer.lean)
- low-level exporter behind the public `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl` lane
- [tools/infra/generate_source_sink_compression.py](/home/goutev/LEAN4/info-geometry-lean/tools/infra/generate_source_sink_compression.py) then lifts that atomic export into the public correspondence object `artifacts/dag/source-sink-bipartite.json`
- together these are the canonical source for causal order, coverage, and correspondence between atomic truth and hydrated readable carriers

2. Authoritative semantic-block lane
- [BlockExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/BlockExport.lean) for in-process block slicing
- [ServerExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ServerExport.lean) plus [semantic_block_export.py](/home/goutev/LEAN4/info-geometry-lean/tools/semantic_block_export.py) for the trusted heavy-file path
- outputs `reports/dag/*.semantic-block.stdlib.json`

3. Native auxiliary / limited lane
- [RootOrderExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/RootOrderExport.lean)
- [SkeletonExport.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/SkeletonExport.lean)
- useful for native reports, but not the default current refresh path

4. Compatibility / legacy lane
- [ExportForwardGraph.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ExportForwardGraph.lean)
- [ExportDecls.lean](/home/goutev/LEAN4/info-geometry-lean/lean/DAG/ExportDecls.lean)
- [tools/graph.py](/home/goutev/LEAN4/info-geometry-lean/tools/graph.py) and older `docs-map/graph.json` consumers
- archived module-graph compatibility tools under [archive/legacy/](/home/goutev/LEAN4/info-geometry-lean/archive/legacy/README.md)

These compatibility surfaces are archived for inspection only and are not the canonical causal-order substrate.

## 1) Current Trust Model

For public graph artifacts, the trust order is:

1. Atomic declaration DAG under `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
2. Public correspondence artifact under `artifacts/dag/source-sink-bipartite.json`
3. Readable reports and graph views under `reports/dag/`

If those layers disagree, trust the atomic DAG first, then the bipartite correspondence artifact, and regenerate the readable reports.

The repository also has two source-attribution export paths with different trust levels:

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

At the center are three graph forms:

1. `Graph alpha` in `Basic.lean`
- Nodes are declarations or synthetic entities.
- Edges are typed by `EdgeKind` (`type` or `value`).

2. `HydratedGraph alpha` in `Basic.lean` + `Hydrate.lean`
- Adds SCC decomposition, condensed DAG, predecessor map, topological order, and dominator sets.

3. Public source-sink correspondence artifact under `artifacts/dag/source-sink-bipartite.json`
- Built downstream of the exported declaration DAG.
- Connects typed atomic source bundles to hydrated readable carriers.
- Preserves bundle ids, motif signatures, witness counts, compression scores, and canonical path examples.

This gives a progression:

Environment -> Graph -> SCC DAG -> Public correspondence artifact -> Metrics/Queries/Readable projections

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

### Workflow A: Authoritative declaration topology, correspondence, and causal order

Use this when you want the current rooted partial order, coverage metrics, declaration-level causal geometry, and the maintained correspondence layer over the authoritative umbrella import root.

Step 1: export the authoritative declaration graph and declaration index

```bash
python3 tools/refresh_decl_graph.py
```

Step 2: derive the public source-sink correspondence artifact

```bash
python3 tools/infra/generate_source_sink_compression.py \
  --artifact-out artifacts/dag/source-sink-bipartite.json
```

Step 3: build the rooted causal-order report

```bash
python3 tools/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
```

Step 4: classify declaration-bearing files still outside `InfoGeometry.All`

```bash
python3 tools/classify_missing_all.py
```

Use this path for:
- root-set extraction,
- topological layers,
- declaration coverage,
- source-bundle / sink-carrier correspondence,
- `InfoGeometry.All` absorption planning,
- causal-order reports.

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
- explicit `edges`
- per-block `primaryDeps`

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

### Workflow E: Multi-module frontier discovery (`Skynet v2`)

Use this after exporting trusted semantic block JSONs for the heavy modules you
want to connect.

```bash
python3 tools/skynet_v2.py \
  --input reports/dag/KasparovCycle.semantic-block.stdlib.json \
  --input reports/dag/AnalyticalIndex.semantic-block.stdlib.json \
  --input reports/dag/OperatorAlgebraBridge.semantic-block.stdlib.json \
  --input reports/dag/GrandSynthesis.semantic-block.stdlib.json \
  --seed KasparovCycle.analyticalIndex \
  --walk reverse \
  --top 12 \
  --json-out reports/dag/skynet-v2-frontier-reverse.json \
  --md-out reports/dag/skynet-v2-frontier-reverse.md
```

Walk modes:
- `forward`
  dependency/base search
- `reverse`
  consumer/downstream search
- `both`
  local bridge kernel around the seed

To regenerate the tracked auto status page after refreshing exports/frontiers:

```bash
python3 tools/generate_auto_docs.py
```

To rerun the frontier packets and regenerate the tracked status page together:

```bash
python3 tools/update_repo_docs.py
```

### Compatibility workflow: older declaration exports

These remain useful for older consumers and one-off inspection, but they are not the authoritative current causal-order path.

```bash
lake env lean --run lean/DAG/ExportForwardGraph.lean \
  InfoGeometry.All docs-map/module_graph.json InfoGeometry

lake env lean --run lean/DAG/ExportDecls.lean \
  InfoGeometry.All InfoGeometry docs-map/declarations.json InfoGeometry
```

If these outputs disagree with `artifacts/dag/full_graph.json` or `artifacts/dag/index/decls.jsonl`, trust the `artifacts/dag/` artifacts and regenerate the derived reports. The `.build/` copies are only transient cache/fallback surfaces.

To include a full trusted export refresh for the heavy default modules:

```bash
python3 tools/update_repo_docs.py --refresh-exports
```

Current verified use case:
- `KasparovCycle.analyticalIndex` crosses into `Canonical.AnalyticalIndex`
- reverse frontier reaches `GrandSynthesis` Wheeler-DeWitt consumers

## 6) Semantic Block Export Invariants

The semantic block export now preserves a deliberate split:

- causal/dependency substrate sees `primary + aux`
- semantic presentation sees `primary` only

Concretely:
- `auxProduces` stay in `decls`, `producer`, and dependency roll-up logic
- `primaryProduces` drive semantic block nodes and semantic skeleton selection
- `primaryDeps` record hard declaration dependencies of the block's primary declarations
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
- Typed frontier extraction over semantic block graphs. Partial: done.
- Diffusion / restart-walk over purified semantic web. Partial: done via `tools/skynet_v2.py`.
- LLM-facing frontier packets for candidate bridge statements. Partial: done via skill references and report-only packets.

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
