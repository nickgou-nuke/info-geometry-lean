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

2. Native structural topology artifact
- Lean emits this as `artifacts/dag/structural-topology.json` from the hydrated SCC DAG.
- It preserves stable component ids, membership, condensation edges, layer summaries, strict dominators, and canonical root-witness paths.
- Use this for native condensation-level structure before hydrating into readable carriers.

3. Source-sink bipartite correspondence artifact
- Nodes are typed atomic packets and hydrated readable carriers.
- Incidence edges preserve bundle ids, motif signatures, witness counts, compression scores, and canonical path examples.
- Use this for source-sink compression, path-packet transport, and projection from atomic theorem truth into readable module carriers.

4. Block export / causal provenance
- Nodes are source command blocks.
- The exporter records which declarations each block produced.
- This is the right layer for source-level attribution and semantic slicing.

5. Semantic block graph
- Built from block export, but filtered to `primaryProduces`.
- This removes generated `_proof_*`, `match_*`, and auxiliary elaborator noise from the semantic presentation layer while keeping causal provenance intact underneath.
- It now also carries `primaryDeps`, explicit semantic block edges, and enough metadata for frontier diffusion in Python.

The practical rule is:

Declaration graph for global topology and atomic truth.
Native structural topology artifact for condensed SCC-level invariants and witness paths.
Bipartite correspondence artifact for generation, compression, and bundle transport.
Semantic block graph for human-facing theory structure.

## 0.5) Hierarchy And Status

The repository currently has four graph/export lanes, and they should be kept separate:

1. Authoritative declaration-DAG lane
- [Indexer.lean](lean/DAG/Indexer.lean)
- [StructuralExport.lean](lean/DAG/StructuralExport.lean)
- low-level exporter behind the public `artifacts/dag/full_graph.json`, `artifacts/dag/index/decls.jsonl`, and `artifacts/dag/structural-topology.json` lane
- [tools/infra/generate_source_sink_compression.py](tools/infra/generate_source_sink_compression.py) then lifts the atomic export plus native structural topology into the public correspondence object `artifacts/dag/source-sink-bipartite.json`
- together these are the canonical source for causal order, native structural invariants, and correspondence between atomic truth and hydrated readable carriers

2. Authoritative semantic-block lane
- [BlockExport.lean](lean/DAG/BlockExport.lean) for in-process block slicing
- [ServerExport.lean](lean/DAG/ServerExport.lean) plus [semantic_block_export.py](tools/semantic_block_export.py) for the trusted heavy-file path
- outputs `reports/dag/*.semantic-block.stdlib.json`

3. Native auxiliary / limited lane
- [RootOrderExport.lean](lean/DAG/RootOrderExport.lean)
- [SkeletonExport.lean](lean/DAG/SkeletonExport.lean)
- useful for native reports, but not the default current refresh path

4. Compatibility / legacy lane
- [ExportForwardGraph.lean](lean/DAG/ExportForwardGraph.lean)
- [ExportDecls.lean](lean/DAG/ExportDecls.lean)
- [tools/graph.py](tools/graph.py) and older `docs-map/graph.json` consumers
- archived module-graph compatibility tools under [archive/legacy/](archive/legacy/README.md)

These compatibility surfaces are archived for inspection only and are not the canonical causal-order substrate.

## 1) Current Trust Model

For public graph artifacts, the trust order is:

1. Atomic declaration DAG under `artifacts/dag/full_graph.json` and `artifacts/dag/index/decls.jsonl`
2. Native structural topology under `artifacts/dag/structural-topology.json`
3. Public correspondence artifact under `artifacts/dag/source-sink-bipartite.json`
4. Readable reports and graph views under `reports/dag/`

If those layers disagree, trust the atomic DAG first, then the native structural topology, then the bipartite correspondence artifact, and regenerate the readable reports.

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

At the center are four graph forms:

1. `Graph alpha` in `Basic.lean`
- Nodes are declarations or synthetic entities.
- Edges are typed by `EdgeKind` (`type` or `value`).

2. `HydratedGraph alpha` in `Basic.lean` + `Hydrate.lean`
- Adds SCC decomposition, condensed DAG, predecessor map, topological order, and dominator sets.

3. Public native structural topology artifact under `artifacts/dag/structural-topology.json`
- Emitted directly from the Lean hydrated graph.
- Preserves stable component ids, membership, condensation edges, layer summaries, strict dominators, and canonical root-witness paths.

4. Public source-sink correspondence artifact under `artifacts/dag/source-sink-bipartite.json`
- Built downstream of the exported declaration DAG plus the native structural topology.
- Connects typed atomic source bundles to hydrated readable carriers.
- Preserves bundle ids, motif signatures, witness counts, compression scores, and canonical path examples.

This gives a progression:

Environment -> Graph -> HydratedGraph -> Structural topology artifact -> Public correspondence artifact -> Metrics/Queries/Readable projections

## 3) Layered Architecture

### Layer A: Graph Kernel
- `Basic.lean`: graph structures (`Graph α`, `HydratedGraph α`, `EdgeKind`) and extraction from a Lean `Environment`. Edge collection peels both `.proj` heads and constant folds from `Expr` to capture hidden dependencies that `foldConsts` alone would miss.
- `Util.lean`: dependency walkers and generated-name filtering helpers (`arrayReplicate`, noise-label predicates).
- `SCC.lean`: Tarjan's O(V+E) SCC decomposition — iterative DFS with `lowlink` tracking and an explicit stack; `partial` annotation covers the well-foundedness gap.
- `Topo.lean`: Kahn's O(V+E) topological sort on the condensed DAG; seeded by zero-indegree nodes computed from the predecessor map.
- `Dominators.lean`: fixed-point bit-vector dominator analysis — `dom[u] = {u} ∪ ⋂_{p∈preds(u)} dom[p]` iterated in topological order using `ByteArray` bit packing (AND + single-bit SET).
- `Hydrate.lean`: composes the above into `HydratedGraph` — runs Tarjan → Kahn → bit-vector dominators in sequence; builds the condensed DAG by deduplicating cross-SCC edges with a `Std.HashSet (Nat × Nat)`.

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
- `JsonInstances.lean`: JSON codecs for all core types (`Graph`, `HydratedGraph`, `Block`, `Export`).
- `Indexer.lean`: authoritative entry point — runs as `lake env lean --run`; drives `IndexerM` over the elaborated environment to emit `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl`, `types.jsonl`, `full_graph.json`.
- `StructuralExport.lean`: emits `structural-topology.json` from the hydrated SCC graph; preserves stable component ids, layer BFS, deepest chains, dominator chains, and canonical root-witness paths.
- `BlockExport.lean`: command-block slicing, tactic morphisms, block DAG, quiver emitters.
- `ServerExport.lean`: RPC methods over editor snapshots, including semantic block export.
- `SemanticServerRpc.lean`: explicit builtin RPC registration shim for server integration.
- `SkeletonExport.lean`: "true skeleton" export via vulnerability ranking.
- `RootOrderExport.lean`: root → capstone traversal order export.

### Auxiliary
- `Functor.lean`: categorical morphism recognition and commutative-square search.
- `Indexer.lean`: patched indexing pipeline with morphism extraction and graph JSON.
- `LiftNaturality.lean`: shared lift-pattern recognizer for naturality diagnostics/promoters.
- `FindFinrank.lean`, `KernelExtract.lean`: utility and support modules.

## 3.5) End-to-End Data Flow

```
Lean environment (InfoGeometry.All)
        │
        ▼  lake env lean --run lean/DAG/Indexer.lean
  ┌─────────────────────────────────────┐
  │  IndexerM (StateRefT MetaM)         │
  │  ├─ buildGraphFromEnv()  → Basic    │
  │  ├─ hydrate()                       │
  │  │    ├─ tarjan()        → SCC      │
  │  │    ├─ topo()          → Topo     │
  │  │    └─ dominators()    → Doms     │
  │  ├─ emitStructuralTopology() → StructuralExport │
  │  └─ processConstant() per decl      │
  │       ├─ recognizeMorphism()        │
  │       └─ addEdge() (deduped)        │
  └─────────────────────────────────────┘
        │
        ▼  artifacts/dag/
  ┌──────────────────────────────────────────────────┐
  │  full_graph.json          (flat forward adjacency)│
  │  structural-topology.json (SCC/dominator/layers)  │
  │  index/decls.jsonl        (per-decl metadata)     │
  │  index/edges.jsonl        (typed dep edges)       │
  │  index/morphisms.jsonl    (Hom/Equiv/Iso/Map)     │
  │  index/types.jsonl        (unique type strings)   │
  └──────────────────────────────────────────────────┘
        │
        ▼  tools/infra/ (Python + NetworkX)
  ┌──────────────────────────────────────────────────────────────┐
  │  refresh_decl_graph.py          ← shells to Indexer.lean     │
  │  plot_decl_graph.py             ← shared NetworkX loader     │
  │  generate_causal_report.py      ← root/capstone/layer ranks  │
  │  generate_source_sink_compression.py ← bipartite layer       │
  │  generate_structural_dedup.py   ← WL-hash quotient candidates│
  │  generate_structural_fibers.py  ← packet-conditioned fibers  │
  │  generate_theorem_surface_index.py ← surface classification  │
  │  classify_missing_all.py        ← coverage gap detection     │
  │  check_bipartite_bleed.py       ← anti-bleed validation      │
  │  select_openclaw_target.py      ← hotspot prioritisation     │
  │  refresh_blueprint_tags.py      ← blueprint annotation sync  │
  └──────────────────────────────────────────────────────────────┘
        │
        ▼  reports/dag/  (human-readable outputs)
  true-root-order.{md,json}   source-sink-compression.{md,json}
  frontier-burndown.{md,json} module-networkx.{graphml,svg}  …
```

All Python scripts resolve paths exclusively through `tools/pathing.py`. No tool
hardcodes artifact locations.

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

## 4.5) `tools/infra/` Script Reference

All scripts in `tools/infra/` consume DAG artifacts produced by `Indexer.lean` and
route paths through `tools/pathing.py`.

| Script | Inputs | Outputs | Purpose |
|---|---|---|---|
| `refresh_decl_graph.py` | Lean env via `Indexer.lean` | `full_graph.json`, `structural-topology.json`, `index/*.jsonl` | **Canonical tick** — shells to `lake env lean --run lean/DAG/Indexer.lean`; everything downstream depends on this |
| `plot_decl_graph.py` | `full_graph.json`, `decls.jsonl`, optional surface index | `declaration-networkx.graphml`, `module-networkx.{graphml,svg}`, frontier variants, `networkx-graph-summary.json` | Shared NetworkX loader used as a library by other scripts; also a standalone graph renderer |
| `generate_causal_report.py` | `full_graph.json`, `decls.jsonl`, debt indices | `reports/dag/true-root-order.{md,json}` | Root/capstone extraction, topological layers, debt-weighted ranking; coverage gap detection |
| `generate_source_sink_compression.py` | `full_graph.json`, `decls.jsonl`, `structural-topology.json`, surface index | `source-sink-bipartite.json`, `source-sink-compression.{md,json}`, `source-sink-incidence.{graphml,svg}` | Bipartite bundle/carrier incidence layer; motif matching; compression scoring |
| `generate_structural_dedup.py` | `full_graph.json`, `decls.jsonl`, `structural-topology.json` | `reports/dag/structural-dedup-candidates.{md,json}` | WL-hash-driven quotient candidates for declaration deduplication |
| `generate_structural_fibers.py` | `source-sink-bipartite.json` | `reports/dag/structural-fibers.{md,json}` | Packet-conditioned fiber decomposition of the bipartite layer |
| `generate_theorem_surface_index.py` | `decls.jsonl` | `reports/dag/theorem-surface-index.json` | Classifies theorems by surface category (constructive / bridge / surrogate / neutral) |
| `classify_missing_all.py` | `decls.jsonl`, `lean/InfoGeometry/` file tree | `reports/dag/missing-all-classification.md` | Finds declaration-bearing `.lean` files absent from `InfoGeometry.All` |
| `check_bipartite_bleed.py` | `source-sink-bipartite.json` | console / exit code | Validates that no source bundle bleeds into the wrong sink partition |
| `select_openclaw_target.py` | causal report JSON, surface index | console / `reports/dag/openclaw-target.json` | Picks the highest-priority structural hotspot for the OpenClaw driver |
| `refresh_blueprint_tags.py` | `decls.jsonl`, `BlueprintTags.lean` | updated `BlueprintTags.lean` | Synchronises blueprint annotation sites with the current declaration metadata |
| `run_locked_lake_build.py` | — | — | Thin locked-build wrapper around `lake build` |

## 5) Primary Workflows

### Workflow A: Authoritative declaration topology, correspondence, and causal order

Use this when you want the current rooted partial order, coverage metrics, declaration-level causal geometry, and the maintained correspondence layer over the authoritative umbrella import root.

Step 1: export the authoritative declaration graph, declaration index, and native structural topology

```bash
python3 tools/infra/refresh_decl_graph.py
```

Step 2: derive the public source-sink correspondence artifact from the atomic DAG plus the native structural topology

```bash
python3 tools/infra/generate_source_sink_compression.py   --structure artifacts/dag/structural-topology.json   --artifact-out artifacts/dag/source-sink-bipartite.json
```

Step 3: build the rooted causal-order report

```bash
python3 tools/infra/generate_causal_report.py \
  --out reports/dag/true-root-order.md \
  --json-out reports/dag/true-root-order.json
```

Step 4: classify declaration-bearing files still outside `InfoGeometry.All`

```bash
python3 tools/infra/classify_missing_all.py
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
- Shared search core extraction (`SearchCore.lean`).
- Search module deduplication — `Search.lean`, `SearchRank.lean`, `FinalSearch.lean` consume shared helpers.
- `SearchCoreTests.lean` for deterministic behaviour checks.

### Phase 2 (open)
- Canonical expression dependency fold extraction. Three independent implementations currently exist:
  - `Util.collectDeps` — walks `ConstantInfo` recursively via environment lookups.
  - `Basic.collectExprConsts` — `foldConsts` + explicit `.proj` head peeling.
  - `Indexer.collectConsts` — direct `foldConsts` without proj head coverage.
  - Target: single shared primitive covering all three call sites.

### Phase 3 (open)
- Unify local/global expression disassembly logic (`Disassembler` and `GlobalDisassembler`).

### Phase 4 (open)
- Consolidate context-block heuristics shared by `BlockExport` and `ServerExport`.

### Phase 5 (open)
- Optional umbrella/API normalization in `DAG.lean` (currently `import`-only, no re-export shims).

### Phase 6 (partial)
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
