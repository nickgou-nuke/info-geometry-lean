# InfoGeometry Lean Fusion

> Status: `reference memory`
> Last verified: 2026-06-04
> Commit: `37f7cca04` — toolchain `leanprover/lean4:v4.28.0`
> Build: **10118 jobs, passes**
> Shadows: **145** `:= by sorry` across 13 modules
> Queue: **50 tasks** in ArangoDB proof-search
> Worker: `evolution_worker.py` running (daemon)
> Working tree: **dirty**

---

**Table of Contents**

- [Repository Architecture](#repository-architecture)
- [Current Repository State (2026-06-02)](#current-repository-state-2026-06-02)
- [Constructive Closure Mandate](#constructive-closure-mandate)
- [Authority Order & Trust Rules](#authority-order--trust-rules)
- [Lean Foundation: Kernel-Checked Graph Subsystems](#lean-foundation-kernel-checked-graph-subsystems)
- [LeanTrail: Advanced Graph Analysis Pipeline](#leantrail-advanced-graph-analysis-pipeline)
- [LeanTrail Vacuum Surgery & Honest Sorry Policy (v1.3)](#leantrail-vacuum-surgery--honest-sorry-policy-v13)
- [Pipeline State: Current Snapshot Facts](#pipeline-state-current-snapshot-facts)
- [Live Repository Surface](#live-repository-surface)
- [Quick Start](#quick-start)
- [Quick Command Reference](#quick-command-reference)
- [Closure-Debt Constructive-Proof SOP](#closure-debt-constructive-proof-sop)
- [Key Results](#key-results)
- [Documentation Map](#documentation-map)
- [UTMOST MANDATE](#utmost-mandate-native-lean-proof-closure-over-witnesscertificate-scaffolding)

---

## Repository Architecture

This repository is **three coupled systems** at once:

1. **A Lean 4 theorem library** — ~2,442 `.lean` files across 84 subdirectories
   under `lean/InfoGeometry/`, formalizing information geometry, non-commutative
   Bregman divergence, thermodynamic synthesis, Virasoro/cocycle bridges,
   Clifford algebras, operator algebras, quantum dynamics, topological phases,
   optimal transport, and more.

2. **A kernel-checked graph export and meta-analysis layer** — `lean/DAG/` (60+
   files) is the Lean-side graph export system, building the declaration
   dependency graph directly from the Lean **kernel-checked environment** via
   `buildGraphFromEnv()`. This is not metadata; it is a finite explicit object
   induced by kernel-checked declarations and their dependency structure.
   `lean/InfoGeometry/Meta/` (28 files) provides the Lean-native meta-layer for
   architecture, trust, proof shape, induction, vacuity, and audits. Both are
   **compiled and verified by the Lean kernel** — they are not Python wrappers.

3. **A Python tooling and orchestration layer** — LeanTrail (17+ scripts),
   DAG refresh infrastructure, ArangoDB ingestion, graph algorithms (WL, Hodge,
   motifs), critic/surgery pipelines, and generative discovery bridges. These
   tools are **navigation and audit infrastructure**: they consume kernel-verified
   artifacts and help surface candidates, but **never decide theorem truth**.

The key distinction: **Lean-compiled code is kernel-verified truth**. Python tools
are evidence for navigation, review, and automation — the Lean kernel remains the
sole proof authority.

```
┌══════════════════════════════════════════════════════════════════════┐
║  KERNEL-CHECKED LAYER (Lean 4, lake build verified)                 ║
║                                                                      ║
║  lean/InfoGeometry/  (2,442 files — theorem library)                 ║
║  lean/InfoGeometry/Meta/  (28 files — architecture, trust, proof)    ║
║  lean/DAG/   (60+ files — graph export, Hodge, SCC, kernel equiv)   ║
║  lean/DAG/Algo/  (5 files — traversal, check, core algorithms)      ║
║  lean/scripts/DAG/Exploration/  (15 files — servers, search)        ║
║  lean/AuditNative.lean, lean/AuditStrict.lean  (native audit)       ║
║  lean/InfoGeometry/Lint/  (5 files — NonTriviality, Pauli, etc.)    ║
║                                                                      ║
║  lake build → dagIndexer (Lean exe) → artifacts/dag/index/          ║
║   93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms         ║
╚══════════════════════════════════════════════════════════════════════╝
                              │
                              ▼
┌──────────────────────────────────────────────────────────────────────┐
│  PYTHON TOOLING LAYER (navigation, audit, automation)                │
│                                                                      │
│  tools/leantrail/  (17 scripts) — LeanTrail pipeline                  │
│  tools/infra/      (~50 scripts) — DAG refresh, Arango ingest        │
│  tools/frontier/   — semantic snapshots, LLM bridges                 │
│  tools/quality/    — closure debt, placeholder audit                 │
│                                                                      │
│  Pipeline:                                                           │
│  DAG index ──► Lossless InfoTree ──► ArangoDB algorithms              │
│       │                                                              │
│       └──► LeanTrail Snapshot ──► Critic Packets ──► Surgery Plan    │
│                                   8,711 packets     ⚠ blocked         │
└──────────────────────────────────────────────────────────────────────┘
```

## Current Repository State (2026-06-02)

### Clean/Maintained

| Area | Status | Details |
|------|--------|---------|
| Lean build target | ✅ Indexed | Commit `37f7cca04`, toolchain `leanprover/lean4:v4.28.0` |
| `dagIndexer` export | ✅ Fresh Jun 2 | 93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms |
| `dagDoctor` conformance | ✅ Passes | 10/10 checks, 0% node/edge drift |
| LeanTrail snapshot | ✅ `graph_snapshot.json` | 375 MB, Jun 2 08:30 |
| Critic packets | ✅ Generated | 8,711 `obfuscation_suspicion` (high severity) |
| Critic prompts | ✅ Generated | 25 MB of LLM-ready prompts |
| Critic ingest | ✅ Merged | 8,719 nodes enriched → `graph_snapshot.critic.json` (379 MB) |
| Failed transitions | ✅ Tracked | 5,560 edges with failed proof-state transitions |

### Dirty/In-Progress

| Area | Status | Details |
|------|--------|--------|
| `vacuity_audit.py` | 🔧 Modified | 103 lines changed — under active development |
| `vacuity_ingest.py` | 🔧 Modified | 5 lines changed |
| `surgery_plan.py` | 🔧 Modified | 18 lines changed |
| `shadow_ledger.py` | 🆕 Untracked | New tool, `lake` script added but file untracked |
| Vacuity audit | ❌ Not run | No kernel biopsies on current snapshot |
| Surgery plan | ⚠ Blocked | Zero packets: `vacuity_evidence_nodes: 0` |
| New Lean modules | 🆕 Untracked (22 files) | Dynamics/ (8), Clifford/ (5 new), OperatorAlgebra/ (5), OptimalTransport/, Topological/ (3), Cantor/, Codes/ |
| `Lint/SurgeryContract.lean` | 🆕 Untracked | New lint contract module |
| `leantrail/backend/query_api.py` | 🔧 Modified | Query API changes |
| Lean source files | 🔧 Modified (11 files) | `All.lean`, `Clifford/*.lean`, `OperatorAlgebra/*.lean`, `Quantum/*.lean`, etc. |

## Constructive Closure Mandate

Replacing witness-gated and external-certificate leftovers with **native Lean 4
proofs** is the repository's highest proof-engineering priority. See
[docs/CONSTRUCTIVE_CLOSURE_MANDATE.md](docs/CONSTRUCTIVE_CLOSURE_MANDATE.md).

The formula/function rule is also current policy:
[docs/FORMULA_FUNCTION_POLICY.md](docs/FORMULA_FUNCTION_POLICY.md). Formulas are
definitions, functions are functions, and downstream code must call the function
directly rather than storing the formula as prose or a field label.

## Authority Order & Trust Rules

If documentation and code disagree, trust:

1. **`lean/` and `lakefile.lean`** — Lean source, kernel-compiled. This is proof
   authority. Everything below is navigation and audit infrastructure.
2. **`tools/`, `src/igf/`** — Python tooling. Kernel-checked artifacts are input;
   Python derives reports, visualizations, and candidate lists. Python never
   overrides Lean truth.
3. **`docs/CODEBASE_STATUS.md`** — Current verified state (stale as of 2026-05-02;
   re-audit before relying).
4. **`docs/` maintained entry docs** — Reference memory; re-audit against code.

### Core Law

```text
Graph tools identify candidate wires.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

### What This Means in Practice

- **`lean/DAG/` exports are kernel-checked** — the graph is built from the Lean
  environment, not from syntactic scraping. Tarjan SCC, dominators, Hodge
  operators, 2-complex, kernel equivalence, and triple homomorphism checkers are
  all Lean4 code that compiles.
- **Python-derived hashes, WL classes, Hodge cones, and critic packets** are
  navigation evidence, never proof authority. They may propose candidate pairs,
  but only the Lean kernel (`Lean.Meta.isDefEq`, `lake build`) may certify them.
- **LeanTrail is the most advanced pipeline** — it integrates kernel biopsies
  (`#biopsy_non_triviality`), SCC analysis, critic semantic analysis, and surgery
  planning. It is under active development (3 scripts currently dirty).

## Lean Foundation: Kernel-Checked Graph Subsystems

### `lean/DAG/` — The Lean-Side Graph Export Layer (60+ files)

The DAG subsystem is **not metadata**. It is a finite, explicit object induced by
kernel-checked declarations and their dependency structure. It compiles as part
of the Lean library and runs as Lean executables (`dagIndexer`, `infotreeExtract`,
`disconnectedAudit`, `exactProoflessnessAudit`) or interactive commands.

#### Core Graph Construction (kernel-verified types)

| File | What It Does |
|------|-------------|
| `Basic.lean` | `EdgeKind` enum, `Graph α`, `HydratedGraph α` types; `buildGraphFromEnv()` extracts declarations and edges from the Lean environment |
| `SCC.lean` | Tarjan's algorithm — strongly connected component decomposition |
| `Hydrate.lean` | Chains Tarjan → SCC-to-DAG → topological sort → dominator computation |
| `Topo.lean` | BFS in-degree topological sort on compressed SCC DAG |
| `Dominators.lean` | Bitset-based dominator computation for impact analysis |
| `Analysis.lean` | `pathCountFrom`, `distanceMap`, `influenceFrom`, `vulnerabilityOf`, `rootSet`, `capstoneSet` |

#### Higher Graph Theory (Lean-checked)

| File | What It Does |
|------|-------------|
| `GraphHodge.lean` | Finite Hodge/Laplacian/Dirac/chiral operators on the declaration 2-complex |
| `GraphHodgeBridge.lean` | Canonical finite graph-Hodge bridge packet |
| `TwoComplex.lean` | 2-complex (cell complex) structure over the declaration DAG |
| `Betti.lean` | Betti-number / homological rank computations |
| `Impact.lean` | Forward/reverse BFS reachability at SCC level → declaration level |
| `ConeCommand.lean` | Interactive `#deps_dot`, `#deps_json`, `#cone_json` for causal-diamond prompts |

#### Kernel-Certified Equivalence and Triple Checking

| File | What It Does |
|------|-------------|
| `KernelEquivalenceExport.lean` | **Native certificate checker**: imports a module and promotes candidate pairs only when `Lean.Meta.isDefEq` verifies type/value equality. **Only this Lean-native tool may set `leanVerified=true` or `safeForAutoRewrite=true`** |
| `TripleSystem.lean` | Lean-native typed subject-predicate-object incidence systems |
| `TripleHomomorphismExport.lean` | Finite preservation checker: `(s,p,o) in source ⇒ (F_Obj(s), F_Rel(p), F_Obj(o)) in target` |
| `ExactMorphism.lean` | Exact-sequence detection in morphism chains |
| `Isomorphism.lean` | Isomorphism detection and equivalence tracking |
| `LiftNaturality.lean` | Naturality verification for lifted morphisms |
| `SubgraphMatch.lean` | Subgraph pattern matching |
| `CategoryBridge.lean` | Maps declarations to `CategoryTheory.Quiver`; verifies composition in `MetaM` |

#### Export Pipelines

| File | Output | Description |
|------|--------|-------------|
| `Indexer.lean` | `full_graph.json`, `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl` | Main export: `DeclNode`, `DepEdge`, `Morphism`, `TypeNode` records |
| `StructuralExport.lean` | `structural-topology.json` | SCC-level metadata: depth, dominators, roots, layers |
| `ProcessFlowExport.lean` | `process-flow/*.jsonl` | 8 dependency roles, boundary/locality/polarity/defect |
| `ExprArangoExport.lean` | `ig_nodes.jsonl`, `ig_edges.jsonl` | Expression-level Arango export with De Bruijn `bvar` annotations |
| `RepresentationDepthExport.lean` | `representation-depth-tags.json` | Lean-enforced depth grammar tags |
| `SkeletonExport.lean` | `skeleton.json` | Vulnerability-ranked theorem skeleton |
| `BlockExport.lean` | block-level JSON | File slicing: blocks, spine tags, tactics, docstrings |
| `RawInfoTreeExport.lean` | InfoTree raw export | Tree-structured export for downstream ingestion |

#### Lean Scripts for Exploration (`lean/scripts/DAG/Exploration/` — 15 files)

| File | Purpose |
|------|---------|
| `SemanticBlockServer.lean` | Lean executable — semantic block query server |
| `SemanticSnapshotServer.lean` | Lean executable — LLM proof-snapshot server |
| `CompilerBridgeServer.lean` | Lean executable — compiler bridge server |
| `SemanticBlockExport.lean` | Lean executable — semantic block export |
| `QueryEngine.lean`, `Search.lean` | Structured query evaluation over graph metadata |
| `Disassembler.lean` | Expression-level disassembly |
| `NaturalityDiagnostics.lean`, `NaturalityPromoter.lean` | Naturality verification |
| `SquarePromoter.lean` | Square-commuting diagram promotion |
| `Betti.lean`, `Isomorphism.lean`, `FinalSearch.lean`, `SearchRank.lean` | Specialized analysis tools |

#### Kernel Equivalence Discipline

Candidate equivalence promotion must go through the Lean/kernel lane:

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

Modes:
- **`type`**: certifies definitional equality of types/statements. May set
  `leanVerified=true`. Must **not** set `safeForAutoRewrite=true`.
- **`value`**: certifies body equality only when types are also definitionally
  compatible. Can mark rewrite-safe only when both type and value pass.
- **`type-and-value`**: both lanes. One of the only modes that can set
  `safeForAutoRewrite=true`.

Python-derived hashes, role tokens, graph SCCs, and vector neighborhoods may
propose candidate pairs but are **never allowed to set `leanVerified`** — only
this Lean-native exporter or a future Lean-native checker with the same kernel
authority may do that.

For finite RDF/Arango-style triple preservation:

```bash
lake env lean --run lean/DAG/TripleHomomorphismExport.lean \
  artifacts/triples/source.jsonl \
  artifacts/triples/target.jsonl \
  artifacts/triples/maps.jsonl \
  artifacts/triples/triple-homomorphism-audit.json \
  artifacts/triples/missing-triples.jsonl
```

### `lean/InfoGeometry/Meta/` — Lean-Native Meta Layer (28 files)

This is the **Lean-compiled meta layer** — not Python, not Markdown. These
modules define the architecture, trust, proof shape, induction, and vacuity
framework that the kernel itself can reason about.

| File | Purpose |
|------|---------|
| `Architecture.lean` | Repository architecture grammar and design intent |
| `Trust.lean` | First-pass forbidden axioms beyond explicit `sorryAx` detection |
| `ProofShape.lean` | Head shape of elaborated theorem proofs and definitions |
| `Vacuity.lean` | Vacuity analysis definitions |
| `Admission.lean` | Admission/debt tracking |
| `HonestyPolicy.lean` | Honest sorry policy implementation |
| `OwnerTarget.lean` | Owner-target declaration marking |
| `SocketTarget.lean` | Socket/wire target tracking |
| `BridgeTarget.lean` | Bridge target tracking |
| `ClosureAttribute.lean` | Closure debt attributes |
| `DefectRegistry.lean` | Defect registration and query |
| `RegionPolicy.lean` | Region/policy enforcement |
| `StrictDef.lean` | Strict definition requirements |
| `StrictSurface.lean` | Strict surface area tracking |
| `CompilerTelemetry.lean` | Compiler telemetry capture |
| `CurvatureTelemetry.lean` | Curvature telemetry |
| `DrazinRefactor.lean` | Drazin refactor patterns |
| `CalibrationReexport.lean` | Calibration re-export |
| `HiveLogos.lean` | Hive/logos integration |
| `EssenceOfInductiveProof.lean` | Inductive proof essence |
| `InductionHandbook.lean` | Induction methodology handbook |
| `InductionHowTo` (separate file) | Induction implementation guide |
| `InductiveInvariantPacket.lean` | Inductive invariant packet definitions |
| `FiniteToInfiniteTransitionSOP.lean` | Finite→infinite transition SOP |
| `InductiveLimitClosureInterface.lean` | Inductive limit closure interface |
| `MarkovJonesInduction.lean` | Markov/Jones induction patterns |
| `TestTactic.lean` | Test tactics for meta layer |
| `DvorakTactics.lean` | Custom tactics |

All of these compile **as part of `lean_lib InfoGeometryMeta`** — they are
kernel-checked Lean code, not documentation.

### `lean/InfoGeometry/Lint/` — Lint and Audit Modules (5 files, kernel-checked)

| File | Purpose |
|------|---------|
| `NonTriviality.lean` | **Kernel biopsy**: provides `#biopsy_non_triviality` command used by LeanTrail vacuity audit |
| `Pauli.lean` | Pauli auditor — rejects inflated or underived closure claims |
| `Vacuity.lean` | Vacuity analysis lint |
| `WitnessLint.lean` | Witness/certificate linting |
| `SurgeryContract.lean` | 🆕 Surgery contract module (untracked, new) |

## LeanTrail: Advanced Graph Analysis Pipeline

LeanTrail is the repository's **most advanced and actively developed tool**
(3 scripts currently dirty, `shadow_ledger.py` newly added). It integrates:

- **Kernel-checked graph data** from `lean/DAG/` exports
- **Lean kernel biopsies** via `#biopsy_non_triviality` (from `lean/InfoGeometry/Lint/NonTriviality.lean`)
- **Python orchestration** for large-scale analysis (17+ scripts in `tools/leantrail/`)
- **ArangoDB** for scalable graph algorithms

The LeanTrail tooling lives in two places:

| Component | Location | Language | Role |
|-----------|----------|----------|------|
| Backend models & store | `leantrail/backend/` (7 files) | Python | `GraphSnapshot`, `NodeRecord`, `EdgeRecord`, `GraphStore` |
| Query API | `leantrail/backend/query_api.py` | Python | REST-style graph queries (🔧 modified) |
| Schemas | `leantrail/schemas/` (7 JSON schemas) | JSON Schema | Graph snapshot, bridge request, critic packet schemas |
| API server | `leantrail/api/server.py` | Python | OpenAPI server |
| UI | `leantrail/ui/index.html` | HTML | Browser-based graph explorer |
| **Tools (active)** | `tools/leantrail/` (17 scripts) | Python | Full pipeline: conformance, vacuity, surgery, critic |

### LeanTrail Scripts

| Script | Purpose | Status |
|--------|---------|--------|
| `conformance.py` | Compare snapshots (node/edge drift, SCC, path queries, hotspot Jaccard) | ✅ |
| `export.py` | Export to GraphML, Neo4j CSV, Arango JSON | ✅ |
| `vacuity_audit.py` | Spawn Lean kernel biopsies via `#biopsy_non_triviality` | 🔧 Dirty |
| `vacuity_ingest.py` | Merge biopsy data into snapshot → `graph_snapshot.vacuity.json` | 🔧 Dirty |
| `surgery_plan.py` | SCC analysis → 4 packet streams (vacuum, bridge, proof_hole, alignment) | 🔧 Dirty |
| `shadow_ledger.py` | Approve/reject vacuum packets | 🆕 Untracked |
| `surgery_apply.py` | Byte-level splice + `lake env lean` validation | ✅ |
| `critic_packets.py` | Semantic analysis (obfuscation, docstring mismatch, witness packaging) | ✅ |
| `critic_prompt_builder.py` | LLM review prompts from critic packets | ✅ |
| `critic_ingest.py` | Merge critic judgments into snapshot | ✅ |
| `hole_packets.py` | Extract proof hole packets | ✅ |
| `failure_harvester.py` | Extract failed proof-state transitions | ✅ |
| `path_lock_registry.py` | Lock/unlock paths in the snapshot | ✅ |
| `arango_ingest.py` | Ingest LeanTrail snapshot into ArangoDB | ✅ |
| `arango_physics_evaluator.py` | Physics-motivated graph evaluation | ✅ |
| `adapters.py` | Snapshot load/save, format conversion | ✅ |

### LeanTrail Data Flow

```
graph_snapshot.json                    (raw graph from dagIndexer, 375 MB)
       │
       ▼
VacuityAudit ──► vacuity_audit.jsonl  (kernel biopsy per declaration)
       │                                ⚠ NOT YET RUN on current snapshot
       ▼
VacuityIngest ──► graph_snapshot.vacuity.json  (biopsy-enriched)
       │                                ⚠ NOT YET RUN on current snapshot
       ▼
SurgeryPlan ──► 4 packet streams:
    vacuum_packets.jsonl          (contractible fake_transport/pure_conductor)
    bridge_packets.jsonl          (axiomatic/orphan bridge obligations)
    proof_hole_packets.jsonl      (honest sorry / closure debt)
    alignment_packets.jsonl       (Hodge forest overlap candidates)
       │                           ⚠ ALL EMPTY (no vacuity evidence yet)
       ▼
ShadowLedger ──► shadow_approved_packets.jsonl  (human/automated review gate)
       │                           🆕 tool exists, not yet run
       ▼
CriticPackets ──► critic_packets.jsonl  8,711 packets  ✅ DONE
       │                           (all obfuscation_suspicion / high severity)
       ▼
CriticPrompts ──► critic_prompts.jsonl  25 MB  ✅ DONE
       │
       ▼
CriticIngest ──► graph_snapshot.critic.json  379 MB  ✅ DONE (8,719 nodes)
       │
       ▼
SurgeryApply ──► byte-level splice + lake env lean validation
                ⚠ BLOCKED (no approved vacuum packets yet)
```

## LeanTrail Vacuum Surgery & Honest Sorry Policy (v1.3)

### 1. Honest Sorry Policy

Explicit `sorry` (`sorryAx`) is permitted and tracked solely as **honest, visible
closure debt**. The toolchain strictly rejects hidden/disguised substitutes
(local axioms, opaque placeholders, witness wrappers, proof sockets, renamed
`sorry` variants).

- **Explicit `sorry`**: Honest open proof obligation; indexed and quarantined
  into proof-hole packets. Not eligible for vacuum contraction.
- **Hidden wrappers**: Blocked and routed to quarantine or rejection.

The policy is implemented in `lean/InfoGeometry/Meta/HonestyPolicy.lean`
(kernel-checked) and enforced by `lean/InfoGeometry/Lint/Pauli.lean`.

### 2. Critic Packet Semantic Analysis

The critic packet pipeline has been run on the current snapshot, producing
**8,711 `obfuscation_suspicion` packets** at **high severity**. This means every
declaration currently triggers an obfuscation suspicion — expected when no kernel
biopsy data exists. A prior run on a vacuity-enriched snapshot produced 5,571
critic packets.

| Category | What It Detects |
|----------|----------------|
| **Obfuscation suspicion** | `_statement`/`_sorry` pairs, `readback` sockets, opaque boundaries, witness field packaging |
| **Docstring/statement mismatch** | Declaration name vs. docstring claims |
| **Axiomatic frontier review** | Declarations that introduce axioms instead of proving |
| **Compatibility shim detection** | Unused forwarding modules, stale dropins, namespace duplicates |

### 3. Surgery Packet Streams

When run on a vacuity-enriched snapshot, `surgery_plan.py` classifies each SCC
into a role (priority: `contaminated > protected > exported > unknown > gate >
orphan_genuine > closure_debt > translator > pure_conductor > fake_transport >
dead_socket`) and emits four streams:

| Stream | Action | Targets | Gate |
|--------|--------|---------|------|
| **vacuum** | `contract` | `fake_transport`, `pure_conductor`; `is_prop=true`; `scc_size=1` | Shadow-approved + kernel check |
| **bridge** | `bridge` | Contaminated, protected, exported, orphan_genuine | Manual review |
| **proof_hole** | `quarantine` | `closure_debt`, `honest_sorry` | Tracked explicitly |
| **alignment** | `align` | Hodge forest overlap candidates | Signature-level alignment |

### 4. Source-Edit Gate

Before any auto-contraction, **all of these** must hold:

```text
packet_stream = vacuum
action_phase = contract
state = shadow_approved (or certified for manual debug)
decl_span_kind = top_level_decl
patch_span_kind = decl_body
source_info_kind = original
scc_size = 1
contamination = clean
is_prop = true
fileHash matches
no high-severity unresolved critic packet
```

### 5. Context Graph Tools

```bash
# Search Lean source for imports/references
rg -n "<NameOrNamespace>" lean -g '*.lean'
rg -n "import <Module.Path>" lean -g '*.lean'

# Use Lean-native interactive commands in any file:
# #deps_dot Some.Theorem
# #deps_json Some.Theorem
# #cone_json Some.Theorem   (bounded causal cone)

# Interactive cone → Arango-backed prompt
python3 tools/infra/arango_causal_chiral_cone_prompt.py \
  --decl InfoGeometry.Some.Module.some_theorem \
  --json-out artifacts/cones/some_theorem.json \
  --md-out artifacts/cones/some_theorem.md

# Visualize the cone before LLM submission
python3 tools/infra/visualize_causal_chiral_cone_packet.py \
  --json-in artifacts/cones/some_theorem.json \
  --html-out artifacts/cones/some_theorem.html

# Kernel-equivalence certification (Lean-native)
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

## Pipeline State: Current Snapshot Facts

1. **The DAG is fresh** — built at commit `37f7cca04`, toolchain `v4.28.0`.
   93,554 nodes, 782,004 edges, 5,473 types, 9,929 morphisms.

2. **Conformance passes** — 10/10 checks, 0% node/edge drift, 1.0 Jaccard
   for coherence and holonomy hotspots.

3. **Critic analysis is complete** — 8,711 obfuscation-suspicion packets
   generated and ingested (8,719 nodes enriched).

4. **Vacuity audit has NOT been run** on the current snapshot. The tool is
   under active development (103 lines modified). Without kernel biopsy data,
   the surgery plan produces zero packets.

5. **Surgery plan reports `vacuity_evidence_nodes: 0`**. This is expected and
   documented: without biopsy enrichment, the planner cannot classify SCCs.

6. **22 untracked Lean files** add new modules in Dynamics, Clifford,
   OperatorAlgebra, OptimalTransport, Topological, Cantor, and Codes.

## Live Repository Surface

### Lean Libraries

| Library | `lake` name | Source | Description |
|---------|------------|--------|-------------|
| InfoGeometry | `lean_lib InfoGeometry` | `lean/InfoGeometry/` | Main theorem library (84 dirs, 2,442 files) |
| DAG | `lean_lib DAG` | `lean/DAG/` | Lean-side graph export (60+ files) |
| InfoGeometryMeta | `lean_lib InfoGeometryMeta` | `lean/InfoGeometry/Meta/` | Lean-native meta layer (28 files) |
| InfoGeometryCanonical | `lean_lib InfoGeometryCanonical` | `lean/InfoGeometry/Canonical/All.lean` | Canonical theorems root |
| InfoGeometryLLM | `lean_lib InfoGeometryLLM` | `lean/InfoGeometry/LLM/` | LLM interaction layer |
| Agent | `lean_lib Agent` | `lean/Agent/` | Agent/runtime interface |
| Docs | `lean_lib Docs` | `lean/Docs/` | Doc generation support |
| Socratic | `lean_lib Socratic` | `lean/Socratic/` | Socratic dialogue framework |
| SelfReference | `lean_lib SelfReference` | `lean/SelfReference/` | Self-referential constructions |
| Experimental | `lean_lib Experimental` | `lean/Experimental/` | Experimental / in-progress work |
| AuditNative | `lean_lib AuditNative` | `lean/AuditNative.lean` | Native audit/verification |
| AuditStrict | `lean_lib AuditStrict` | `lean/AuditStrict.lean` | Strict linting and audit |
| PrimitiveSetsAboveX | `lean_lib PrimitiveSetsAboveX` | `external/` | Pinned Erdos #1196 proof (v4.30.0-rc1) |
| scripts | `lean_lib scripts` | `lean/scripts/` | Lake script helper modules |

### Lean Executables

| Executable | Module Root | Purpose |
|------------|-------------|---------|
| `dagIndexer` | `DAG.Indexer` | Declaration graph indexer (main export pipeline) |
| `groundTruthHarvester` | `DAG.GroundTruthHarvester` | Ground truth extraction |
| `infotreeExtract` | `DAG.InfoTreeExtract` | InfoTree extraction |
| `disconnectedAudit` | `DAG.DisconnectedAudit` | Disconnected declaration audit |
| `exactProoflessnessAudit` | `DAG.ExactProoflessnessAudit` | Proof-less declaration audit |
| `semanticBlockExport` | `scripts.DAG.Exploration.SemanticBlockExport` | Semantic block export |
| `semanticBlockServer` | `scripts.DAG.Exploration.SemanticBlockServer` | Semantic block query server |
| `compilerBridgeServer` | `scripts.DAG.Exploration.CompilerBridgeServer` | Compiler bridge server |
| `semanticSnapshotServer` | `scripts.DAG.Exploration.SemanticSnapshotServer` | LLM proof-snapshot server |

### Python

| Component | Path | Role |
|-----------|------|------|
| LeanTrail tools | `tools/leantrail/` (17 scripts) | Vacuity, surgery, critic, conformance pipeline |
| DAG infrastructure | `tools/infra/` (~50 scripts) | DAG refresh, Arango ingest, algorithms |
| Frontier | `tools/frontier/` | Semantic snapshots, proof sessions |
| Quality | `tools/quality/` | Closure debt crawl, placeholder audit |
| Observability | `tools/observability/` | Graph overlay HTML reports |
| Alexandria | `tools/alexandria/` | External knowledge integration |
| CLI package | `src/igf/` | Maintained CLI (`igf` command) |
| CLI entry | `scripts/cli.py` | `infogeometry` console script |
| Total | 451 Python files | |

### Generated & Operational Artifacts

| Directory | Size | Contents |
|-----------|------|----------|
| `artifacts/dag/index/` | 3.3 GB | `decls.jsonl`, `edges.jsonl`, `morphisms.jsonl`, `types.jsonl`, topology overlays, `meta.json` |
| `artifacts/dag/process-flow/` | — | `flow-edges.jsonl`, `process-events.jsonl`, `defects.jsonl`, lawful-path candidates |
| `artifacts/leantrail/` | 1.8 GB | Snapshots, vacuity/critic data, surgery packets, conformance reports |
| `artifacts/infotree/` | — | Lossless InfoTree materializations |
| `artifacts/graph_overlay/` | — | HTML graph overlay reports |
| `reports/` | — | Generated audit and debt reports |

## Quick Start

### Python Tooling (first time)

```bash
python3 -m venv .venv
. .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e .
```

### Basic Lean + DAG Checks

```bash
lake script run changedVerify    # verify changed files build
lake script run dagStatus        # check DAG freshness
lake script run dagDoctor        # detailed DAG diagnostics
```

### Full DAG Refresh

```bash
lake script run dagAll           # full pipeline: build → index → report
```

### Run Vacuity Audit (the next step to unblock surgery)

```bash
lake script run leantrailVacuityAudit \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --out artifacts/leantrail/vacuity_audit.jsonl \
  --module-batch-size 25 --keep-going

lake script run leantrailVacuityIngest \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --audit artifacts/leantrail/vacuity_audit.jsonl

lake script run leantrailSurgeryPlan \
  --snapshot artifacts/leantrail/graph_snapshot.vacuity.json
```

### Review Critic Packets (already available)

```bash
# Generate LLM review prompts from existing critic packets
lake script run leantrailCriticPrompts \
  --packets artifacts/leantrail/critic_packets.jsonl

# View reports
cat artifacts/leantrail/critic_report.md
cat artifacts/leantrail/critic_prompts.md

# Inspect a single packet
head -1 artifacts/leantrail/critic_packets.jsonl | python3 -m json.tool | head -40
```

### Kernel Equivalence (Lean-native certification)

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean \
  InfoGeometry \
  artifacts/expr-graph/translation-candidates/pairs.jsonl \
  artifacts/expr-graph/translation-candidates/lean-kernel-equivalence.jsonl \
  --mode type
```

### IGF Pipeline CLI

```bash
igf preflight
igf build --print-json
igf run --strict --print-json
igf validate --strict --print-json
```

### GraphRAG Explorer

```bash
python3 tools/infra/ask_repo.py "Weyl character formula" --top-k 8
```

## Quick Command Reference

### Lake Scripts

| Command | Purpose | Status |
|---------|---------|--------|
| `dagStatus` | Check DAG freshness | ✅ |
| `dagDoctor` | DAG diagnostics | ✅ |
| `dagRefresh` | Full DAG re-index | ✅ |
| `dagReports` | Generate DAG reports | ✅ |
| `dagAll` | Full DAG pipeline | ✅ |
| `leanGraphSlice` | Project hydrated DAG slice to lean-graph JSON | ✅ |
| `changedVerify` | Verify changed files build | ✅ |
| `strictCheck` | Strict Lean lint driver | ✅ |
| `leantrailConformance` | Compare snapshots | ✅ |
| `leantrailExport` | Export to GraphML/Neo4j/Arango | ✅ |
| `leantrailVacuityAudit` | Kernel biopsy audit | 🔧 Modified, not yet run |
| `leantrailVacuityIngest` | Merge audit into snapshot | 🔧 Modified, not yet run |
| `leantrailSurgeryPlan` | Generate surgery packets | 🔧 Modified, blocked |
| `leantrailShadowLedger` | Approve/reject packets | 🆕 Untracked |
| `leantrailCriticPackets` | Semantic analysis | ✅ 8,711 packets |
| `leantrailCriticPrompts` | LLM review prompts | ✅ 25 MB |
| `leantrailCriticIngest` | Merge critic judgments | ✅ 8,719 nodes |
| `leantrailHolePackets` | Extract proof hole packets | ✅ |
| `leantrailArangoIngest` | Ingest into ArangoDB | ✅ |
| `leantrailArangoPhysicsEval` | Arango physics evaluation | ✅ |
| `leantrailFailureHarvest` | Harvest failure data | ✅ 5,560 failures |
| `leantrailPathLock` | Path lock registry | ✅ |
| `leantrailSurgeryApply` | Apply approved surgery | ⚠ Blocked |
| `semanticAudit` | Run semantic audit | ✅ |
| `semanticSnapshot` | Build semantic snapshot | ✅ |
| `proofSession` | Proof session handler | ✅ |
| `proofPrint` | Proof reconstruction printer | ✅ |
| `chatgptCollaborator` | ChatGPT bridge | ✅ |
| `blueprintAlexandriaBridge` | Blueprint ↔ Alexandria | ✅ |
| `blueprintArangoMatch` | Blueprint ↔ Arango | ✅ |
| `paperproofTraceBridge` | Paperproof trace | ✅ |
| `leanParanoiaAudit` | LeanParanoia audit bridge | ✅ |
| `refreshBlueprintTags` | Refresh blueprint tags | ✅ |
| `bilingualSpineReport` | Generate bilingual spine report | ✅ |
| `leanAutoTraceBridge` | Lean auto trace bridge | ✅ |

### Lean Executables (run directly)

```bash
lake env lean --run lean/DAG/KernelEquivalenceExport.lean <args>
lake env lean --run lean/DAG/TripleHomomorphismExport.lean <args>
lake env lean --run lean/DAG/ProcessFlowExport.lean <args>
lake env lean --run lean/DAG/ExprArangoExport.lean <args>
```

### Lean Interactive Commands (in any .lean file)

```lean
import DAG.ConeCommand
#deps_dot Some.Theorem
#deps_json Some.Theorem
#cone_json Some.Theorem
```

### Lean Build

```bash
lake env lean <file>.lean           # check single file
lake build <Module.Name>            # build specific module
lake build                          # full library
lake build InfoGeometry.All         # umbrella build
```

## Closure-Debt Constructive-Proof SOP

### 1. Run deterministic debt discovery first

```bash
python3 tools/quality/closure_debt_crawler.py \
  --root lean \
  --json-out reports/audit/repo-closure-debt-crawler.json \
  --md-out reports/audit/repo-closure-debt-crawler.md \
  --print-summary

python3 tools/quality/placeholder_audit.py \
  --root lean/InfoGeometry \
  --json-out reports/audit/repo-placeholder-audit.json \
  --md-out reports/audit/repo-placeholder-audit.md \
  --signals-out reports/audit/repo-placeholder-signals.json
```

Agentic file-by-file audit:

```bash
python3 tools/quality/run_agentic_closure_debt_audit.py \
  --root lean \
  --coding-agent-command 'codex exec --json' \
  --out-dir reports/audit/agentic-closure-debt \
  --limit 1 --print-progress
```

### 2. Prioritize work

- **P0**: hard findings (`sorry`, `admit`, unsafe proof holes)
- **P1**: owner-target propositions lacking theorem-backed constructive chains
- **P2**: soft/advisory debt (skeletal proofs, packaging debt)

### 3. Enforce proof authority policy

- No witness placeholders as final authority.
- Green compile is necessary but not sufficient.
- Every promoted proposition must be backed by explicit derivation notes.
- Prefer existing mathlib lemmas; add minimal intermediate lemmas as needed.
- External literature is input for theorem design only.
- Reject vacuous packaging as closure evidence.

### 4–7. Verify, re-scan, commit, deduplicate

See the full SOP in the [dag-wire-refactor skill](skills/lean-dag-wire-refactor/SKILL.md)
for the dedicated deduplication/wire-removal protocol.

## Key Results

### 1. Thermodynamic Synthesis: Non-Commutative Bregman Divergence

Formalizes `A_info = (Δ - 1) - log Δ` as operator-valued Helmholtz free energy
in the finite nilpotent sector (`CoproductToVirasoroCocycleBridge`, `N^2 = 0`).

### 2. Cantor/Fock and Dirac Sea Geometry

- `CantorFockSpace.lean` — fermionic annihilation (`a^2 = 0`), Cantor prefix readout
- `DiracSea.lean` — combinatorial `ℤ → Bool` boundary flip, nilpotent `diracSeaStep`

### 3. Ongoing Expansions (untracked, 22 new files)

| Area | Files | Topics |
|------|-------|--------|
| **Dynamics** | 8 | BisognanoWichmann, TomitaTakesaki, KMS, Rindler, Wasserstein |
| **Clifford** | 5 new | Bott, Moebius, S-matrix, Log CFT, Modular CFT |
| **OperatorAlgebra** | 5 new | Continuum limit, Erlangen-Jaynes-Gromov, Log monodromy |
| **Topological** | 3 new | Anyons, Fibonacci |
| **OptimalTransport** | New dir | OT bridge module |
| **Cantor, Codes** | New dirs | Cantor constructions, code families |

## Documentation Map

Start with these:

| Document | What It Covers |
|----------|---------------|
| [docs/README.md](docs/README.md) | Documentation routing system & philosophy |
| [docs/CODEBASE_STATUS.md](docs/CODEBASE_STATUS.md) | Previous verified state (stale: 2026-05-02) |
| [docs/RepositoryMemoryMap.md](docs/RepositoryMemoryMap.md) | High-level repo structure |
| [docs/ModuleMap.md](docs/ModuleMap.md) | Lean module dependency structure |
| [docs/LeanTrail.md](docs/LeanTrail.md) | LeanTrail blueprint and API surface |
| [docs/ARANGO_DAG_REFRESH_METHODOLOGY.md](docs/ARANGO_DAG_REFRESH_METHODOLOGY.md) | Full Arango refresh runbook |
| [lean/DAG/README.md](lean/DAG/README.md) | DAG subsystem documentation (kernel-checked graph export) |
| [leantrail/README.md](leantrail/README.md) | LeanTrail backend docs |
| [docs/CONSTRUCTIVE_CLOSURE_MANDATE.md](docs/CONSTRUCTIVE_CLOSURE_MANDATE.md) | Closure mandate policy |
| [docs/FORMULA_FUNCTION_POLICY.md](docs/FORMULA_FUNCTION_POLICY.md) | Formula/function discipline |
| [PAULI_MANDATE.md](PAULI_MANDATE.md) | Pauli auditor discipline |
| [skills/lean-dag-wire-refactor/SKILL.md](skills/lean-dag-wire-refactor/SKILL.md) | Wire removal/refactor skill |

For induction systematics:
- [docs/InductionSystematics.md](docs/InductionSystematics.md)
- [docs/InductionHowTo.md](docs/InductionHowTo.md)
- [skills/induction-systematics/SKILL.md](skills/induction-systematics/SKILL.md)

## Agentic Pipeline — Autonomous Self-Improving Proof Chain

This repository includes a fully autonomous agentic pipeline that scans, ranks,
and resolves formal proof debt. A novice agent opening this repo should follow
this guide to understand and operate the system.

### 1. Cognitive Architecture (5 Pillars)

| Pillar | Function | Formalization |
|--------|----------|---------------|
| **Logos** | Conscious theorem inventory | `lean/InfoGeometry/Meta/FormalLogos.lean` |
| **Sensing** | Self-model of proof topology | `lean/InfoGeometry/Causal/ProofDAGRepresentation.lean` |
| **Shadow** | Boundary cochain tracking | `lean/InfoGeometry/SelfReference/ShadowCone.lean` |
| **Transcendent** | Archetype detection across domains | `lean/InfoGeometry/Meta/TranscendentFunction.lean` |
| **Conscience** | Vacuity pattern detection | `tools/infra/vacuity_critic.py` (18 patterns) |

### 2. Quick Start for a Novice Agent

```bash
# 1. Build the project
lake build InfoGeometry.All

# 2. Scan for all `:= by sorry` shadows
python3 tools/infra/shadow_cone_scanner.py

# 3. Scan for all `_True` obfuscation patterns
python3 tools/leantrail/vacuity_audit.py --snapshot artifacts/leantrail/graph_snapshot.json

# 4. Detect archetypal operator patterns across domains
python3 tools/infra/detect_archetypes.py

# 5. Enqueue top shadows to the proof-search queue
python3 -c "
from tools.infra.hive_arango_queue import enqueue_goal, aql
from tools.infra.arango_env import *
from pathlib import Path
import hashlib, json

load_repo_arango_env(Path.cwd())
ep = arango_endpoint(); db = arango_database('infogeometry')
usr = arango_username(); pwd = arango_password('alexandria_root')

shadows = [json.loads(l) for l in open('artifacts/shadow_cones/shadows.jsonl') if l.strip()]
for s in shadows[:10]:
    target = f'Resolve shadow \`{s[\"apex_name\"]}\` in {s[\"file\"]}:{s[\"line\"]}'
    gh = hashlib.sha256(target.encode()).hexdigest()[:24]
    module = s['file'].replace('.lean','').replace('/','.')
    enqueue_goal(ep, db, usr, pwd, queue_name='proof-search',
        goal_hash_shape=gh, canonical_shape=gh, target_pretty=target,
        module=module, goal_index=s['line'], priority=1.0, task_kind='proof.search')
"

# 6. Start the evolution worker (processes the queue)
python3 tools/infra/evolution_worker.py
```

### 3. Understanding the Shadow Lifecycle

Shadows progress through five statuses:

```
Roaming → Incident → Paired → Integrated
                               → Rejected
```

- **Roaming**: no proof-DAG incidence detected (semantic similarity only)
- **Incident**: one-sided incidence (dependencies or dependents found)
- **Paired**: two-sided incidence (both past and future cone nodes identified)
- **Integrated**: resolved as theorem, axiom, or explicit conditional premise
- **Rejected**: proven impossible or meaningless

### 4. Key Files and What They Do

| File | Purpose |
|------|---------|
| `tools/infra/evolution_worker.py` | Main daemon — polls ArangoDB queue, runs 3-stage pipeline |
| `tools/infra/gepa_evolver.py` | Genetic Evolutionary Proof Algorithm — mutates skills |
| `tools/infra/shadow_cone_scanner.py` | Scans `:= by sorry`, computes past/future incidences |
| `tools/infra/vacuity_critic.py` | Reviews failed tasks, discovers new obfuscation patterns |
| `tools/infra/proof_seeker.py` | Searches mathlib, arXiv, web for existing proofs |
| `tools/infra/chatgpt_browser_harness_driver.py` | Browser CDP automation for ChatGPT audit |
| `tools/infra/hive_arango_queue.py` | ArangoDB-backed task queue with leasing |
| `lean/InfoGeometry/Meta/ShadowLedger.lean` | Formal shadow ledger (Lean structures) |
| `lean/InfoGeometry/Meta/TranscendentFunction.lean` | Formal archetype/synthesis structures |
| `lean/InfoGeometry/Causal/ProofDAGRepresentation.lean` | Proof DAG + Hodge operator bridge |
| `lean/InfoGeometry/SelfReference/ShadowCone.lean` | Shadow cone carrier layer |

### 5. The 3-Stage Resolution Pipeline

Each shadow task is processed through up to 3 stages:

**Stage 0 — ChatGPT Audit**: Browser CDP opens ChatGPT, sends full file context
plus 577KB Alexandria research corpus, generates proof + audit map.

**Stage 1 — Pi/DeepSeek Coding Agent**: Takes the audit map + proof sketch,
generates Lean 4 code, compiles, reads errors, fixes, repeats (max 3 iterations).

**Stage 2 — Proof Seeker**: Falls back to searching mathlib, arXiv, web, and
Alexandria corpus if stages 0-1 fail.

### 6. Authority Boundary

The pipeline can propose, reflect, and evolve, but:

- **Lean kernel** is the final authority (via `lake build`)
- **LeanTrail** is a "semantic explorer scaffold" (see `docs/LeanTrail.md`)
- **ArangoDB graph** is a "projection over compiler memory"
- **Proposals are not theorems** until the kernel says they are

### 7. Current State

```
Build:         10118 jobs, passes
Shadows:       145 `:= by sorry` across 13 modules
Queue:         50 tasks in ArangoDB proof-search, pending
Worker:        evolution_worker.py running (daemon)
_True fields:  Eliminated (~220 across ~25 files)
ClosureDebt:   2 fields in Eval/ClosureDebtTest.lean (DO NOT FIX — GEPA targets)
```

## UTMOST MANDATE: Native Lean proof closure over witness/certificate scaffolding

Replacing witness-gated and external-certificate leftovers with native Lean
proofs is the top-priority mandate.

- Witness packets, certificate fields, external certificates, and assumption
  interfaces are **temporary scaffolding only**.
- They are **not final mathematical closure** and **not promotion authority**.
- Every promoted proposition must be discharged by native Lean derivation chains.
- Open gaps must be recorded explicitly — **do not package them as complete**.
- **Real progress** = replacing certificate/witness fields with theorem-backed
  native derivations.
