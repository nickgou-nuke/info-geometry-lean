# Toolchain Architecture — Complete Reference

> Generated: 2026-06-15 from direct code audit of all scripts, DAG tools, and Lean extraction infra.

This document explains every tool, script, and data pipeline in the repository's
audit/inspection/quality chain. It is organized by **data flow**: Lean kernel →
artifacts → Python consumers.

---

## Table of Contents

1. [Architecture Overview](#architecture-overview)
2. [Layer 0: Lean Kernel Extraction](#layer-0-lean-kernel-extraction)
3. [Layer 1: Python Orchestration](#layer-1-python-orchestration)
4. [Layer 2: LeanTrail Normalization](#layer-2-leantrail-normalization)
5. [Layer 3: Audit & Inspection Tools](#layer-3-audit--inspection-tools)
6. [Layer 4: API & Server](#layer-4-api--server)
7. [The NonTriviality Biopsy System](#the-nontriviality-biopsy-system)
8. [The `_True`/`_sorryProof` Pattern](#the-_true_sorryproof-pattern)
9. [The Rep-Depth Architecture Grammar](#the-rep-depth-architecture-grammar)
10. [File Index](#file-index)

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────┐
│                    LEAN KERNEL (ground truth)            │
│  env.constants → ci.type → ci.value? → collectExprConsts│
│  findDeclarationRanges? → findDocString?                │
│  @[rep_depth] @[capstone] @[infrastructure]             │
└──────────────────────┬──────────────────────────────────┘
                       │ lake env lean --run
                       ▼
┌─────────────────────────────────────────────────────────┐
│  DAG/Indexer.lean          DAG/Hydrate.lean             │
│  DAG/Basic.lean            DAG/StructuralExport.lean    │
│  DAG/ProcessFlowExport.lean  DAG/ExprFingerprint.lean   │
│  InfoGeometry/Meta/Architecture.lean                    │
│  InfoGeometry/Meta/Vacuity.lean                         │
│  InfoGeometry/Lint/NonTriviality.lean                   │
└──────────────────────┬──────────────────────────────────┘
                       │ produces
                       ▼
┌─────────────────────────────────────────────────────────┐
│  artifacts/dag/index/                                   │
│    meta.json      decls.jsonl    edges.jsonl            │
│    full_graph.json  types.jsonl  morphisms.jsonl        │
│  artifacts/dag/representation-depth-tags.json           │
│  artifacts/dag/process-flow/process-events.jsonl        │
│  artifacts/dag/process-flow/holonomy-events.jsonl       │
└──────────────────────┬──────────────────────────────────┘
                       │ consumed by
                       ▼
┌─────────────────────────────────────────────────────────┐
│  PYTHON ORCHESTRATION LAYER                             │
│  tools/infra/refresh_decl_graph.py                      │
│  tools/infra/refresh_blueprint_tags.py                  │
│  tools/infra/run_locked_lake_build.py                   │
└──────────────────────┬──────────────────────────────────┘
                       │ normalizes into
                       ▼
┌─────────────────────────────────────────────────────────┐
│  LEANTRAIL NORMALIZATION                                │
│  leantrail/backend/normalizer.py → GraphSnapshot        │
│  leantrail/backend/store.py      → GraphStore           │
│  leantrail/backend/models.py     → NodeRecord/EdgeRecord│
│  leantrail/backend/query_api.py  → QueryAPI             │
└──────────────────────┬──────────────────────────────────┘
                       │ queried by
                       ▼
┌─────────────────────────────────────────────────────────┐
│  AUDIT & INSPECTION TOOLS                               │
│  tools/leantrail/vacuity_audit.py     (biopsy gate)     │
│  tools/leantrail/hole_packets.py      (failure→hole)    │
│  tools/leantrail/shadow_index.py      (text grep)       │
│  tools/leantrail/surgery_plan.py      (nx graph ops)    │
│  tools/leantrail/conformance.py       (parity check)    │
│  tools/leantrail/critic_packets.py    (LLM prompts)     │
│  tools/leantrail/export.py            (GraphML/Neo4j)   │
│  tools/leantrail/path_lock_registry.py                  │
│  tools/leantrail/failure_harvester.py                   │
│  tools/leantrail/arango_*.py         (ArangoDB)         │
└─────────────────────────────────────────────────────────┘
```

**Key architectural principle**: The Lean kernel is the sole authority for truth.
The Python tools are diagnostic consumers — they annotate, query, and visualize,
but never determine theorem validity. Graph shape is evidence, not proof.

---

## Layer 0: Lean Kernel Extraction

All Python tools depend on artifacts produced by Lean code running inside the
Lean environment. These are the **foundational producers**.

### `lean/DAG/Basic.lean`

Core graph types and extraction primitives.

| Declaration | Purpose |
|-------------|---------|
| `EdgeKind` | `type \| value` (type-level vs value-level dependency) |
| `Graph α` | `nodes : Array α`, `nodeToIdx`, `forward : Array (Array (Nat × EdgeKind))` |
| `HydratedGraph α` | Extends `Graph` with `sccs`, `sccOf`, `dag`, `preds`, `topo`, `doms` |
| `collectExprConsts(e)` | Walks expression tree collecting all `const` names + projection heads |
| `edgesFromConstantInfo(ci)` | Returns `Array (Name × EdgeKind)` — immediate deps of a constant |

**How `edgesFromConstantInfo` works:**
1. Walk `ci.type` → collect all constant names → tag as `EdgeKind.type`
2. If `ci.value?` exists (the proof/body), walk it → tag as `EdgeKind.value`
3. Concatenate both arrays

### `lean/DAG/Hydrate.lean`

Takes a raw `Graph α` and computes the full SCC/DAG structure:

```
Tarjan SCC → sccOf mapping → DAG condensation → topological order → dominator tree
```

Uses three companion modules:
- `DAG/SCC.lean` — Tarjan's strongly connected components
- `DAG/Topo.lean` — topological sort on DAG
- `DAG/Dominators.lean` — dominator tree computation

### `lean/DAG/Indexer.lean`

**The main extraction engine.** Run via:
```bash
lake env lean --run lean/DAG/Indexer.lean <import-module> <namespace> <output-dir> <graph-out> <structure-out>
```

**What it does per constant** (`processConstant`):

| Step | Data extracted | Source API |
|------|---------------|------------|
| Module name | `InfoGeometry.Arithmetic.RiemannHypothesis` | `env.getModuleIdxFor?` |
| Source file | `/path/to/file.lean` | `Lean.findLean` |
| Line/column | `(42, 5)` | `findDeclarationRanges?` |
| Docstring | `"/-- ... -/"` | `findDocString?` |
| Kind | `theorem\|def\|axiom\|opaque\|inductive` | `ConstantInfo` match |
| Vacuity tags | `@[infrastructure]` etc. | `InfoGeometry.Meta.vacuityRoleTagStringsOf` |
| Rep-depth tags | `rep_depth:krein` etc. | `InfoGeometry.Meta.repDepthTagStringsOf` |
| Capstone flag | `@[capstone]` | `InfoGeometry.Meta.capstoneAttr.hasTag` |
| Type fingerprint | SHA256 of normalized type | `ExprFingerprint.computeFingerprint` |
| Value fingerprint | SHA256 of normalized body | `ExprFingerprint.computeFingerprint` |
| Type deps | `["riemannZeta", "Complex.abs", ...]` | `collectConsts(ci.type)` |
| Value deps | `["Real.log", "dikinOmega", ...]` | `collectConsts(ci.value?)` |
| Morphism recognition | `Func\|Hom\|Equiv\|Iso\|Map` | Syntactic Π-type + head-symbol inspection |

**Output files produced:**

| File | Content |
|------|---------|
| `decls.jsonl` | One JSON object per declaration |
| `edges.jsonl` | `{src, dst, kind: "type"\|"value"}` |
| `full_graph.json` | `{nodes: [String], forward: [[(Nat, String)]]}` — adjacency list |
| `meta.json` | `{schemaVersion, timestamp, nodeCount, edgeCount, morphismCount, nsFilter, importRoot}` |
| `morphisms.jsonl` | `{declName, category, domainKey, codomainKey, typeStr, doc}` |
| `types.jsonl` | Deduplicated type keys from morphism recognition |
| `edge-leakage.json` | Leakage report: edges crossing namespace boundaries |

**Edge deduplication**: Before writing, the indexer maintains an `edgeSet : Std.HashSet EdgeKey`
to ensure each `(src, dst, kind)` triple appears at most once.

### `lean/DAG/ProcessFlowExport.lean`

Classifies every dependency edge with semantic roles:

| Enum | Values |
|------|--------|
| `DependencyRole` | `head \| requiredArg \| transportArg \| witness \| closureSupport \| ornament \| remoteSupport \| unknown` |
| `BoundaryClass` | `internal \| localInterface \| bridge \| capstone \| mixed \| unclear` |
| `LocalityClass` | `local \| adjacent \| remote \| mixed` |
| `PolarityClass` | `neutral \| sameLayer \| descending \| remote \| mixed \| regressive` |
| `DerivationalRole` | `vertical \| primitiveTranslator \| capstoneCoherence \| violation` |
| `DefectKind` | `remoteAttachment \| failedLocalFactorization \| unresolvedComparison \| illicitBoundaryCrossing \| mixedPolarity \| regressiveFlow \| typeOnlySupport \| boundaryBypass \| unclearPolarity` |

Output: `artifacts/dag/process-flow/process-events.jsonl`

### `lean/InfoGeometry/Meta/Architecture.lean`

**The representation-depth grammar.** Defines a 6-layer architecture:

| Depth | Slug | Layer Label | Description |
|-------|------|-------------|-------------|
| 0 | `count` | L0_Count | counting/combinatorial substrate |
| 1 | `projective` | L1_Projective | projection/support/compression substrate |
| 2 | `operator` | L2_Operator | operator-algebraic bridge substrate |
| 3 | `krein` | L3_Krein | Krein/doubled-geometry substrate |
| 4 | `transport` | L4_ModularTransport | modular/transport/flow substrate |
| 5 | `thermo` | L5_ThermodynamicClosure | thermodynamic/free-energy/closure substrate |

**Attributes:**
- `@[rep_depth count|projective|operator|krein|transport|thermo]` — assigns a declaration to a layer
- `@[capstone]` — marks a theorem as a composite capstone (exempt from strict adjacency)

**Architecture audit** (`#audit_architecture`):
- Enforces that canonical spine declarations obey depth adjacency
- Detects REGRESSION (depending on deeper layer) and WORMHOLE (skipping layers)
- `#audit_rep_depth_coverage` checks that all canonical def/theorem declarations are tagged

**Key functions:**
- `nearestTaggedDescendants(env, root)` — BFS through untagged nodes to find nearest tagged deps
- `taggedDependencyViolations(env, declName, depth, allowComposite)` — produces violation messages
- `transitivelyUsedConstants(env, root)` — full transitive closure

### `lean/InfoGeometry/Meta/Vacuity.lean`

Lightweight semantic role tags:

| Attribute | Meaning |
|-----------|---------|
| `@[infrastructure]` | Support lemma, not theorem-level mathematical content |
| `@[terminal]` | Public terminal declaration with no expected downstream reuse |
| `@[expository]` | Public wrapper/restatement kept for readability |

### `lean/DAG/ExprFingerprint.lean`

Computes content-addressable hashes of Lean expressions. Used to detect:
- Duplicate theorems under different names
- Unchanged proof bodies across refactors
- Structural dedup candidates

---

## Layer 1: Python Orchestration

These Python scripts drive the Lean extraction tools. They are **orchestrators**,
not producers.

### `tools/infra/refresh_decl_graph.py`

**Purpose**: Run the full DAG refresh cycle.

**Algorithm:**
```
1. Compute olean content hash (SHA256 of all .olean files)
2. Compute lean source hash (SHA256 of all .lean files)
3. Check if should_skip_decl_refresh:
   - meta.json exists with matching olean/source hash AND matching import_root/namespace
   - AND no stale source file references in existing decls
4. If skipping: return 0 (incremental)
5. If refreshing:
   a. run_locked_prebuild(target, run_mode="exe")
   b. build_indexer_command() → spawn lake env lean --run DAG/Indexer.lean ...
   c. stamp_decl_index_meta() — backfill timestamp + olean hash
   d. write_indexer_timing_sidecar()
```

**Key design decision**: Uses content-hash incremental skip to avoid rebuilding
the entire index when nothing changed.

### `tools/infra/refresh_blueprint_tags.py`

Extracts `@[rep_depth ...]` and `@[capstone]` attribute data into
`artifacts/dag/representation-depth-tags.json`. This is consumed by the
LeanTrail normalizer to annotate nodes with `rep_depth`, `depth_nat`, and
`capstone` flag.

### `tools/infra/run_locked_lake_build.py`

Prebuilds a Lake target under a file lock to prevent concurrent build corruption.
Supports both `exe` (compiled executable) and `run` (interpreted) modes.

---

## Layer 2: LeanTrail Normalization

### `leantrail/backend/models.py`

The three core dataclasses:

```python
@dataclass
class NodeRecord:
    id: str                    # fully qualified declaration name
    name: str                  # same as id
    kind: str                  # "Declaration" | "Module"
    module: str                # source module
    file: str | None           # .lean file path
    line: int | None           # line number
    rep_depth: str | None      # e.g. "count", "krein"
    role: str | None           # "owner" | "translator" | "coherence" | "capstone"
    module_family: str | None  # first 3 segments of module name
    commit_sha: str
    toolchain: str             # leanprover/lean4:v4.28.0
    artifact_version: int
    attrs: dict                # arbitrary metadata

@dataclass
class EdgeRecord:
    src: str
    dst: str
    kind: str                  # depends_type|depends_value|contains|obstructs|violates_depth|translator_of|coheres_with
    weight: float
    evidence_ref: str          # provenance of this edge
    attrs: dict                # includes path_state, failure_count, failure_kinds

@dataclass
class GraphSnapshot:
    metadata: dict
    nodes: list[NodeRecord]
    edges: list[EdgeRecord]
```

### `leantrail/backend/normalizer.py`

**The normalization engine.** Produces `GraphSnapshot` from raw DAG artifacts.

**Edge kind mapping:**
| DAG kind | Snapshot kind |
|----------|--------------|
| `"type"` | `depends_type` (weight 1.0) |
| `"value"` | `depends_value` (weight 1.1) |
| `supportCandidates` | `translator_of` (weight 0.6) |
| `comparisonCandidates` | `coheres_with` (weight 0.6) |
| `closureDeps` | `obstructs` (weight 0.6) |
| module→decl | `contains` (weight 1.0) |
| depth violation | `violates_depth` (weight 3.0) |

**Depth violation detection:**
```python
def _is_lawful_depth(src_depth, dst_depth, src_capstone):
    if src_capstone: return True          # capstones can reach anywhere
    if src_depth is None or dst_depth is None: return True
    return dst_depth == src_depth or dst_depth == src_depth - 1
```
A `violates_depth` edge (weight 3.0) is created when a declaration depends on
something that is neither same-layer nor one layer down, unless it's a capstone.

**Role inference** (when process-flow role is absent):
```python
if capstone → "capstone"
elif "translator" or "bridge" in name+module → "translator"
elif "cohere" or "compatibility" or "equiv" in name+module → "coherence"
else → "owner"
```

**Path state annotation** (per edge):
```python
if key in locked_index → "locked"
elif key in failed_index → "failed"
else → default_path_state(kind)
```
Where default is: `"meta"` for contains edges, `"failed"` for obstructs/violates_depth, `"bound"` otherwise.

**Endpoint annotation** (per node, counting only non-meta edges with bound/locked state):
```
indeg=0, outdeg=0 → "isolated"
indeg=0 → "source"
outdeg=0 → "sink"
else → "internal"
```

**Edge deduplication**: Merges edges with same `(src, dst, kind)` by collecting
`evidence_refs` and taking the max weight.

### `leantrail/backend/store.py`

**In-memory graph database.** Built from a `GraphSnapshot`.

| Method | Algorithm | Complexity |
|--------|-----------|------------|
| `search(q)` | Linear scan of `name+module+kind+module_family` for substring | O(n) |
| `get_decl(name)` | Hash lookup + outgoing/incoming edge collection | O(1 + deg) |
| `neighborhood(center, radius)` | BFS visiting both out-edges and in-edges | O(V+E) in subgraph |
| `shortest_path_with_state_policy` | BFS with edge filtering (block `violates_depth`/`obstructs` when lawful, filter by state policy) | O(V+E) |
| `coherence_hotspots(limit)` | Score = `2·translator_edges + 5·violation_edges + 0.05·dep_edges` | O(V) |
| `holonomy_hotspots(limit, α, β, γ)` | Score = `α·tactic_steps + β·context_expansion + γ·metavariable_flux` | O(V) |
| `dedup_candidates(status)` | Reads `attrs.structural_dedup` from nodes | O(V) |

**Path state policies for shortest path:**
- `"any"` — all non-meta, non-blocked edges
- `"exclude-failed"` — skip `path_state == "failed"`
- `"locked-only"` — only use `path_state == "locked"`

**Holonomy scoring**: Prefers explicit telemetry from `attrs.holonomy.{tactic_steps, context_expansion, metavariable_flux}`.
Falls back to structural proxies: out-degree for tactic_steps, in-degree for context_expansion,
violation-edge count for metavariable_flux.

### `leantrail/backend/query_api.py`

Wraps `GraphStore` with:

- **Snapshot staleness detection**: Compares `commit_sha` and dag_meta fields
  (`timestamp`, `sourceHash`, `oleanHash`, `nodeCount`, `edgeCount`, `morphismCount`).
  Auto-rebuilds if stale.
- **Proof-state RPC**: Delegates to `LeanRPCAdapter` for live `lake env lean` proof state queries
- **Bridge candidate creation**: Validates against JSON schema, writes to
  `artifacts/dag/process-flow/bridge-candidates/`

---

## Layer 3: Audit & Inspection Tools

### `tools/leantrail/vacuity_audit.py` — The Biopsy Gate

**The most powerful audit tool.** Does NOT do text grep — it runs actual Lean
compilation.

**Algorithm:**
```
1. Load GraphSnapshot
2. Filter declarations by --module-prefix / --decl-prefix / --decl
3. Group by module, batch into groups of --module-batch-size (default 25)
4. For each batch:
   a. Generate temp .lean file:
      import InfoGeometry.Lint.NonTriviality
      import <module>
      set_option autoImplicit false
      #biopsy_non_triviality <decl1>
      #biopsy_non_triviality <decl2>
      ...
   b. Run: lake env lean <temp_file> --timeout <N>
   c. Parse JSON output from logInfo lines
5. Write vacuity_audit.jsonl
```

**The `#biopsy_non_triviality` command** (see [NonTriviality Biopsy](#the-nontriviality-biopsy-system))
classifies each declaration into a `vacuity_role`:

| Role | Meaning |
|------|---------|
| `gate` | Genuine theorem with mathlib dependency and non-trivial proof body |
| `fake_transport` | Vacuous socket — wraps unproven fields as theorems |
| `pure_conductor` | Trivial projection/accessor — just passes through a field |
| `contaminated` | References forbidden axioms or has dependency violations |
| `closure_debt` | Contains `sorry` but configured as honest debt |
| `type_boundary` | Non-Prop declaration at the type/value boundary |

### `tools/leantrail/hole_packets.py` — Failure→Hole Pipeline

Takes `failed_transitions.jsonl` and produces ranked "hole packets."

**Algorithm:**
```
1. Load failed transitions JSONL
2. Group by (src, dst) → HoleAccumulator
   - Sum failure_count
   - Collect error_kinds, dep_kinds, transition_ids, witnesses
3. Score each hole:
   priority = total_cost + 2·failure_count + 3·diversity(error_kinds)
4. Z2 surrogate: failure_count mod 2 (odd = "open", even = "pairable")
5. Annotate path states:
   - shortest_path(src, dst, state_policy="any")
   - shortest_path(src, dst, state_policy="exclude-failed")
   - shortest_path(src, dst, state_policy="locked-only")
6. Annotate required lock status from conformance report
7. Attach socratic packet template (missing_assumptions, bridge_obligations,
   minimal_lemma_chain, expected_first_error_signature)
8. Output hole_packets.jsonl + hole_packets.md
```

### `tools/leantrail/shadow_index.py` — Text-Level Debt Scanner

Pure text grep — no compilation. Scans `.lean` files for:

| Detection | Pattern |
|-----------|---------|
| `sorryDebt` | `\bsorry\b` outside strings/comments |
| `vacuityDebt` | Field names ending in `_True`, `_sorryProof`, `_certificate`, `_witness`, `_bridge`, etc. with `Prop` on the same line |
| `wrapperDebt` | `structure` declaration with certificate fields in next 10 lines |
| `failedCompilation` | `lake env lean <file>` returns non-zero (optional, slow) |

**Vacuity suffixes detected** (from `VACUITY_SUFFIXES`):
`_True`, `_sorryProof`, `_certificate`, `_valid`, `_witness`, `_bridge`,
`_surety`, `_indemnity`, `_attestation`, `_covenant`, `_verity`, `_testimony`,
`_accreditation`, `_bond`, `_seal`, `_voucher`, `_nexus`, `_guaranty`

**Domain detection**: Maps files to keyword domains (Berezinian, Pfaffian,
BottPeriodicity, CliffordAlgebra, HodgeKrein, etc.) based on file path and
parent directory.

### `tools/leantrail/surgery_plan.py` — Dependency Graph Surgery

Uses `networkx` for graph-based refactoring planning:

- Builds a `nx.DiGraph` from snapshot edges
- Identifies "vacuum roles" (`fake_transport`, `pure_conductor`) for contraction
- Computes SCC decomposition, identifies removable subgraphs
- Produces a `surgery_manifest.json` with planned operations

### `tools/leantrail/conformance.py` — Cross-Format Parity Check

Compares two graph representations:

**Input formats**: `snapshot`, `graphml`, `neo4j-csv`, `arango-json`

**Checks performed:**
- Node and edge count drift percentages
- Node/edge kind distribution comparison
- Overlap on node ids and edge keys
- Dependency SCC signature parity
- Shortest-path query parity (canonical seeds or custom `--path-queries`)
- Hotspot overlap (coherence, holonomy) via Jaccard index
- Required-path-lock gate (fails if locked paths missing from candidate)

### `tools/leantrail/export.py`

Exports canonical snapshot to external formats:
- GraphML (`graph_snapshot.graphml`)
- Neo4j CSV (`neo4j/nodes.csv`, `neo4j/edges.csv`)
- Arango JSON (`arango/ig_nodes.jsonl`, `arango/ig_edges.jsonl`)

### `tools/leantrail/decl_lookup.py`

CLI wrapper for `GraphStore.get_decl(name)`. Query:
```bash
python3 -m tools.leantrail.decl_lookup --snapshot <path> --name <fully.qualified.name>
```

### `tools/leantrail/snapshot_summary.py`

Prints a summary of a LeanTrail snapshot:
```
commit_sha=...
toolchain=leanprover/lean4:v4.28.0
artifact_version=3
nodes=101000 edges=825015
node_kinds: Declaration=98741, Module=2259
edge_kinds: coheres_with=57276, contains=98741, depends_type=308123, ...
top_modules: [1] InfoGeometry.Probability.HomologicalProbability count=703 ...
```

### `tools/leantrail/path_lock_registry.py`

Registers `bound` or `locked` path records into `path_locks.jsonl`.
Locked paths survive conformance gates — they represent known-correct
dependency chains that must not be broken.

### `tools/leantrail/failure_harvester.py`

Harvests process-flow defects into `failed_transitions.jsonl`. Consumes
`artifacts/dag/process-flow/defects.jsonl` and optional build logs.

### `tools/leantrail/shadow_ledger.py`

Tracks avoidance and resolution of shadow debt items across time.

### `tools/leantrail/critic_packets.py` / `critic_prompt_builder.py`

Generates LLM prompt packets for socratic review of hole/vacuity findings.
Emits `artifacts/leantrail/critic_prompts.jsonl`.

### `tools/leantrail/dedup_candidates.py`

Identifies structural deduplication candidates — declarations that may be
aliases of each other based on expression fingerprint matching.

### `tools/leantrail/arango_*.py`

ArangoDB integration:
- `arango_ingest.py` — Load snapshot into ArangoDB
- `arango_physics_evaluator.py` — Local surprisal evaluation along dependency paths

---

## Layer 4: API & Server

### `leantrail/api/server.py`

Flask/HTTP server exposing the query API:

| Endpoint | Description |
|----------|-------------|
| `GET /search?q=...` | Substring search over declarations |
| `GET /decl/{name}` | Full declaration info + incoming/outgoing edges |
| `GET /neighborhood/{name}?radius=2` | BFS neighborhood |
| `GET /path?from=...&to=...&lawful_only=true&state_policy=any` | Shortest path |
| `GET /proofstate?file=...&line=...&col=...` | Live proof state via Lean RPC |
| `GET /coherence/hotspots` | Top coherence hotspots |
| `GET /holonomy/hotspots?limit=25&alpha=1.5&beta=2.0&gamma=3.0&min_score=0.0` | Holonomy hotspots |
| `POST /bridge-candidate` | Create bridge candidate packet |

**Run:**
```bash
python3 -m leantrail.api.server \
  --repo-root . \
  --snapshot artifacts/leantrail/graph_snapshot.json \
  --host 127.0.0.1 --port 8765
```

### `leantrail/backend/rpc_adapter.py`

Adapts the Lean RPC protocol for proof-state queries. Wraps `lake env lean`
invocations for live interaction with the Lean environment.

### `leantrail/backend/indexer.py`

Python-side snapshot builder. Calls `normalizer.build_snapshot()` and
writes the result. Supports incremental mode: detects changed modules from
`git diff`, expands to impacted neighborhood, rebuilds only those modules,
merges patch into existing snapshot.

---

## The NonTriviality Biopsy System

**Location**: `lean/InfoGeometry/Lint/NonTriviality.lean`

This is the Lean-native vacuity detector. It is NOT a heuristic — it runs
inside the Lean kernel and inspects the actual expression trees.

### Configuration (`AuditConfig`)

```lean
abbrev AuditConfig := List Name × Nat × Bool × List Name × Bool
--                 projectRoots  depth  rejectLocalAxioms  allowedAxioms  allowSorry
```

Default: roots=`[InfoGeometry]`, depth=32, rejectLocalAxioms=true,
allowedAxioms=`[propext, Quot.sound, Classical.choice]`, allowSorry=true.

### The Expression Audit (`auditExprTrivialityDetailed`)

Recursively walks the full expression tree of a declaration's value:

| Expression form | Action |
|----------------|--------|
| `Expr.app fn arg` | Recursively audit both, merge results |
| `Expr.lam` / `Expr.forallE` / `Expr.letE` | Audit body, add node |
| `Expr.proj` | Audit struct, add node |
| `Expr.const declName` | **The key case** — see below |
| `Expr.mdata` | Audit inner body |
| `Expr.sort` / `Expr.lit` / `Expr.bvar` / `Expr.fvar` | Count as 1 node |
| `Expr.mvar` | Mark as vacuous socket |
| `sorry` | `Expr.getSorry?` → mark `containsSorry` |

**Constant classification** (`Expr.const declName`):

| Condition | Classification |
|-----------|---------------|
| `declName ∈ {Eq.refl, Iff.rfl, True.intro, False.elim}` | Trivial builtin |
| `declName` matches `_sorryProof`, `_True`, `_certificate`, `witness`, `socket`, etc. | **Suspicious** → mark `containsVacuousSockets` |
| `declName` is in project roots and `seen.contains` | Cycle → `containsVacuousSockets` |
| `declName` is in project roots and `depth == 0` | Hit unfold limit → `containsVacuousSockets` |
| `declName` is in project roots | Unfold value and recurse with `depth - 1` |
| `declName` is external and is `thmInfo`/`axiomInfo` | **Genuine gate** → `hasNontrivialConst` |
| `declName` is external and is `defnInfo` | Neutral |
| `declName` not found in env | Count as 1 node |

### The Transitive Audit (`auditTransitiveDependencies`)

After the expression audit, runs a separate pass:
1. `Lean.collectAxioms declName` — get all axioms in transitive closure
2. Classify each axiom:
   - `sorryAx` + allowSorry → `honest_sorry` state
   - `sorryAx` + !allowSorry → `sorryAx` violation
   - Other forbidden → `forbidden_axiom` violation
3. Bounded DFS through dependency graph to catch opaque boundaries
   (declarations with no accessible value)

### The Vacuity Role Classifier (`classifyVacuityRole`)

```
if contamination == "honest_sorry"     → "closure_debt"
elif contamination != "clean"          → "contaminated"
elif !isProp                            → "type_boundary" or "gate"
elif isGenuine(metric)                  → "gate"
elif containsVacuousSockets or hitLimit → "fake_transport"
else                                    → "pure_conductor"
```

### The Genuineness Criterion (`MathfulnessMetric.isGenuine`)

```lean
def isGenuine (m : MathfulnessMetric) : Bool :=
  termNodeCount > 5 ∧
  utilizesMathlibAxioms ∧
  ¬containsVacuousSockets ∧
  ¬hitUnfoldLimit ∧
  ¬containsSorry
```

A theorem is **genuine** only if:
1. Its proof body has more than 5 term nodes
2. It references at least one external mathlib theorem/axiom
3. It doesn't contain vacuous sockets (cycles or trivial projections)
4. It didn't hit the unfold depth limit
5. It doesn't contain `sorry`

### JSON Output

```json
{
  "target": "InfoGeometry.Arithmetic.RHEquivalence.dikinOmega_pos",
  "name": "...",
  "module": "InfoGeometry.Arithmetic.RHEquivalence",
  "decl_kind": "theorem",
  "attrs": {
    "vacuity": {
      "role": "gate",
      "is_prop": true,
      "term_node_count": 42,
      "uses_external_gate": true,
      "contains_vacuous_sockets": false,
      "hit_unfold_limit": false,
      "contains_sorry": false,
      "unfolded_local_consts": [...],
      "suspicious_consts": []
    },
    "contamination": {
      "state": "clean",
      "violations": [],
      "all_axioms": ["propext"],
      "opaque_boundaries": [],
      "closure_debts": [],
      "hit_dependency_fuel_limit": false
    }
  }
}
```

---

## The `_True`/`_sorryProof` Pattern

This is the **central vacuity pattern** in the repository. It was discovered
during the code audit of `MajoranaPolyaHilbertSocket.lean` (60 `_True` fields,
112 `_sorryProof` fields, 171 `sorry` occurrences) and is now detected by
the shadow index and the NonTriviality biopsy tools.

### How It Works

```lean
structure SomeSocket where
  theoremStatement_True : Prop := by
    sorry                              -- ← UNPROVEN Prop, defaults to sorry
  theoremStatement_sorryProof :
    theoremStatement_True              -- ← ASSUMES the unproven Prop

theorem theoremStatement (S : SomeSocket) : S.theoremStatement_True :=
  S.theoremStatement_sorryProof        -- ← "proof" by field projection
```

### Why It Compiles

1. `theoremStatement_True` is a `Prop` field with default value `:= by sorry` — Lean accepts this because `sorry` can fill any goal
2. `theoremStatement_sorryProof` is a field of type `theoremStatement_True` — it just names the assumption
3. `theorem theoremStatement` projects the `_sorryProof` field — this is a valid proof in Lean because the structure HAS that field (even though the field's value came from `sorry`)

### What It Means

The "theorems" are **tautologies of their own assumptions**. The structure says
"I have a property P" (by `sorry`) and "I have a proof of P" (by naming the
assumption). The theorem then says "if you give me S, then P". This is
technically true because S contains a proof of P — but that proof was `sorry`.

### The Honest-Sorry Variant

When `allowSorry := true` in the audit config, the NonTriviality biopsy treats
`sorry` as "honest closure debt" rather than contamination. This is the
repository's policy: `sorry` is acceptable when it's visible, tracked, and the
structure is named with `_sorryProof` (making the debt explicit in the name).

---

## The Rep-Depth Architecture Grammar

The `@[rep_depth ...]` attribute system enforces a 6-layer architecture:

```
L0_Count          — counting, combinatorics (e.g., Fintype.card, Finset.sum)
L1_Projective     — projection, support, compression (e.g., projectors, idempotents)
L2_Operator       — operator-algebraic bridge (e.g., CliffordAlgebra, ι, polar)
L3_Krein          — Krein/doubled geometry (e.g., modular_j, complex_i, Tomita)
L4_ModularTransport — modular flow, transport (e.g., KMS, Bregman divergence)
L5_ThermodynamicClosure — free energy, closure (e.g., partition function, zeta)
```

**Adjacency rule**: A declaration at depth `d` may only depend on declarations at
depth `d` (same layer) or `d-1` (one layer down), unless tagged `@[capstone]`.

**Violations**:
- **REGRESSION**: `d` depends on `d' > d` (deeper layer) — not allowed
- **WORMHOLE**: `d` depends on `d' < d-1` (skips layers) — not allowed for non-capstones

**Audit commands**:
- `#audit_architecture` — checks adjacency for all tagged canonical declarations
- `#audit_rep_depth_coverage` — reports canonical declarations missing `@[rep_depth]`

---

## File Index

### Lean DAG Core
| File | Purpose |
|------|---------|
| `lean/DAG/Basic.lean` | Graph types, expression constant extraction |
| `lean/DAG/Indexer.lean` | Main declaration indexer (decls.jsonl + edges.jsonl) |
| `lean/DAG/Hydrate.lean` | SCC/topo/dominator computation |
| `lean/DAG/SCC.lean` | Tarjan's SCC algorithm |
| `lean/DAG/Topo.lean` | Topological sort |
| `lean/DAG/Dominators.lean` | Dominator tree |
| `lean/DAG/StructuralExport.lean` | SCC/topological structure export |
| `lean/DAG/ProcessFlowExport.lean` | Dependency role/boundary classification |
| `lean/DAG/ExprFingerprint.lean` | Expression content hashing |
| `lean/DAG/ExportDecls.lean` | Legacy declaration inventory exporter |
| `lean/DAG/ExportForwardGraph.lean` | Forward graph export |
| `lean/DAG/ExprArangoExport.lean` | ArangoDB expression graph export |
| `lean/DAG/DeclIndex.lean` | Declaration index utilities |
| `lean/DAG/SearchCore.lean` | Semantic search core |
| `lean/DAG/QueryEngine.lean` | Graph query engine |
| `lean/DAG/Disassembler.lean` | Expression disassembly |
| `lean/DAG/GlobalDisassembler.lean` | Whole-environment disassembly |
| `lean/DAG/DisconnectedCapstoneAudit.lean` | Identifies capstones unreachable from roots |
| `lean/DAG/ExactProoflessnessAudit.lean` | Identifies declarations backed by axioms/opaques |

### Lean Meta Attributes
| File | Purpose |
|------|---------|
| `lean/InfoGeometry/Meta/Architecture.lean` | `@[rep_depth]`, `@[capstone]`, `#audit_architecture` |
| `lean/InfoGeometry/Meta/Vacuity.lean` | `@[infrastructure]`, `@[terminal]`, `@[expository]` |
| `lean/InfoGeometry/Meta/OwnerTarget.lean` | Owner target interface |
| `lean/InfoGeometry/Meta/BridgeTarget.lean` | Bridge target interface |
| `lean/InfoGeometry/Meta/SocketTarget.lean` | Socket target interface |
| `lean/InfoGeometry/Meta/ShadowLedger.lean` | Shadow debt ledger |

### Lean Lint
| File | Purpose |
|------|---------|
| `lean/InfoGeometry/Lint/NonTriviality.lean` | `#biopsy_non_triviality` command, expression audit |

### Python Scripts (CLI entry points)
| Script | Purpose |
|--------|---------|
| `scripts/leantrail_snapshot.py` | `python3 -m tools.leantrail.snapshot_summary` |
| `scripts/leantrail_decl.py` | `python3 -m tools.leantrail.decl_lookup` |
| `scripts/leantrail_dedup.py` | `python3 -m tools.leantrail.dedup_candidates` |

### Python Tools (LeanTrail)
| Tool | Purpose |
|------|---------|
| `tools/leantrail/snapshot_summary.py` | Print snapshot metadata summary |
| `tools/leantrail/decl_lookup.py` | Look up a declaration by fully qualified name |
| `tools/leantrail/vacuity_audit.py` | Run `#biopsy_non_triviality` on selected declarations |
| `tools/leantrail/hole_packets.py` | Build ranked hole packets from failure transitions |
| `tools/leantrail/shadow_index.py` | Text-level sorry/vacuity scanner |
| `tools/leantrail/surgery_plan.py` | networkx-based graph surgery planner |
| `tools/leantrail/conformance.py` | Cross-format parity check |
| `tools/leantrail/export.py` | Export snapshot to GraphML/Neo4j/Arango |
| `tools/leantrail/critic_packets.py` | Generate LLM critic prompt packets |
| `tools/leantrail/critic_prompt_builder.py` | Build LLM prompts from vacuity/hole data |
| `tools/leantrail/dedup_candidates.py` | Identify structural dedup candidates |
| `tools/leantrail/path_lock_registry.py` | Register bound/locked dependency paths |
| `tools/leantrail/failure_harvester.py` | Harvest process-flow defects |
| `tools/leantrail/shadow_ledger.py` | Track shadow debt avoidance/resolution |
| `tools/leantrail/arango_ingest.py` | Load snapshot into ArangoDB |
| `tools/leantrail/arango_physics_evaluator.py` | Local surprisal evaluation |
| `tools/leantrail/adapters.py` | GraphML/Neo4j/Arango import adapters |
| `tools/leantrail/vacuity_ingest.py` | Ingest vacuity audit results |

### Python Infra (Orchestration)
| Tool | Purpose |
|------|---------|
| `tools/infra/refresh_decl_graph.py` | Full DAG refresh cycle |
| `tools/infra/refresh_blueprint_tags.py` | Extract rep-depth/capstone tags |
| `tools/infra/run_locked_lake_build.py` | Prebuild under file lock |
| `tools/infra/artifacts.py` | Artifact path utilities, olean hash, staleness check |
| `tools/infra/build.py` | Indexer command construction, hash computation |
| `tools/infra/timings.py` | Indexer timing sidecar |
| `tools/infra/decl_graph.py` | Declaration graph data structures |
| `tools/infra/decl_graph_support.py` | Graph utilities |

### Python Backend (LeanTrail)
| Module | Purpose |
|--------|---------|
| `leantrail/backend/models.py` | `NodeRecord`, `EdgeRecord`, `GraphSnapshot` |
| `leantrail/backend/normalizer.py` | `LeanTrailNormalizer.build_snapshot()` |
| `leantrail/backend/store.py` | `GraphStore` — in-memory graph DB |
| `leantrail/backend/query_api.py` | `LeanTrailQueryAPI` — staleness, search, path, bridge |
| `leantrail/backend/indexer.py` | Python-side snapshot build orchestration |
| `leantrail/backend/extractor.py` | Subprocess runner for DAG refresh commands |
| `leantrail/backend/rpc_adapter.py` | Lean RPC protocol adapter |
| `leantrail/api/server.py` | HTTP API server |

### Artifact Schemas
| Schema | Purpose |
|--------|---------|
| `leantrail/schemas/leantrail_graph_snapshot.schema.json` | Snapshot JSON schema |
| `leantrail/schemas/leantrail_bridge_request.schema.json` | Bridge request JSON schema |
