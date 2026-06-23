# Lean DAG / LeanTrail Toolchain Reference

This document records the actual code path for the repository graph, InfoTree,
LeanTrail, and proof-debt tooling.  It is based on direct source inspection of
Lean, Lake, and Python files.  It is **not** based on stale docstrings or
narrative reports.

Core rule:

```text
Lean elaboration/kernel data is foundational.
Python scripts are downstream consumers, wrappers, validators, ingesters,
reporters, and query tools.
```

Python never proves declarations and does not own the semantic graph.  The data
that Python processes is prepared by Lean code running over the elaborated Lean
environment or over compiler InfoTrees.

---

## 1. Authority layers

### Layer 0: Lean source and Lake build graph

Source files under `lean/` are the only source of formal declarations.  Lake
builds modules and executables from those files.

Important Lake declarations in `lakefile.lean`:

| Lake item | Root | Role |
|---|---|---|
| `lean_exe dagIndexer` | `DAG.Indexer` | authoritative declaration DAG exporter |
| `lean_exe infotreeExtract` | `DAG.InfoTreeExtract` | compiler InfoTree/tactic transition extractor |
| `lean_exe groundTruthHarvester` | `DAG.GroundTruthHarvester` | InfoTree/tactic ground-truth harvester |
| `lean_exe disconnectedAudit` | `DAG.DisconnectedAudit` | Lean-side audit executable |
| `lean_exe exactProoflessnessAudit` | `DAG.ExactProoflessnessAudit` | Lean-side prooflessness audit executable |
| `package_facet dagMeta` | calls `tools/infra/dag_refresh.py` after building `dagIndexer` and `InfoGeometry.All.olean` | Lake-tracked DAG metadata refresh |
| `package_facet dagArtifactsManifest` | calls `tools/infra/dag_manifest.py` after building `dagIndexer` and `InfoGeometry.All.olean` | Lake-tracked artifact manifest |

The facets are important: they show the intended ownership order.  Lake first
builds Lean artifacts (`dagIndexer`, `InfoGeometry.All.olean`), then Python runs
a wrapper around the Lean executable.

### Layer 1: Lean environment extraction

These files produce declaration-level graph data from the elaborated Lean
environment:

| Lean file | What it prepares for Python |
|---|---|
| `lean/DAG/Basic.lean` | foundational graph type and dependency extraction from `ConstantInfo` |
| `lean/DAG/DeclIndex.lean` | direct dependency and reverse-user maps |
| `lean/DAG/Indexer.lean` | canonical JSON/JSONL export of declarations, edges, morphisms, types, full graph, structural topology |
| `lean/DAG/Hydrate.lean` | SCC condensation, DAG, predecessors, topological order, dominators |
| `lean/DAG/StructuralExport.lean` | `structural-topology.json` rows: components, membership, roots, capstones, layers, dominators |
| `lean/DAG/ExportForwardGraph.lean` | legacy/simple forward graph exporter; compatibility layer, not current authority |

The key primitive is in `lean/DAG/Basic.lean`:

```lean
def collectExprConsts (e : Lean.Expr) : Lean.NameSet

def edgesFromConstantInfo (ci : Lean.ConstantInfo)
    : Array (Lean.Name × EdgeKind)

def buildGraphFromEnv (env : Lean.Environment) (nsPrefix? : Option String := none)
    : Graph Lean.Name
```

This means the graph is extracted from elaborated `ConstantInfo` type/value
expressions, not from comments.

`lean/DAG/Indexer.lean` then imports modules, reads the Lean environment, folds
over `env.constants`, filters by namespace, processes constants, filters edges,
and writes artifacts.

Canonical artifacts written by `DAG.Indexer`:

```text
artifacts/dag/index/decls.jsonl
artifacts/dag/index/edges.jsonl
artifacts/dag/index/raw_edges.jsonl
artifacts/dag/index/morphisms.jsonl
artifacts/dag/index/types.jsonl
artifacts/dag/index/edge-leakage.json
artifacts/dag/index/meta.json
artifacts/dag/full_graph.json
artifacts/dag/structural-topology.json
```

### Layer 2: Lean InfoTree extraction

These files tap Lean compiler InfoTrees and prepare tactic/proof-state data for
Python consumers:

| Lean file | What it prepares |
|---|---|
| `lean/DAG/InfoTreeExtract.lean` | compact tactic transition + declaration rows for one file |
| `lean/DAG/RawInfoTreeExport.lean` | raw, multi-table InfoTree projection for one file |
| `lean/DAG/BlockExport.lean` | semantic block extraction and InfoTree dependency/morphism extraction |
| `lean/DAG/GroundTruthHarvester.lean` | tactic-step harvesting from InfoTrees |
| `lean/DAG/HolonomyExporter.lean` | telemetry packets from a single InfoTree |

`InfoTreeExtract.lean` runs the frontend with `infoState.enabled := true`, then
walks `frontendState.commandState.infoState.trees`.  It serializes tactic
transitions with ranges, source snippets, goals before/after, constant
references, and local context slots.

`RawInfoTreeExport.lean` is the richer compiler-memory lane.  It serializes
many JSONL tables, including:

```text
raw_infotree_roots.jsonl
raw_infotree_nodes.jsonl
raw_infotree_edges.jsonl
raw_infotree_payloads.jsonl
raw_infotree_payload_fields.jsonl
raw_infotree_contexts.jsonl
raw_infotree_decl_links.jsonl
raw_infotree_env_refs.jsonl
raw_infotree_mctx_refs.jsonl
raw_infotree_mctx_decls.jsonl
raw_infotree_lctx_refs.jsonl
raw_infotree_lctx_decls.jsonl
raw_infotree_goal_states.jsonl
raw_infotree_fvar_lineage.jsonl
raw_infotree_tactic_arguments.jsonl
raw_infotree_messages.jsonl
raw_infotree_projection_leakage.jsonl
```

Those rows are compiler-derived surfaces.  Python only batches, validates,
merges, imports, and queries them.

### Layer 3: Python orchestration and consumers

Python scripts do not create formal truth.  They run Lean exporters, check
freshness, import JSONL into databases, build reports, and expose query tools.

Important Python wrappers/consumers:

| Python file | Layer | Role |
|---|---:|---|
| `tools/infra/refresh_decl_graph.py` | wrapper | calls `dagIndexer` / `lean/DAG/Indexer.lean` and stamps metadata |
| `tools/infra/build.py` | wrapper | constructs indexer command and locked prebuild invocation |
| `tools/infra/dag_refresh.py` | wrapper | config-driven DAG refresh entrypoint |
| `tools/infra/dag_status.py` | monitor | checks DAG artifact status |
| `tools/infra/dag_all.py` | orchestration | runs the larger DAG refresh/report pipeline |
| `tools/infra/dag_doctor.py` | diagnostic | checks indexer executable/artifact health |
| `tools/infra/batch_raw_infotree_export.py` | wrapper | runs `RawInfoTreeExport.lean` file-by-file and merges only validated rows |
| `tools/infra/validate_raw_infotree_export.py` | validator | validates raw InfoTree output directories |
| `tools/infra/arango_raw_infotree_ingest.py` | database ingest | imports raw InfoTree JSONL tables into Arango |
| `tools/infra/arango_raw_infotree_graph.py` | database graph | creates/probes named Arango graph over raw InfoTree tables |
| `tools/infra/verify_raw_infotree_arango_descent.py` | database audit | verifies Arango descent invariants for raw InfoTree rows |
| `tools/infra/hydrate_arango_topology.py` | database ingest/enrichment | hydrates Arango topology from DAG artifacts |
| `tools/infra/hydrated_dag_to_lean_graph.py` | projection | converts hydrated DAG data into another graph view |
| `tools/infra/generate_structural_dedup.py` | report | analyzes structural duplication and shadow relations |
| `tools/infra/causal_cone_spectrum.py` | report | reads `structural-topology.json` and `decls.jsonl` |
| `tools/infra/context_preflight.py` | retrieval | gathers code/DAG/LeanTrail context for a query |
| `tools/leantrail/decl_lookup.py` | query | looks up declaration data in LeanTrail snapshots |
| `leantrail/backend/indexer.py` | LeanTrail ingest | reads DAG artifacts into LeanTrail backend structures |
| `leantrail/backend/normalizer.py` | LeanTrail normalize | normalizes DAG/decl data for LeanTrail snapshots |

---

## 2. Canonical declaration-DAG pipeline

The authoritative declaration graph path is:

```text
Lean source files
  -> Lake builds InfoGeometry.All.olean and dagIndexer
  -> lean/DAG/Indexer.lean imports InfoGeometry.All
  -> Lean Environment / ConstantInfo / Expr traversal
  -> decls.jsonl, edges.jsonl, raw_edges.jsonl, morphisms.jsonl, types.jsonl
  -> full_graph.json
  -> hydrate in Lean: SCCs, DAG, topo, dominators
  -> structural-topology.json
  -> Python consumers: LeanTrail, Arango, reports, context tools
```

Concrete command path in Python:

```text
tools/infra/refresh_decl_graph.py
  -> tools/infra/build.py:build_indexer_command
  -> lake env .lake/build/bin/dagIndexer ...
     or lake exe dagIndexer ...
     or lake env lean --run lean/DAG/Indexer.lean ...
```

`refresh_decl_graph.py` also computes olean/source hashes and may skip a refresh
only if artifacts are fresh.  That skip logic is a wrapper optimization; it does
not change the source of truth.

---

## 3. InfoTree/raw compiler-memory pipeline

The raw InfoTree path is:

```text
Lean source file
  -> Lean frontend with infoState.enabled := true
  -> commandState.infoState.trees
  -> lean/DAG/RawInfoTreeExport.lean
  -> per-file raw_infotree_*.jsonl tables
  -> tools/infra/batch_raw_infotree_export.py validates and merges
  -> tools/infra/arango_raw_infotree_ingest.py imports rows
  -> tools/infra/arango_raw_infotree_graph.py creates graph overlays
  -> tools/infra/verify_raw_infotree_arango_descent.py audits descent invariants
```

The compact InfoTree extractor path is:

```text
Lean source file
  -> lean_exe infotreeExtract / DAG.InfoTreeExtract
  -> tactic transition rows and declaration rows
```

Again, Python is downstream.  The data is produced by Lean frontend/compiler
state.

---

## 4. LeanTrail placement

LeanTrail is a graph/snapshot/query layer over Lean-produced artifacts.

Typical inputs:

```text
artifacts/dag/index/decls.jsonl
artifacts/dag/index/edges.jsonl
artifacts/dag/full_graph.json
artifacts/dag/structural-topology.json
artifacts/leantrail/graph_snapshot.json
```

Key files:

| File | Role |
|---|---|
| `leantrail/backend/models.py` | backend data models |
| `leantrail/backend/store.py` | snapshot/storage access |
| `leantrail/backend/indexer.py` | reads DAG artifacts such as `decls.jsonl` |
| `leantrail/backend/normalizer.py` | normalizes DAG declarations/edges into snapshot form |
| `tools/leantrail/decl_lookup.py` | declaration lookup CLI |
| `tools/leantrail/export.py` | export utility |

LeanTrail is evidence and navigation.  It is not a proof checker.  A LeanTrail
lookup must still be followed by direct owner-file inspection and `lake env lean
owner/file.lean` when truth matters.

---

## 5. Architectural decisions

1. **Lean owns semantic extraction.**
   The declaration DAG comes from `Lean.Environment`, `ConstantInfo`, and
   elaborated `Expr`s.  Raw proof-state data comes from compiler `InfoTree`s.

2. **Python owns operational plumbing.**
   Python scripts run commands, validate outputs, batch per-file jobs, stamp
   metadata, ingest into Arango, build reports, and provide search/query tools.

3. **Artifacts are evidence, not proof.**
   JSON/JSONL/Arango/LeanTrail artifacts are useful only as derived evidence.
   They do not replace kernel checking.

4. **Direct owner-file checks dominate graph reports.**
   If graph data says a declaration exists or is clean, verify the owner file
   and run:

   ```bash
   lake env lean path/to/owner.lean
   ```

5. **`lake build` alone can miss unimported files.**
   For suspicious or new owner files, direct `lake env lean file.lean` is the
   required check.

6. **Raw InfoTree export must be file-scoped and validated.**
   `batch_raw_infotree_export.py` deliberately avoids poisoning a global export
   with one failed file.  It validates each per-file export before merging.

---

## 6. Vacuity, `_True`, and `_sorryProof` patterns

Repository policy says missing proofs must remain explicit theorem debt.  The
bad pattern is laundering proof debt behind fields or theorem names that look
closed but carry no mathematical content.

High-risk patterns include:

```lean
some_claim_True : Prop := True
some_claim_True : True := by trivial
some_claim_sorryProof : some_claim_True := by sorry
some_claim_certificate : Prop := by sorry
some_claim_valid : Prop := True
```

Why this is dangerous:

```text
name claims content
  + formal statement is True or a wrapper Prop
  + proof is trivial/sorry/opaque
  = semantic inflation / fake closure
```

Relevant tools:

| Tool | Role |
|---|---|
| `scripts/vacuity-linter.py` | regex/AST-style linter for obvious vacuity patterns |
| `scripts/quality/mathless_proof_audit.py` | finds skeletal `rfl`/`trivial`/`simp`/`aesop`-only proof bodies |
| `tools/infra/vacuity_critic.py` | learns/records obfuscation-pattern synonyms such as `_True`, `_sorryProof`, `_certificate`, `_valid`, `_witness`, `_bridge` |
| `tools/planner/*` | ranks vacuity/replacement/corridor candidates |
| `tools/infra/shadow_cone_scanner.py` | scans `sorry` shadows and computes past/future cones |
| `tools/infra/hollow_semantic_auditor.py` | audits name/docstring/type mismatch and tautological propositions |

The critic’s built-in high-risk suffixes include:

```text
_True
_sorryProof
_certificate
_valid
_witness
_bridge
```

These tools are triage only.  They can flag suspect code, but only Lean source
and kernel checking decide whether a theorem is valid.

---

## 7. NonTriviality biopsy / critic lane

The repository uses a biopsy-style discipline: classify declarations by local
proof shape, dependencies, contamination, and source evidence before acting.

The Critic Lane policy in `docs/LeanTrailCriticLane.md` is:

```text
LLM creates hypotheses about problems.
LeanTrail stores and ranks them.
Humans review them.
Lean kernel validates any resulting code.
```

Inputs mentioned there include:

```text
artifacts/leantrail/graph_snapshot.vacuity.json
artifacts/leantrail/proof_hole_packets.jsonl
artifacts/leantrail/bridge_packets.jsonl
artifacts/leantrail/alignment_packets.jsonl
```

Critic/biopsy categories include:

| Category | Meaning |
|---|---|
| `proof_shape_name_mismatch` | substantive name but weak/vacuous proof shape |
| `docstring_statement_mismatch` | prose claims more than the formal statement proves |
| `honest_sorry_triage` | visible proof debt; track, do not hide |
| `obfuscation_suspicion` | local axioms, opaque placeholders, certificate sockets, renamed admit mechanisms |
| `orphan_genuine_review` | real math disconnected from protected roots; preserve and bridge |
| `axiomatic_frontier_review` | theorem region supported by axioms/opaque boundaries |
| `alignment_candidate_review` | possible bridge candidate from graph/Hodge/de Bruijn overlap |
| `educational_alias_protection` | wrapper may be pedagogical; do not delete automatically |

Important distinction:

```text
explicit sorry        = honest proof debt
transitive sorry      = quarantined dependency path
laundered sorry/True  = unsafe closure; reject or quarantine
```

A NonTriviality biopsy therefore asks:

1. What is the actual Lean statement?
2. Does the proof body use `sorry`, `admit`, local axioms, opaque stand-ins, or
   trivial proof for a grand theorem name?
3. Does the declaration depend transitively on `sorryAx` or known sockets?
4. Does the theorem state real content, or only `True` / a wrapper Prop?
5. Is it an owner theorem, translator, coherence lemma, capstone, or shadow?
6. Does direct `lake env lean owner.lean` succeed?

Only after those checks can a declaration be called theorem-backed.

---

## 8. How to answer “where did this graph/data come from?”

Use this chain:

```text
For declaration DAG data:
  lean/DAG/Basic.lean
  lean/DAG/Indexer.lean
  lean/DAG/Hydrate.lean
  lean/DAG/StructuralExport.lean
  artifacts/dag/index/*.jsonl
  artifacts/dag/full_graph.json
  artifacts/dag/structural-topology.json

For raw compiler/tactic data:
  lean/DAG/InfoTreeExtract.lean
  lean/DAG/RawInfoTreeExport.lean
  artifacts/raw_infotree or artifacts/infotree raw_infotree_*.jsonl

For Python consumers:
  tools/infra/refresh_decl_graph.py
  tools/infra/batch_raw_infotree_export.py
  tools/infra/arango_*infotree*.py
  leantrail/backend/*.py
  tools/leantrail/*.py
```

Short answer:

```text
The Lean code prepares the data.
Python reads the Lean-produced artifacts and builds operational views.
```

---

## 9. Minimal trusted commands

Refresh canonical declaration DAG:

```bash
python3 tools/infra/refresh_decl_graph.py --force
```

Or via Lake script/facet if configured:

```bash
lake script run dagRefresh
lake script run dagStatus
```

Direct run of the Lean indexer:

```bash
lake env lean --run lean/DAG/Indexer.lean \
  InfoGeometry.All InfoGeometry \
  artifacts/dag/index \
  artifacts/dag/full_graph.json \
  artifacts/dag/structural-topology.json
```

Raw InfoTree export for one file:

```bash
lake env lean --run lean/DAG/RawInfoTreeExport.lean \
  lean/Some/File.lean artifacts/raw_infotree/some_file
```

Batch raw InfoTree export:

```bash
python3 tools/infra/batch_raw_infotree_export.py --roots lean/InfoGeometry
```

Declaration lookup:

```bash
python3 tools/leantrail/decl_lookup.py \
  --name Fully.Qualified.Declaration.Name \
  --format json
```

Owner-file truth check:

```bash
lake env lean lean/path/to/Owner.lean
```

---

## 10. Bottom line

The repository has two Lean-produced data foundations:

1. **Environment/ConstantInfo DAG** from `lean/DAG/Indexer.lean` and
   `lean/DAG/Basic.lean`.
2. **Compiler InfoTree/tactic-state data** from `lean/DAG/InfoTreeExtract.lean`
   and `lean/DAG/RawInfoTreeExport.lean`.

Everything Python does sits on top of those foundations.
