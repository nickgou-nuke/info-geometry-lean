# Repository Deep Search Protocol

> Status: `current authority`
> Scope: mandatory code-grounded discovery before answering repository questions.
> Rule: docs, generated reports, docstrings, file names, and transcripts are hints
> only. Executable source, Lean owner files, Lake entrypoints, and build output
> decide what exists.

## Why This Exists

This repository changes faster than prose. A new Lean owner module, Python
ingester, Arango collection, or Pi tool can be added without every README,
docstring, and generated report being updated. Agents must therefore search the
implementation from several independent angles before answering questions about
what is present, stale, missing, or proved.

Do not answer from names alone. A file called "bridge" or "capstone" is not
proof. A file under `external_refs/` can be valuable context without being
repo-owned proof authority. A generated artifact can be useful evidence without
being a source of truth.

## Search Surfaces

Use these labels consistently when searching and reporting:

| Surface | Meaning | Default authority |
|---|---|---|
| `repo-owned` | `lean/`, `tools/`, `scripts/`, `src/`, root TypeScript tools, `lakefile.lean`, `package.json` | authoritative for implementation |
| `external-ref` | `external_refs/**`, mirrored repos, vendored examples | context only unless explicitly promoted |
| `generated-artifact` | `artifacts/`, `reports/`, `paper_node/`, `witnesses/auto_sympy/`, cached graph exports | evidence only |
| `runtime-state` | `.runtime/`, `.hermes/tmp/`, provider caches | never proof authority |
| `archive` | quarantine/outdated/archive folders | historical only |
| `docs` | `docs/`, README-style prose, generated handovers | routing/hints unless a current authority document says otherwise |

When a question asks "what is in the repo", start with `repo-owned`. Then add
`external-ref` only when the question explicitly asks about installed mirrors,
libraries, Loogle indexing, or external comparison.

## Current Code-Derived Inventory Snapshot

Regenerate these counts when precision matters. They intentionally overlap
because one tool can serve multiple lanes.

Scan basis: repo-owned tool surfaces excluding `external_refs/**`,
`node_modules/**`, `.lake/**`, `.runtime/**`, `artifacts/**`, `reports/**`,
archives, and docs.

| Lane | Count observed | What it means |
|---|---:|---|
| Python tool files | 578 | Python scripts/modules in repo-owned tool surfaces |
| Shell tool files | 62 | shell entrypoints/wrappers |
| Root TypeScript Pi tools | 8 | Pi/aiClaw/Arango extension tools at repo root |
| AQL/query assets | 11 | AQL query assets for graph/RAG layers |
| JSON schema/config assets | 56 | tool schemas, graph schemas, query configs |
| Lake scripts | 67 | `script ...` entrypoints in `lakefile.lean` |
| Lake Lean executables | 9 | `lean_exe ...` entrypoints in `lakefile.lean` |
| Lake package facets | 2 | DAG artifact/package facets |
| NPM scripts | 19 | `package.json` operational aliases |
| Arango brain surfaces | 148 | files with Arango graph/query/ingest behavior |
| GraphRAG/semantic surfaces | 59 | text, semantic, retrieval, embedding, and RAG code |
| DAG/decl-graph surfaces | 228 | Lean declaration graph, DAG, graph audit, and report code |
| LeanTrail surfaces | 44 | LeanTrail export/ingest/vacuity/critic/path-lock code |
| Raw InfoTree surfaces | 37 | compiler-memory raw InfoTree export/ingest/validation code |
| Search/index/ingest surfaces | 341 | local/external indexing, retrieval, and ingestion code |
| Python CLI surfaces | 455 | Python files with CLI signatures |

These are not "different products"; they are toolchain surfaces. The practical
toolchains are listed below.

## Distinct Search And Indexing Toolchains

### 1. Lean Kernel And Lake Entry Points

Authority lane for proof truth.

Code surfaces:

```text
lakefile.lean
lean/DAG/*
lean/InfoGeometry/*
```

Core commands:

```bash
lake env lean lean/InfoGeometry/Path/Owner.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Path.Owner
lake script run dagStatus
lake script run dagRefresh
lake script run dagAll
```

Use this lane to answer whether a theorem, owner module, import, axiom, sorry,
or build target is real.

### 2. Local LeanSearch And Loogle

Retrieval lane for Lean declarations. This is navigation, not proof authority.

Code surfaces:

```text
tools/infra/leansearch_local.py
tools/infra/hive_leansearch_bee.py
tools/infra/hive_loogle_bee_worker.py
tools/run_leansearch_safe.sh
scripts/infra/index_all_repos.sh
scripts/infra/build_and_index.sh
external_refs/loogle
```

Important distinction:

```text
LeanSearch local = deterministic records from local DAG artifacts.
Loogle = theorem search service/index, including external indexed libraries.
```

Use filters when Loogle/external refs are included; do not mix Loogle hits with
repo-owned owner theorem claims.

### 3. Text/Literature GraphRAG Brain

Semantic text/library memory. This is good for context, citations, external
source retrieval, and prior-art recall.

Code surfaces:

```text
arango-rag-tool.ts
commit-conscious-knowledge.ts
setup-db.ts
scripts/index-external-repos.py
scripts/harvest-knowledge.sh
tools/alexandria/semantic_ingest.py
tools/alexandria/retrieve_context.py
tools/infra/graph_rag_query.py
tools/infra/graphrag_context.py
tools/infra/ask_repo.py
tools/infra/graphrag/*
```

Observed default database/collections:

```text
AICLAW_ARANGO_DB=aiclaw_auto_rag
literature_nodes
citation_edges
literature_search_view
knowledge_base.json fallback
```

This brain answers "what context/literature/source text is known?" It does not
answer "what has Lean proved?" without a Lean owner check.

## ArangoDB Schema Families

As of the current code scan, repo-owned scripts expose at least four physical
database defaults and fourteen logical Arango schema families. These families
overlap by design; some are overlays inside the same database.

Physical database defaults:

| Default | Evidence | Role |
|---|---|---|
| `aiclaw_auto_rag` on `http://127.0.0.1:8540` | `tools/infra/aiclaw_auto_arango.py`, root Pi tools | isolated natural-language/proof-memory RAG |
| `infogeometry` on `http://127.0.0.1:8530` | `src/igf/config/env_aliases.py` | repo DAG, InfoTree, graph overlays, scheduling sidecars |
| `alexandria` | `tools/alexandria/arango_ingest.py`, `tools/alexandria/automathtext_arango_ingest.py` | literature and AutoMathText ingestion |
| `hive_live` | `tools/infra/hive_arango_queue.py` and Hive workers | live Hive queue/packet memory |

Important caveat: `arango_database(default)` returns `ARANGO_DATABASE` when it
is set, even if a script passes a different default such as `hive_live`.
Agents must report the resolved database from the run, not assume the default.

Logical schema families:

| # | Family | Main collections | Primary scripts |
|---:|---|---|---|
| 1 | aiClaw natural-language/proof-memory RAG | `literature_nodes`, `citation_edges`, `literature_search_view` | `tools/infra/aiclaw_auto_arango.py`, `setup-db.ts`, `arango-rag-tool.ts`, `commit-conscious-knowledge.ts` |
| 2 | Alexandria classic literature graph | `alexandria_documents`, `alexandria_sections`, `alexandria_chunks`, `alexandria_entities`, `alexandria_*_edges` | `tools/alexandria/arango_ingest.py` |
| 3 | AutoMathText-V2 ancestry/theorem graph | `automath_fragments`, `automath_chunks`, `automath_entities`, `automath_expr_nodes`, `automath_theorem_shapes`, `automath_overlay_nodes`, `automath_*_edges` | `tools/alexandria/automathtext_v2_ingest.py`, `tools/alexandria/automathtext_arango_ingest.py` |
| 4 | txt2kg external-text KG and predigestion | `txt2kg_sources`, `txt2kg_chunks`, `txt2kg_triples`, `txt2kg_entities`, `txt2kg_relationships` | `tools/alexandria/txt2kg_hive_ingest.py` |
| 5 | LeanTrail / expression base graph | `ig_nodes`, `ig_edges` | `tools/leantrail/arango_ingest.py`, `tools/infra/arango_expr_graph_ingest.py` |
| 6 | layered SCC/topology overlay | `topology_overlay`, `topology_overlay_edges`, optionally `raw_info_nodes`, `raw_info_edges` | `tools/infra/materialize_lossless_infotree.py`, `tools/infra/hydrate_arango_topology.py`, `tools/infra/arango_layered_ingest.py` |
| 7 | chiral patch sidecar | `ig_patch_runs`, `ig_chiral_patches`, `ig_patch_spectral_signatures`, `ig_patch_members`, `ig_patch_edges` | `src/igf/*`, `tools/infra/ingest_chiral_sidecars.py` |
| 8 | wire topology / De Bruijn / logic vectors | `ig_wires`, `ig_gates`, `ig_wire_edges`, `ig_scc`, `ig_hashes`, `ig_logic_tokens`, `ig_logic_vectors`, `ig_text_index_docs`, `ig_translation_*`, optional certificate edges | `tools/infra/arango_wire_topology_ingest.py` |
| 9 | derived Arango DAG algorithms | `arango_dag_components`, `arango_dag_layers`, `arango_dag_wl_labels`, `arango_dag_hodge`, `arango_dag_chiral`, `arango_dag_dirac`, and related `arango_dag_*` collections | `tools/infra/arango_dag_algorithms.py` |
| 10 | raw InfoTree compiler-memory brain | `raw_infotree_*` row collections and `raw_infotree_*_edges` | `tools/infra/batch_raw_infotree_export.py`, `tools/infra/arango_raw_infotree_ingest.py`, `tools/infra/arango_raw_infotree_graph.py` |
| 11 | Hive live queue and packet memory | `hive_goals`, `hive_tasks`, `hive_workers`, `hive_events`, `hive_*_packets`, `hive_*_edges` | `tools/infra/hive_arango_queue.py`, Hive workers |
| 12 | semantic content audit scheduler | `semantic_content_audit_runs`, `semantic_content_audit_modules`, `semantic_content_audit_findings`, `semantic_content_audit_importer_edges`, optional `hive_tasks` | `tools/infra/ingest_semantic_content_audit.py` |
| 13 | prima materia claim graph | `prima_materia_artifacts`, `claims`, `graph_morphisms` | `tools/infra/prima_materia_ingest.py` |
| 14 | Hive purified shadow consensus | `hive_purified_shadow_batches`, `hive_purified_shadow_nodes`, `hive_purified_shadow_edges` | `tools/infra/shadow_plant_worker.py` |

The natural-language ArangoDB is family 1, and Alexandria families 2-4 are also
language/text ingestion lanes. None of them are Lean proof authority.

### 4. Declaration DAG / IGF Patch Graph Brain

Repo graph memory for declarations, patch topology, structural overlays, and
process-flow audits.

Code surfaces:

```text
src/igf/cli.py
src/igf/pipeline/*
src/igf/graph/*
tools/infra/dag_*.py
tools/infra/refresh_decl_graph.py
tools/infra/decl_graph.py
tools/infra/hydrated_dag_to_lean_graph.py
tools/infra/arango_layered_ingest.py
tools/infra/arango_dag_algorithms.py
tools/infra/arango_wire_topology_ingest.py
```

Observed IGF collections:

```text
ig_patch_runs
ig_chiral_patches
ig_patch_spectral_signatures
ig_patch_members
ig_patch_edges
```

Use this brain to find source/sink declarations, wrappers, stale wires,
dependency topology, and likely owner modules. Then descend to Lean source.

### 5. Raw InfoTree / Compiler-Memory Brain

Compiler-side raw InfoTree and parent-document lineage. This is the lane for
projection leakage, context trees, local contexts, metavariable contexts, and
source-to-node edges.

Code surfaces:

```text
lean/DAG/RawInfoTreeExport.lean
tools/infra/batch_raw_infotree_export.py
tools/infra/validate_raw_infotree_export.py
tools/infra/arango_raw_infotree_ingest.py
tools/infra/arango_raw_infotree_graph.py
tools/infra/materialize_lossless_infotree.py
tools/infra/hydrate_arango_topology.py
tools/infra/verify_raw_infotree_arango_descent.py
tools/infra/verify_layered_arango_descent.py
```

Observed collection families:

```text
raw_infotree_roots
raw_infotree_nodes
raw_infotree_contexts
raw_infotree_payloads
raw_infotree_decl_links
raw_infotree_env_refs
raw_infotree_mctx_refs
raw_infotree_lctx_refs
raw_infotree_goal_states
raw_infotree_fvar_lineage
raw_infotree_projection_leakage
raw_infotree_*_edges
```

Use this brain when a normal declaration graph is too coarse.

### 6. Hash, WL, De Bruijn, And Expression-Fingerprint Lane

Structural redundancy and identity lane. This is navigation/audit evidence,
not proof authority.

Code surfaces:

```text
lean/DAG/ExprFingerprint.lean
tools/infra/build_chiral_patch_hashes.py
tools/infra/hash_signature.py
tools/infra/generate_structural_fibers.py
tools/observability/*
tools/alexandria/materialize_coarse_scc_overlay.py
```

Important fields and concepts observed in code:

```text
deBruijnIncidenceHash
alpha-local hash
WL duplicate graph neighborhoods
ancestry_hash
packet_hash
content_hash
source_hashes
```

Use this lane to detect wrappers, duplicate proof shapes, projection leaks,
and stale duplicated modules. Never use a hash match as a theorem proof.

### 7. LeanTrail, Critic, Vacuity, And Path-Lock Lane

Proof hygiene and theorem-honesty lane.

Code surfaces:

```text
tools/leantrail/*
scripts/leantrail_decl.py
scripts/leantrail_dedup.py
scripts/leantrail_snapshot.py
tools/infra/hive_leantrail_bee.py
scripts/vacuity-linter.py
tools/check_vacuity_policy.py
tools/infra/arango_structural_vacuity_audit.py
```

Use this lane to find fake closure, vacuity, bad sockets, stale shims, and
owner-surface drift.

### 8. SymPy, Witness, Pi, aiClaw, And Archon Orchestration

Agent execution lane. It produces suggestions, witnesses, and reports; Lean
still decides.

Code surfaces:

```text
agent-orchestrator.ts
sympy-witness.ts
lean-prover-tool.ts
chatgpt-oracle.ts
commit-conscious-knowledge.ts
tools/infra/auto_sympy_witnesses.py
tools/sympy/*
tools/infra/aiclaw_chat.py
tools/infra/socratic_clawbot.py
tools/infra/agent_orchestrator_queue.py
scripts/run_agent_orchestrator_archon.sh
```

Required persistence rule:

```text
proofs/<task-id>.lean
proofs/<task-id>.sp
artifacts/agent_orchestrator/*.json
```

## Mandatory Multi-Lane Search Before Answering

For a bounded automatic packet, use:

```bash
python3 tools/infra/context_preflight.py "your repo question" --include-external
```

Persist the packet when a session, paper node, or agent handoff will rely on it:

```bash
python3 tools/infra/context_preflight.py "your repo question" \
  --include-external \
  --json-out artifacts/context/preflight.json \
  --markdown-out artifacts/context/preflight.md
```

For any nontrivial repo question, run at least these five checks:

### 1. Repo-owned executable search

```bash
rg -n --glob '!external_refs/**' --glob '!node_modules/**' --glob '!.lake/**' \
  --glob '!.runtime/**' --glob '!artifacts/**' --glob '!reports/**' \
  'QUERY|RELATED_SYMBOL|RELATED_COMMAND' lean tools scripts src cli lakefile.lean package.json '*.ts'
```

### 2. Entrypoint search

```bash
rg -n 'script |lean_exe |def main|if __name__ == .__main__.|argparse|process.argv|Bun.argv|name:' \
  lakefile.lean package.json tools scripts src cli *.ts \
  --glob '!external_refs/**' --glob '!node_modules/**' --glob '!.runtime/**'
```

### 3. Graph/indexing lane search

```bash
rg -n 'Arango|AQL|GraphRAG|LeanSearch|loogle|infotree|decl_graph|deBruijn|debruijn|embedding|hash' \
  tools scripts src lean lakefile.lean package.json *.ts \
  --glob '!external_refs/**' --glob '!node_modules/**' --glob '!.runtime/**'
```

### 4. External context search, explicitly filtered

```bash
rg -n 'QUERY|RELATED_SYMBOL' external_refs --glob '!**/.lake/**' --glob '!**/node_modules/**'
```

Report this separately as `external-ref` evidence.

### 5. Lean owner validation

```bash
lake env lean lean/InfoGeometry/Path/Owner.lean
```

If you cannot identify an owner file, say that. Do not promote GraphRAG,
Loogle, SymPy, or Arango results into proof claims.

## Reporting Contract

Every answer about repository contents should separate:

```text
Observed in repo-owned code:
Observed in external refs:
Observed in generated/runtime artifacts:
Lean owner checked:
Open/stale/uncertain:
```

If a docstring says one thing and code says another, report the code result and
name the stale document as maintenance debt.

## Non-Negotiable Rule

Search several ways before answering:

```text
lexical rg
entrypoint scan
Lean owner scan
graph/RAG lane scan
external-ref scan when relevant
build check when making proof claims
```

This is the only safe way to operate in a repository where code moves faster
than prose.
