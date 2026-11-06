# Ontology-Layer Improvement Plan — info-geometry-lean

**Source model:** NVIDIA Auto Ontology (`https://github.com/NVIDIA/auto-ontology`)
**Target:** info-geometry-lean repo (`/home/goutev/repos/info-geometry-lean`)
**Status:** Runtime and import paths have been observed, but the declaration projection is not certified current. The 2026-11-05 row counts and endpoint checks are historical observations; see `docs/ONTOLOGY_UNIFICATION_PLAYBOOK.md` for freshness sentinels and limitations. See **Section 10** for the operational guide.

---

## 1. Executive Summary

Auto-Ontology is a Python/FastAPI framework that builds a **semantic, graph-based reasoning layer** over enterprise data. Its core loop is:

1. **Generate** — ingest source schemas → extract terms, relationships, SQL attributes → write ontology to Postgres + pgvector (with embeddings).
2. **Certify** — humans test with real questions (`check_answerable` / `ask_question`), refine terms, certify definitions.
3. **Answer** — agent classifies intent, retrieves terms/columns via embedding search, writes SQL, validates against DB, returns answer + SQL + provenance steps.

The info-geometry-lean repo already owns most of the *pieces* (ArangoDB graph store, Lean declaration DAG, GraphRAG retrieval, pipeline build→validate→ingest→verify, lane locks, staged proof gate, axiom audit, MCP servers, agent skills), but they are **fragmented** across Python tooling, Arango collections, Lean DAG artifacts, and lane infrastructure. There is **no unified ontology layer** with a clean three-kind schema (Terms / Attributes / Relationships), **no MCP-based answerability gate**, and **no portable semantic-model export**.

This plan adds an ontology layer to the repo, modeled on Auto-Ontology, so that:
- every Lean declaration is a queryable **Term** with provenance (file, line, axioms, proof status, stage),
- derived facts are **Attributes**,
- import/causal/rewrite edges are **Relationships**,
- agents can **check answerability** before attempting proofs,
- the ontology is **exportable** as a portable semantic model (Ossie-style YAML/JSON).

---

## 2. Current State Inventory

### 2.1 Auto-Ontology capabilities (the reference model)

| Capability | Description |
|------------|-------------|
| Ontology schema | Three kinds: Terms, SQL Attributes, Relationships |
| Generate stage | Ingest DB schemas → name entities → resolve relationships → write ontology (Postgres + pgvector) |
| Certify stage | Human-in-the-loop: `check_answerable` → refine → certify |
| Answer stage | Intent classification → embedding retrieval → SQL gen → validation → answer + SQL + steps |
| MCP server | `check_readiness`, `search_terms`, `get_term`, `check_answerable`, `ask_question` |
| REST API | SSE streaming, answers carry SQL + provenance steps |
| Portable export | Ossie (Apache) semantic-model YAML import/export |
| Agent skills | setup / management / query triple |

### 2.2 Repo equivalents (already present, but fragmented)

| Repo piece | Location | What it covers |
|------------|----------|----------------|
| ArangoDB graph store | `src/igf/graph/collections.py`, `indexes.py` | `ig_patch_runs`, `ig_chiral_patches`, `ig_patch_edges`, `ig_patch_members`, `ig_patch_spectral_signatures` |
| Lean decl graph | `tools/infra/decl_graph.py`, `refresh_decl_graph.py`, `dag_refresh.py`, `dag_all.py` | Declaration DAG extraction and refresh |
| GraphRAG / retrieval | `tools/infra/graph_rag_query.py`, `graphrag_context.py`, `ask_repo.py`, `arango_raw_infotree_graph.py` | Semantic graph queries |
| Pipeline | `src/igf/pipeline/orchestrator.py` (build → validate → ingest → verify) | Offline pipeline stages |
| Lane locks | `tools/infra/run_locked_lean.py`, `run_locked_lake_build.py` | Serialized Lean builds |
| Staged proof gate | `tools/quality/proof_proxy_staged_gate.py` | Pre-push gate |
| Axiom audit | `tools/infra/opengauss_cli.py`, `opengauss_screener.py`, `axiom_audit.py` | Gate 0–4 kernel + axiom certification |
| MCP servers | `.mcp.json` (`archon-lean-lsp`, `codex`) | Two MCP servers only |
| Agent skills | `skills/` (61+) | Lean/proof skills, no ontology-operation skills |
| Hive queue | `tools/infra/hive_*.py` | ArangoDB packet worker queue |
| Provenance | `docs/CHAT_ARCHETYPE_RECOVERY_LEDGER.md`, `tools/infra/commit-conscious-knowledge.ts` | Ad-hoc ledgers |

### 2.3 Gaps (what Auto-Ontology has that the repo lacks)

| Auto-Ontology capability | Repo gap |
|--------------------------|----------|
| Unified ontology schema (Terms / Attributes / Relationships) | No single schema; patch/chiral collections are pipeline-internal, not a queryable ontology |
| Human-in-the-loop certify (`check_answerable` → refine → certify) | Automated gates only (OpenGauss screener, staged proof gate); no human certification workflow |
| MCP answerability + term-search tools | `.mcp.json` has only `archon-lean-lsp` + `codex`; no `check_answerable` / `search_terms` / `ask_question` |
| REST API with SSE + SQL + steps | No REST API surface over the declaration/ontology graph |
| Portable semantic-model export (Ossie YAML) | Ad-hoc JSON exports (`ast_graph.json`, `commit_decl_edges.jsonl`, `proof_graph.json`); no standardized format |
| Embeddings-backed term retrieval into answerability loop | Vector search exists in pieces (`leansearch_local.py`, Arango indexes) but not wired into a pre-flight answerability gate |
| Agent skills for ontology operation | Skills exist for Lean/proof tasks; none for ontology setup/management/query |

---

## 3. Target Architecture

```
                    +---------------------+
                    |  info-geometry-lean |
                    |  (Lean owner files) |
                    +----------+----------+
                               |
        +----------------------v----------------------+
        |         Ontology Layer (NEW)                |
        |  ---------------------------------------    |
        |  Terms          | Lean declarations:      |
        |                 | FQN, docstring, file,   |
        |                 | line, axioms, stage,    |
        |                 | proof status, embedding |
        |  Attributes     | Derived facts /         |
        |                 | corollaries / specializations |
        |  Relationships  | Import, causalEdge      |
        |                 | (MCP poset), axiom dep, |
        |                 | rewrite/usage edges     |
        +----------------------+----------------------+
                               |
        +----------------------v----------------------+
        |  MCP Server (NEW)                           |
        |  check_readiness, search_terms,             |
        |  get_term, check_answerable, ask_question   |
        +----------------------+----------------------+
                               |
        +----------------------v----------------------+
        |  Lane Pipeline (existing)                   |
        |  run_locked_lean → proof gate → axiom audit |
        +---------------------------------------------+
```

### 3.1 Three-kind ontology schema (ArangoDB)

| Kind | Represents | Key fields |
|------|-----------|------------|
| **Term** | Lean declaration (def/theorem) | `fqn`, `kind` (def/theorem/structure/inductive), `module`, `file`, `line`, `docstring`, `stage` (MCP₁–MCP₁₀), `axioms` (list), `proof_status` (proved/conditional/socket/debt), `embedding` (vector) |
| **Attribute** | Derived fact / corollary / specialization | `source_term` (→ Term), `statement`, `derivation_path`, `proof_status` |
| **Relationship** | Edge between Terms | `from` (→ Term), `to` (→ Term), `type` (import / causalEdge / axiomDep / rewrite / use), `weight` |

### 3.2 MCP server tools (modeled on Auto-Ontology)

| Tool | Purpose |
|------|---------|
| `check_readiness` | Build lock free, dependencies present, ontology populated |
| `search_terms` | Semantic search over Lean declarations (name / docstring / embedding) |
| `get_term` | Declaration details: file, line, axioms, proof status, dependencies, stage |
| `check_answerable` | Does the ontology cover the terms/relationships needed for a proposed theorem? Returns coverage score + missing terms |
| `ask_question` | Returns a Lean proof sketch + declaration DAG path + verification result |

### 3.3 Ontology-backed answerability gate (pre-flight)

Before `run_locked_lean.py` launches a Lean elaboration, the lane pipeline queries the ontology:
- Parse the target theorem statement for symbol references.
- Look up each symbol in the ontology.
- If coverage < threshold (e.g. 0.8), abort with "not answerable: missing terms X, Y" instead of producing a vacuous proof.

This elevates existing vacuity audits (`find_vacuous.py`, `structural_vacuity_linter.py`, `audit_conductive_wires_vacuous_nodes.py`) from post-hoc audits to **pre-flight gates**.

### 3.4 Portable export (Ossie-style)

`tools/infra/export_ontology.py` reads `ast_graph.json` + `commit_decl_edges.jsonl` + MCP stage definitions and emits Ossie-compatible YAML/JSON containing Terms, Attributes, Relationships — importable by other Lean projects or agent contexts.

---

## 4. Implementation Plan

### Phase 1 — Ontology schema + population (lowest effort, highest leverage)

**Owner:** `src/igf/graph/ontology.py` (new), extending `arango_client.py` / `collections.py` / `indexes.py`

Tasks:
1. Define `VERTEX_COLLECTIONS` addition: `ig_ontology_terms`, `ig_ontology_attributes`, `ig_ontology_relationships`.
2. Define `EDGE_COLLECTIONS` addition: `ig_ontology_term_attribute`, `ig_ontology_term_relationship`.
3. Add indexes for `fqn`, `module`, `stage`, `proof_status`, `embedding`.
4. Write `ontology.py` with:
   - `populate_from_decl_graph(decl_graph_path)` — imports Terms from Lean DAG output.
   - `populate_from_mcp_stages()` — imports Relationships from `causalEdge` / MCP₁–MCP₁₀ poset.
   - `populate_attributes()` — imports derived facts (corollaries/specializations).
   - `search_terms(query, limit)` — semantic + lexical search.
   - `check_answerable(symbols)` — coverage report.
5. Wire into `src/igf/pipeline/orchestrator.py` as an optional `do_ontology` stage.

**Deliverable:** `src/igf/graph/ontology.py` + updated `collections.py`/`indexes.py` + pipeline integration.

### Phase 2 — MCP server (immediate value for agents)

**Owner:** New `tools/infra/mcp/ontology_mcp.py` (or extend `.mcp.json`)

Tasks:
1. Create MCP server `info-geometry-ontology` with the five tools above.
2. Backend: `leansearch_local.py` + `graph_rag_query.py` + new `ontology.py`.
3. Add to `.mcp.json`.
4. Test: `search_terms "gramian"` returns `gramianOut`/`gramianIn` with file/line/stage; `check_answerable` on a proposed theorem returns coverage.

**Deliverable:** MCP server + `.mcp.json` entry + smoke test.

### Phase 3 — Answerability gate in lane pipeline

**Owner:** `tools/infra/run_locked_lean.py` wrapper + `tools/infra/lanes/`

Tasks:
1. Add `--check-answerable` flag (or env var) to `run_locked_lean.py`.
2. Before elaboration, extract symbols from target file/statement; query ontology; abort if coverage < threshold.
3. Log coverage report to build artifacts.
4. Integrate into `tools/infra/run_locked_lake_build.py --changed` path for changed owners.

**Deliverable:** Pre-flight answerability gate; zero vacuous proofs launched.

### Phase 4 — Portable export (Ossie-style)

**Owner:** `tools/infra/export_ontology.py` (new)

Tasks:
1. Read `ast_graph.json`, `commit_decl_edges.jsonl`, MCP stage definitions.
2. Emit Ossie-compatible YAML/JSON: Terms, Attributes, Relationships.
3. CLI: `python tools/infra/export_ontology.py --out ontology.yaml`.
4. Round-trip test: export → import into a fresh ArangoDB instance.

**Deliverable:** Export tool + sample `ontology.yaml` for the PeirceSpine lane (MCP₁–MCP₁₀).

### Phase 5 — Agent skills (ontology operation triple)

**Owner:** `skills/lean-ontology-{setup,management,query}/`

Tasks (modeled on Auto-Ontology's skill triple):
1. `lean-ontology-setup` — initialize ontology graph from a Lean checkout (run Phase 1 population).
2. `lean-ontology-management` — inspect, certify, import/export ontology definitions (Phase 4 tool).
3. `lean-ontology-query` — ask questions over the ontology, validate Lean proof paths (MCP client + `ask_question`).

**Deliverable:** Three skill directories under `skills/` with SKILL.md + tooling.

---

## 5. Priority Order

| Priority | Item | Effort | Value |
|----------|------|--------|-------|
| P0 | Phase 1: Ontology schema + population | Medium | Foundation for everything else |
| P0 | Phase 2: MCP server | Medium | Immediate agent value; unblocks safe editing |
| P1 | Phase 3: Answerability gate | Medium | Prevents vacuous proofs; elevates existing audits |
| P1 | Phase 4: Portable export | Low-Medium | Shareable semantic model; peer review |
| P2 | Phase 5: Agent skills | Medium | Teaches agents to use the new layer |

---

## 6. Relation to Current Blocked Work

The staged canonical archetype file:

`lean/InfoGeometry/OperatorAlgebra/PeirceSpine/MetriplecticCausalArchetypesCanonical.lean`

- 748 lines, 22 defs, 32 theorems, **zero** `sorry`/`admit`/`native_decide`/`axiom`.
- Elaborates cleanly when `MetriplecticCausalPlabicKreinYangianPoset.lean` builds.
- **Blocked** because the concurrent agent modified the companion owner (178 insertions), breaking its build — my file's MCP₁₀ depends on `causalEdge` / `mcp_poset_chain_and_irreflexivity` from that owner.

**How the ontology layer helps:** Once implemented, the MCP₁–MCP₁₀ causal poset lives as **Relationships** in the ontology, the 32 theorems as **Terms**, and derived facts (`conjTransposeMulReverse`, `starCutSum`) as **Attributes**. Agents can `check_answerable` before touching the file, and the MCP₁–MCP₁₀ poset is exportable as a portable semantic model independent of the companion owner's build state.

---

## 7. Definition of Done (per phase)

- Phase 1: `python -m igf.pipeline.orchestrator --do-ontology` populates Arango with Terms/Attributes/Relationships from the current Lean checkout; `search_terms` returns correct FQNs.
- Phase 2: MCP server responds to all five tools; `.mcp.json` lists `info-geometry-ontology`.
- Phase 3: `run_locked_lean.py --check-answerable` aborts on missing symbols with a coverage report; no vacuous proof launched.
- Phase 4: `export_ontology.py` emits Ossie-compatible YAML; round-trip import succeeds.
- Phase 5: Three skills exist under `skills/`; each has SKILL.md and can be invoked by an agent.

---

## 8. Files to Create / Modify

### Create
- `src/igf/graph/ontology.py`
- `tools/infra/mcp/ontology_mcp.py` (or `tools/infra/ontology_mcp.py`)
- `tools/infra/export_ontology.py`
- `skills/lean-ontology-setup/SKILL.md` + tooling
- `skills/lean-ontology-management/SKILL.md` + tooling
- `skills/lean-ontology-query/SKILL.md` + tooling

### Modify
- `src/igf/graph/collections.py` — add ontology collections
- `src/igf/graph/indexes.py` — add ontology indexes
- `src/igf/pipeline/orchestrator.py` — add `do_ontology` stage
- `tools/infra/run_locked_lean.py` — add `--check-answerable` flag
- `.mcp.json` — add `info-geometry-ontology` server

---

## 9. Open Questions

1. Should the ontology store Lean-level proof terms (full AST) or just declaration metadata? Recommendation: metadata only (Terms/Attributes/Relationships); full AST stays in `.olean` / Lean DAG.
2. Embedding model for term search — reuse `leansearch_local.py`'s existing index or add pgvector to Arango? Recommendation: reuse existing `leansearch_local.py` to avoid new infra.
3. Who certifies terms in the "Certify" stage? Recommendation: the staged proof gate + human review via PR; ontology records `proof_status` and `certified_by`/`certified_at`.

---

## 10. Live Deployment, Ingestion Bridges & Agent Usage Guide (Verified 2026-11-04)

The ontology layer is deployed and populated from the `infogeometry` ArangoDB
declaration graph (`http://127.0.0.1:8530`) into Auto Ontology's Postgres store
(`localhost:5433`, database `auto_ontology`).

### 10.1 Deployed Service Topology

| Component | Endpoint / Location | Role |
|---|---|---|
| **ArangoDB Declaration Graph** | `http://127.0.0.1:8530` (db `infogeometry`) | Source `decls` (`306,503` declarations) and `edges` (`2,085,736` compiler edges) with `lean-expr-structural-v3` AST/value/shape hashes |
| **Auto Ontology Postgres Store** | `localhost:5433` (db `auto_ontology`) | Stores `catalog_database` (`dialect="lean"`), `catalog_schema` (`name="lean"`), `catalog_table` (`table_type="lean_module"`), `term` (`306,503` rows), `table__term`, and `term__term` |
| **Term Ingestion Bridge** | `tools/infra/arango_to_ontology.py` | Bulk-upserts ArangoDB `decls` into `catalog_table` (one per Lean module), `term` (`name`, `description` + `Source: <relFile>:<line>`, `synonyms=[kind]`, `imported_id=_key`), and `table__term` via `psycopg` `COPY` |
| **Relationship Ingestion Bridge** | `tools/infra/arango_to_ontology_relationships.py` | Bulk-upserts ArangoDB `edges` (`src`, `dst`, `kind`: `"type"` or `"value"`) into `term__term` (`src_term_id`, `dst_term_id`, `kind`) via `psycopg` `COPY` |
| **Auto Ontology FastAPI REST** | `http://localhost:3001` | Local read-only REST API for querying terms (`/api/terms`), term details (`/api/terms/{term_id}`), Lean→Lean dependency edges (`/api/terms/relationships`), module details (`/api/exploration/tables/{table_id}/details`), and entity coverage (`/api/question-entity-coverage`) |
| **Auto Ontology Web UI** | `http://localhost:3000` | Next.js frontend and OAuth authorization server (`/.well-known/oauth-authorization-server`) |
| **Auto Ontology MCP Server** | `http://localhost:3003/mcp` | Configured in `.mcp.json` under `"nvidia-auto-ontology"`. Exposes `check_readiness`, `search_terms`, `get_term`, `get_term_columns`, `get_term_sql_attributes`, `get_sql_attribute`, `describe_table`, `check_answerable`, and `ask_question` (`external_refs/auto-ontology/mcp/auto_ontology_mcp/tools.py`). Requires OAuth sign-in (`401` without a bearer token by design) |
| **Reference Skills** | `external_refs/auto-ontology/skills/nvidia-ontology-{setup,management,query}/SKILL.md` | Upstream skill specifications for setup, modeling/management, and grounded querying |

### 10.2 Populating / Refreshing the Ontology from ArangoDB

Use the exact completed generation ID printed by `refresh_decl_graph.py
--stream` for both bridges. Legacy/custom collections require explicit
`--decl-collection` and, for the relationship bridge, `--edge-collection`.
An immutable refresh does not update legacy collections. The bridges upsert/add
rows; they do not remove terms or relationships left by earlier generations.

```bash
# 1. Load ArangoDB and Auto Ontology Postgres environment variables
source configs/local/hive_arango.env
export POSTGRES_HOST=localhost POSTGRES_PORT=5433 POSTGRES_DATABASE=auto_ontology

# 2. Select the completed generation printed by refresh_decl_graph.py
export GENERATION_ID='<completed-decl-graph-generation-id>'

# 3. Ingest/update that generation's declarations
python3 tools/infra/arango_to_ontology.py \
  --arango-db infogeometry --generation-id "$GENERATION_ID" --legacy-additive --batch-size 5000 --limit 0

# 4. Ingest the matching dependency edges from the same generation
python3 tools/infra/arango_to_ontology_relationships.py \
  --arango-db infogeometry --generation-id "$GENERATION_ID" --legacy-additive --batch-size 5000 --limit 0
```

### 10.3 Verified Read-Only REST Queries (`http://localhost:3001`)

When running in CLI/scripted workflows (or before completing interactive MCP OAuth
sign-in on port `3003`), agents can query the ontology directly over HTTP on
port `3001`:

```bash
# 1. Search terms by concept or declaration substring (returns id, term, docstring, kind synonyms, source_doc_id, related_counts)
curl -s "http://localhost:3001/api/terms?query=Krein&limit=5"

# 2. Verify total indexed declarations in the InfoGeometry namespace (total: 306503)
curl -s "http://localhost:3001/api/terms?query=InfoGeometry&limit=1"

# 3. Disambiguate candidate owners for an overloaded declaration name
curl -s "http://localhost:3001/api/terms?query=normalizedTraceLimit&limit=5"

# 4. Inspect full term record + owning Lean module (catalog_table) by term UUID
curl -s "http://localhost:3001/api/terms/52944066-9f38-4b7b-b333-a767ee4b0212"

# 5. Inspect incoming Lean->Lean dependency edges (declarations whose type/value depends on dst)
curl -s "http://localhost:3001/api/terms/relationships?dst=InfoGeometry.Algebra.Clifford.IsKreinInvolution&limit=5"

# 6. Inspect outgoing Lean->Lean dependency edges (prerequisites used by src)
curl -s "http://localhost:3001/api/terms/relationships?src=InfoGeometry.Clifford.Cl11JordanWignerCARBridge.jwAnnihilation_creation_anticommutator&limit=5"

# 7. Inspect all declarations belonging to a Lean module (by catalog_table UUID from step 4)
curl -s "http://localhost:3001/api/exploration/tables/235122a8-a055-4ac0-a7d5-9bb61fc834ff/details"
```

### 10.4 How Agents Combine Auto Ontology (`:3001` / `:3003`) with ArangoDB AST/AQL Hashes (`:8530`)

1. **Semantic & Lexical Discovery (`http://localhost:3001` or MCP `search_terms` / `get_term`)**:
   Locate existing Lean declarations by mathematical keyword or symbol name,
   read their docstrings and `Source: lean/InfoGeometry/...:line` pointers, and
   disambiguate overloaded names across namespaces (e.g.,
   `InfoGeometry.Canonical.Cl11CARPeirceMassCoercivityBridge.normalizedTraceLimit`
   vs. `InfoGeometry.Canonical.Cl11CuntzCoherentIndexTopologicalBridge.normalizedTraceLimit`).
2. **Immediate Dependency Inspection (`/api/terms/relationships`)**:
   Query `src=<fqn>` to see what a theorem uses (`kind: "type"` vs. `"value"`)
   and `dst=<fqn>` to see which downstream theorems and canonical bridges consume it.
3. **AST/AQL Fingerprint & Multi-Cone Cross-Section (`http://127.0.0.1:8530`)**:
   Pass discovered FQNs into `tools/infra/arango_causal_memory.py query`,
   `tools/infra/arango_causal_chiral_cone_prompt.py`, or
   `tools/infra/astaql_concept_bridge.py` (`docs/ASTAQLHASH-HOWTO.md`) to compare
   `canonicalTypeHash`, `canonicalValueHash`, and `dagShapeHash`
   (`algorithmVersion == "lean-expr-structural-v3"`) and find shared multi-hop
   prerequisites (`shared_nodes`).
4. **Lean Owner Inspection & Kernel Certification**:
   Ontology terms, relationship edges, and AST hashes are **navigation
   evidence**, never proof authority. Always read the resolved Lean owner file
   and certify changes via `run_locked_lean.py`, `run_locked_lake_build.py`, and
   `opengauss_cli.py certify --verify-kernel`.

### 10.5 Automated Service Launcher, Local vLLM Forwarding (`http://127.0.0.1:58051/v1`), & Agent Skills

To ensure all Auto Ontology services and the local vLLM reasoning endpoint
(`http://127.0.0.1:58051/v1` forwarding to `127.0.0.1:18765/v1`, serving
`nvidia/Qwen3.8-27B-NVFP4`) remain active across sessions without being
shadowed by empty `:5432` Docker compose containers, use:

```bash
bash tools/infra/start_auto_ontology_services.sh
```

See the dedicated agent skills:
- `skills/auto-ontology-operations/SKILL.md` — service topology, port de-confliction, REST/MCP queries, and ArangoDB-to-Postgres refresh commands.
- `skills/multilevel-ontology-taxonomy-phylogenesis/SKILL.md` — formalization rules and literature synthesis for Multi-Level Ontology (`MLT` / clabjects / powertypes), Taxonomic Subsumption (`projectorSubspace`, `cladeSubsumes`), and Phylogenetic Cladistics (`cladeFork`, `cladeJoin`, `phyloLineage`, `blastRadiusEdge`).

---

## 11. Recommended Multi-Level Ontology Topology (Views, Not One Global DAG)

The five-level arrangement below is a **navigation and synthesis view** over
selected owner modules. It is not a claim that all repository knowledge forms
one acyclic graph, that every listed module has a direct dependency on the
previous tier, or that the architecture is mathematically optimal. Verify
every edge from Lean imports and declaration dependencies before treating it
as a proof-dependency edge.

Use one typed, provenance-bearing graph model with distinct projections:

1. **Carrier and declaration layer:** Lean declarations, modules, universes,
   carriers, hypotheses, and source locations. Lean source and the kernel stay
   authoritative.
2. **Dependency layer:** directed `type` and `value` references, with the
   acyclic order defined only by actual declaration dependencies.
3. **Mathematical relation layer:** typed `proof`, `equivalence`,
   `representation`, `analogy`, and `conjectural_bridge` relations. These may
   form cycles and are not included in dependency topological sorting.
4. **Taxonomy and phylogeny layer:** subsumption/containment relations and
   source-version/commit lineage, respectively. Keep version events and
   semantic inheritance distinct from theorem dependencies.
5. **Evidence and synthesis layer:** InfoTree/elaboration events, validation
   records, and synthesis declarations linked to their source owners and
   evidence. These are trace/provenance relations, not mathematical proof
   edges unless Lean declarations actually depend on one another.

Selected modules such as `PeirceSpine.Basic`, `OntologyRing`,
`ArchetypeFormalization`, the matrix realization owners,
`JungianEpistemicCompiler`, and `CoagulatedArchetypeSynthesis` can be presented
as a layered overview. Their names, docstrings, and inclusion in a synthesis
do not establish a global five-tier causal order. Promote an edge only after
checking the actual declaration type, dependency, or explicit map and theorem.

The current storage path is also a **projection pipeline**, not yet a single
canonical database: Arango holds declaration graph records, local DAG artifacts
are snapshots, and Auto-Ontology/Postgres is a searchable projection. The
relationship importer currently inserts absent rows but does not remove stale
ones, so a successful import is not by itself a replacement refresh. Record
source revision, generation time, and per-owner freshness sentinels before
using that projection as a current repository view.

**End of design section.** The unification playbook defines relation semantics
and evidence requirements; this plan describes the Auto-Ontology integration
and its current limitations.
