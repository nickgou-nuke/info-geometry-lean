# Pipeline Operator Manual — QMS-PLAN-PIPE-001

**Repository:** info-geometry-lean  
**Version:** 1.0  
**Status:** Current (consolidated operator manual)  
**Governing Policy:** [`AGENTS.md`](AGENTS.md), [`docs/RUNBOOK.md`](docs/RUNBOOK.md), [`docs/ALCHEMICAL_QMS_SOP.md`](docs/ALCHEMICAL_QMS_SOP.md), [`WARNING_DO_NOT_RUN_CACHE.md`](WARNING_DO_NOT_RUN_CACHE.md)  
**Source Review Baseline:** `214f7bcf733eaf4720913bc2c082936f2480d3fc` (Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`)  
**Lean Toolchain:** `leanprover/lean4:v4.34.1` (managed via `elan`)  
**Python:** 3.10+ with `pytest`, `psycopg`, `python-arango`

---

## Table of Contents

1. [Authority & Roles](#authority--roles)
2. [Prerequisites & Environment](#prerequisites--environment)
3. [Preflight Checks (Before Editing)](#preflight-checks-before-editing)
4. [Phase 0 — Context Preflight](#phase-0---context-preflight)
5. [Phase 1 — Lean Owner Verification (Kernel-Checked)](#phase-1---lean-owner-verification-kernel-checked)
6. [Phase 2 — Python Taxonomy Pipeline (Level 5)](#phase-2---python-taxonomy-pipeline-level-5)
7. [Phase 3 — ArangoDB → Auto-Ontology Projection (Level 5)](#phase-3---arangodb--auto-ontology-projection-level-5)
8. [Phase 4 — Cross-Layer Traceability (Level 5)](#phase-4---cross-layer-traceability-level-5)
9. [Phase 5 — Full Pipeline Runner (`run_pipeline.sh`)](#phase-5---full-pipeline-runner-run_pipeline-sh)
10. [Evidence Boundary: Level 1–2 vs Level 5](#evidence-boundary-level-1-2-vs-level-5)
11. [Build, Dependency & Cache Guardrails](#build-dependency--cache-guardrails)
12. [Completion Record & Reporting](#completion-record--reporting)
13. [Available Skills](#available-skills)
14. [Optional Services (Not Proof Authority)](#optional-services-not-proof-authority)

---

## Authority & Roles

Per [`docs/ALCHEMICAL_QMS_SOP.md`](docs/ALCHEMICAL_QMS_SOP.md) (`QMS-SOP-ALC-001` v4.1), the pipeline operates under role separation:

| QMS Role | Agent ID | Responsibility | Prohibition |
|---|---|---|---|
| **G-A (Generator)** | Lane-dependent | Implements, authors candidates, runs narrow validation | May never audit or QA-approve own work |
| **A-A (Independent Auditor)** | Independent | Audits G-A outputs, issues NCs/CAPAs | May not generate |
| **QA-A (Quality Assurance)** | Independent | Verifies CAPA closure, checks SHA-256 fingerprints, signs final disposition | May not generate or audit own work |
| **Orchestrator (Parent)** | Parent | Enforces build-lock, integrates approved candidates, checkpoints edits | Does not audit |

**Build lock discipline:** All builds and tests are serialized through `tools/build_lock.py`. Do not kill a running Lake process without explicit user authorization.

---

## Prerequisites & Environment

Before running any pipeline command:

1. **Checkout root:** `git rev-parse --show-toplevel` (work from this directory)
2. **Current commit:** `git rev-parse HEAD` (baseline: `214f7bcf733eaf4720913bc2c082936f2480d3fc`)
3. **Working tree:** `git status --short` (preserve unrelated staged work)
4. **No running Lake:** `ps -ef | rg -i "lake\|lean"` — confirm no active compiler process
5. **Toolchain:** `lean-toolchain` = `leanprover/lean4:v4.34.1`, `lake-manifest.json` Mathlib pinned — never `lake update`
6. **Python venv:** `.venv-py312` (primary), `external_refs/auto-ontology/.venv` (Auto-Ontology)

**Do not:** run `lake clean`, delete `.lake`/`.lake/build`/`.lake/packages`, change `lean-toolchain`/`lake-manifest.json`, or make dependency directories read-only.

---

## Preflight Checks (Before Editing)

Before editing any mathematical owner:

1. **Read AGENTS.md** — the root agent policy governs acceptance and changes.
2. **Inspect owner source** — record the exact claim, carrier, operations, hypotheses, imports, consumers, smallest missing implication, and adjacent claims.
3. **Read AGENTS.md acceptance rules:** no `sorry`, `admit`, custom axioms, `native_decide`, unsafe proof bypasses, or vacuous wrappers. Permitted foundational axioms: `propext`, `Classical.choice`, `Quot.sound`.
4. **Reuse existing owners** — consult `docs/CATEGORICAL_INFRASTRUCTURE_MAP.md` before introducing another bridge.
5. **Preserve unrelated work** — smallest owner-aligned change, review the diff before committing.

---

## Phase 0 — Context Preflight

The context preflight builds a bounded navigation packet before answering repository questions:

```bash
python3 tools/infra/context_preflight.py "question or target theorem" --include-external
```

**Root list:** `lean`, `tools`, `scripts`, `src`, `cli`, `extensions`, `lakefile.lean`, `package.json`, `pyproject.toml`.

**Excluded:** `external_refs/**`, `node_modules/**`, `.lake/**`, `.runtime/**`, `artifacts/**`, `reports/**`, `paper_node/**`, `quarantine/**`, `archive/**`, `**/__pycache__/**`, `**/*.pyc`.

**Usage:** Search related definitions, alternate formulations, imports, instances, theorem statements, and consumers before claiming a construction is absent or incorrect. Report a bounded search as a bounded search.

---

## Phase 1 — Lean Owner Verification (Kernel-Checked, Level 1–2)

**Authority:** Level 1–2 (Lean kernel elaboration). Only Lean kernel compilation + `#print axioms` + A-A/QA-A semantic sign-off confers mathematical proof authority.

**Target owners** (all ontology/taxonomy/phylogenesis modules):

| Module | Path |
|---|---|
| `CladisticPhylogenesisBridge` | `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean` |
| `OntologyRing` | `lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean` |
| `AnalyticOntologyTaxonomyPhylogenesisPoset` | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` |
| `AnalyticOntologyTaxonomyPhylogenesisPosetAudit` | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean` |
| `DarwinCommitTaxonomy` | `lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean` |

### Step 1.1 — Narrow locked build baseline

Run each owner **individually** (serialized, never `--all-default-targets` as a substitute for narrow owner checks):

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceSpine.CladisticPhylogenesisBridge
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.OntologyRing
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPosetAudit
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Graph.DarwinCommitTaxonomy
```

**Expected:** Exit code 0, `.trace` logs `0 errors, 0 warnings`.

### Step 1.2 — Quality gates

```bash
# Axiom index — must report only {propext, Classical.choice, Quot.sound}
python3 tools/infra/axiom_index.py --json InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset

# Vacuity linter — honesty_score 1.0, vacuity_score 0.0, no findings
python3 tools/scripts/vacuity-linter.py lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean --json

# OpenGauss screener — strict (T17 warnings on data structures without Inhabited are non-blocking text-screen warnings)
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean --strict

# Proof proxy staged gate
python3 tools/quality/proof_proxy_staged_gate.py
```

---

## Phase 2 — Python Taxonomy Pipeline (Level 5)

**Authority:** Level 5 (`[navigation_metadata]` / `[computational_witness]`). Strictly non-proof — Python weak-rule labels, Git commit phylogeny, and Arango/Postgres projections provide navigation and traceability only, never kernel-verified mathematical truth.

### Step 2.1 — Run taxonomy contract tests

```bash
python3 -m pytest tests/test_evolution_taxonomy.py tests/test_repository_phylogeny_export.py tests/test_decl_graph_generation.py tests/test_ontology_term_integrity.py tests/test_ontology_relationship_identity.py tests/test_arango_ontology_bridge.py tests/test_darwin_phylogeny_dashboard.py
```

**Expected:** All pass (live endpoint tests requiring external services are skipped).

### Step 2.2 — Cross-layer contract

The test `test_category_ids_match_lean_darwin_commit_taxonomy_contract` asserts a 12-element bijection between Lean `ChangeCategory.id` string literals (`lean/InfoGeometry/Graph/DarwinCommitTaxonomy.lean` lines 19–32, 37–49) and Python `CATEGORY_IDS` values (`tools/infra/evolution_taxonomy.py` lines 39–52).

**This is a Level 5 schema convention, not a mathematical equivalence.**

---

## Phase 3 — ArangoDB → Auto-Ontology Projection (Level 5)

**Authority:** Level 5 (Catalog Projection). Does not alter Lean proof truth.

### Step 3.1 — Offline dry-run (no credentials required)

```bash
# Declarations
python3 tools/infra/arango_to_ontology.py --dry-run --decls-jsonl <path/to/decls.jsonl> --report-json <path/to/report.json>

# Relationships
python3 tools/infra/arango_to_ontology_relationships.py --dry-run --edges-jsonl <path/to/edges.jsonl> --report-json <path/to/report.json>
```

**Expected:** Exit code 0, JSON report emitted with `status: "dry_run_ok"` and SHA-256 `source_digest`.

### Step 3.2 — Generation-pinned projection (requires live ArangoDB + PostgreSQL)

```bash
python3 tools/infra/arango_to_ontology.py \
    --arango-db infogeometry \
    --generation-id <GEN_ID> \
    --pin-generation \
    --report-json artifacts/ontology_reconciliation.json
```

**Invariants (never violate):**
- Never add unmapped tables to `public` that trigger Alembic drift — keep all generation tables in schema `ig_decl_projection`
- Never change `public.term.source` away from `'semantic'` — upstream FastAPI `:3001` and MCP `:3003` require `term.source == 'semantic'` AND `EXISTS (SELECT 1 FROM public.table__term WHERE term_id = term.id)`
- Atomic reconciliation of `public.table__term` and `public.term__term` inside a single PostgreSQL transaction

### Step 3.3 — Schema file

`tools/infra/sql/001_decl_projection.sql` defines the `ig_decl_projection` schema with immutability triggers (`reject_mutation`, `generation_transition`, `selection_guard`).

---

## Phase 4 — Cross-Layer Traceability (Level 5)

**Authority:** Level 5 (navigation/traceability). Carrier separation contract enforced.

### Step 4.1 — Phylogeny export with declaration links

```bash
python3 tools/repository_evolution/phylogeny_export.py \
    --repo <REPO_ROOT> \
    --since <SINCE_DATE> \
    --until <UNTIL_DATE> \
    --repository-url <REPO_URL> \
    --decl-edges <path/to/commit_decl_edges.jsonl> \
    --out <path/to/repo-phylogeny.json>
```

**Carrier separation (enforced):**
- Topological exporter carrier: `RankedCommitRef` / `ExportedParentLink` / `CompressedParentLink` → `nodes` and `links` in `repo-phylogeny/v2`
- Arango / Touch Graph carrier: `CommitNode` / `CommitEdge` / `CommitDeclEdge` → top-level `"declaration_links"` key
- `shared_path_not_equivalence` (Lean `DarwinCommitTaxonomy.lean:441–468`): shared-path habitat cohabitation is formally proved NOT transitive — never conflate with `exact_declaration` links

### Step 4.2 — Dashboard generation

```bash
python3 tools/infra/darwin_phylogeny_dashboard.py \
    --phylogeny-json <path/to/repo-phylogeny.json> \
    --out reports/darwin_phylogeny.html
```

**Tip tooltip renders:** per-commit `n.labels` (`category (ruleWeightPercent%)`), `n.exact`, and `n.cohabitation` split as `exact: N · habitat cohabitation (non-transitive): M`.

---

## Phase 5 — Full Pipeline Runner (`scripts/run_pipeline.sh`)

**Unified runner** for the four-stage pipeline with a SHA-256 run receipt:

```bash
./scripts/run_pipeline.sh [--skip-lean-build] [--generation-id <ID>] [--report-dir <DIR>]
```

**Stages:**
1. Narrow locked Lean build (5 ontology/taxonomy/phylogenesis owners)
2. Python taxonomy & cross-layer contract tests
3. Phylogeny export + dashboard generation (from live git log or JSON fixture)
4. ArangoDB → Auto-Ontology bridge dry-run (offline) or generation-pinned projection (with `--generation-id`)

**Output:** `run_receipt.json` with `git_head`, `git_status_clean`, per-stage exit codes, durations, and SHA-256 artifact digests.

**Example successful run:**
```json
{
  "schema": "info_geometry.pipeline_run_receipt.v1",
  "stages": {
    "lean_build": {"exit_code": 0, "duration_seconds": 4},
    "taxonomy_tests": {"exit_code": 0, "duration_seconds": 2},
    "phylogeny_export": {"exit_code": 0, "duration_seconds": 0},
    "dashboard": {"exit_code": 0, "duration_seconds": 0},
    "ontology_bridge": {"exit_code": 0, "duration_seconds": 0}
  },
  "overall_exit_code": 0
}
```

---

## Evidence Boundary: Level 1–2 vs Level 5

| Authority Level | Surface | Status | What it confers |
|---|---|---|---|
| **Level 1–2** | Lean 4.34.1 kernel elaboration, `#print axioms` (propext, Classical.choice, Quot.sound only), locked Lake builds | `[kernel_verified]` | Mathematical proof authority |
| **Level 3–4** | AGENTS.md, RUNBOOK.md, QMS SOPs, PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md | `[qms_document_controlled]` | Governance, scope, contracts, audits |
| **Level 5** | Python weak-rule labels, Git commit phylogeny, ArangoDB/PostgreSQL projections, Auto-Ontology terms | `[navigation_metadata]` / `[computational_witness]` | Navigation, observability, traceability **only** — never proof authority |

**Never conflate:** A Python weak-rule label or a Git commit phylogeny edge is **not** a Lean theorem. A fingerprint match is a candidate identifier, not proof of declaration identity.

---

## Build, Dependency & Cache Guardrails

| Rule | Detail |
|---|---|
| **Never `lake clean`** | Never delete `.lake`, `.lake/build`, or `.lake/packages` as a repair |
| **No `lake update`** | Dependency or toolchain changes require explicit user authorization |
| **Serialize builds** | Use `run_locked_lake_build.py` / `run_locked_lean.py` with shared lock (`tools/build_lock.py`) |
| **No read-only packages** | Normal builds must write generated artifacts |
| **No killing Lake** | Do not kill a running Lake process without explicit user authorization |
| **Validate narrow** | A narrow check or default-target build does not establish coverage of every tracked file |
| **Report actual scope** | A successful build certifies only the selected build surface |

---

## Completion Record & Reporting

End every pipeline execution turn with a QMS-compliant report containing:

1. **Changed Files:** Exact paths and line ranges modified (`git status --short` and `git diff --stat`)
2. **Exact Validation Commands & Results:** Narrow locked Lean build commands and exit codes; quality gate outputs; Python unit test commands and pass counts
3. **Proved or Observed Scope:** Explicit distinction between Level 1–2 `[kernel_verified]` Lean theorems (with exact carrier, hypotheses, `#print axioms`) and Level 5 `[navigation_metadata]` Python/Arango/Postgres artifacts; report narrow validation at its actual scope
4. **Role Sign-Off & Remaining Debt:** G-A → A-A → QA-A sign-off chain, SHA-256 fingerprint of controlled deliverables, any open or deferred items

---

## Available Skills

| Skill | Path | Purpose |
|---|---|---|
| Auto-Ontology Setup | `skills/auto-ontology-operations/` | Install, configure, connect, ingest, compile, prove readiness |
| Auto-Ontology Management | `skills/auto-ontology-management/` | Inspect, model, modify, publish through glossary terms, SQL attributes, semantic relationships |
| Auto-Ontology Query | `skills/auto-ontology-query/` | Call Auto-Ontology (MCP first, REST fallback), discover meaning, validate SQL/rows/answers |
| Multi-Level Ontology/Taxonomy/Phylogenesis | `skills/multilevel-ontology-taxonomy-phylogenesis/` | Ontology/taxonomy/phylogenesis lane work |
| Epistemic Compilation | `skills/epistemic-compilation/SKILL.md` | Epistemic compilation workflow |
| Socratic Oracle Proof Repair | `skills/socratic-oracle-proof-repair/SKILL.md` | Oracle-assisted proof repair |
| Darwin Commit Taxonomy | `skills/darwin-commit-taxonomy/` | Darwin commit history taxonomy |
| DAG Wire-Refactor | `skills/lean-dag-wire-refactor/SKILL.md` | DAG, namespace, forwarding-module cleanup |
| Categorical Infrastructure | `skills/categorical-infrastructure-projection/` | Categorical, tensor-tower, colimit work |
| Lean Skill Library | `skills/lean-skill-library/` | Skill catalog |

**Skill catalog registration:** Skills must have `SKILL.md`, `skill-card.md`, `evals/evals.json`, `BENCHMARK.md`, and `skill.oms.sig`. Components register in `components.d/auto-ontology.yml`.

---

## Optional Services (Not Proof Authority)

| Service | Role | Default Port | Notes |
|---|---|---|---|
| Auto-Ontology Backend | FastAPI + LangChain NL-to-SQL | 3001 | Requires `term.source == 'semantic'` |
| Auto-Ontology MCP | Read-only MCP tools | 3003 | Read-only by design; writes via Next.js `/api/...` |
| Auto-Ontology Ingestion | FastAPI ingestion worker | 3002 | — |
| Auto-Ontology Frontend | Next.js 16 web UI | 3000 | — |
| Auto-Ontology Postgres | Catalog + ontology + pgvector | 5432/5433 | Database `auto_ontology` |
| ArangoDB | Declaration graph | 8530 | Database `infogeometry` |
| Hive queue | Task queue | 8540 | Database `hive_live` |
| aiClaw memory | Proof/text memory | 8540 | Database `aiclaw_auto_rag` |
| Alexandria | Literature | 8532 | Database `alexandria` |

**Oracle outputs belong in candidate/report artifacts.** A coding agent inspects and applies source changes, then runs the relevant checks. Do not stack browser prompts or bypass the shared ChatGPT lane.

---

## Quick Reference: Common Commands

| Task | Command |
|---|---|
| Show checkout root | `git rev-parse --show-toplevel` |
| Show current commit | `git rev-parse HEAD` |
| Show working tree | `git status --short` |
| Check running Lake/Lean | `ps -ef \| rg -i "lake\|lean"` |
| Narrow locked Lean build | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock <Module>` |
| Single Lean file check | `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Path/To/File.lean` |
| Axiom index check | `python3 tools/infra/axiom_index.py --json <Module>` |
| Vacuity linter | `python3 tools/scripts/vacuity-linter.py <file.lean> --json` |
| OpenGauss screener | `python3 tools/infra/opengauss_screener.py <file.lean> --strict` |
| Context preflight | `python3 tools/infra/context_preflight.py "question" --include-external` |
| Taxonomy tests | `python3 -m pytest tests/test_evolution_taxonomy.py` |
| Full pipeline | `./scripts/run_pipeline.sh [--skip-lean-build] [--generation-id <ID>] [--report-dir <DIR>]` |
| Dry-run ontology bridge | `python3 tools/infra/arango_to_ontology.py --dry-run --decls-jsonl <file> --report-json <file>` |
| Generate pipeline receipt | `scripts/run_pipeline.sh` (emits `run_receipt.json`) |

---

**Remember:** Lean checks a proposition at its declared type. It does not establish that a physical interpretation, filename, or docstring describes that proposition faithfully. Always read the owner source and record the precise claim, carrier, operations, and conventions.