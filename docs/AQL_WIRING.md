# AQL DAG Pipeline — Wiring the Toolchain into This Repo

## Reference workflow compared

The GEPA / Lean AST -> ArangoDB reference implementation compared for this
port lives in the auto companion tree:

- **`/home/goutev/auto/proofs/tools/lean_graph/README.md`** — the three-layer extraction spec (syntax dump via `DumpLeanGraph.lean`, environment deps via `ExtractGraph.lean`, bridge via `join_syntax_env.py`, Arango import via `import_arango.py`).
- **`/home/goutev/auto/proofs/scripts/aql_queries.md`** — the AQL query arsenal: dependency trees, socket scans, syntax/env bridge coverage, `sorry` scan, tactic audit, KMS inspection.
- **`~/.config/arango/env.sh`** — Arango connection config (endpoint, database, username/password).

Those documents explain the source workflow that was compared. For this
repository, the authoritative commands are the `tools/leantrail/*` and Lake
script entry points documented below.

---

## What we replicated and where

| Original (auto/) | This repo | Notes |
|:---|:---|:---|
| `tools/lean_graph/DumpLeanGraph.lean` | `tools/leantrail/DumpLeanGraph.lean` | Lean-native syntax AST JSONL dump with source ranges. |
| `tools/lean_graph/check_dump_shape.py` | `tools/leantrail/check_dump_shape.py` | Validates the syntax JSONL shape before ingest. |
| `tools/lean_graph/ingest_syntax_to_arango.py` | `tools/leantrail/ingest_syntax_to_arango.py` | Syntax-only Arango ingest with `--execute-http`, no `python-arango` requirement. |
| `scripts/extract_lean_ast_all.py` | `tools/leantrail/ast_extract.py` | Regex-based AST -> JSON node-edge graph. Added JSONL mode, line numbers, namespace extraction. |
| `scripts/index-external-repos.py` | `tools/leantrail/external_index.py` | External RAG indexer. Added structural chunking at Lean declaration boundaries, SHA1 dedup. |
| `scripts/ask_oracle_lemmas.py` + `fix_lean_with_oracle.py` | `tools/leantrail/oracle_search.py` | Unified LLM oracle: `--ask`, `--fix`, `--search`, `--translate`. Added local codebase/mathlib grep before remote call. |
| `ui/dump_graph.py` | `tools/leantrail/arango_dump.py` | ArangoDB → JSON graph dump. Added AQL causal cones (`--cone-downstream`, `--cone-upstream`, `--cone-multi`). |
| `/tmp/aql_query.py` (ad-hoc) | `tools/leantrail/aql_query.py` plus `HttpArangoDB` in `arango_dump.py` | Dependency-light `_api/cursor` HTTP runner and dump/cone fallback. No `python-arango` dependency needed for AQL inspection. |
| *new* | `tools/leantrail/aql_schema.py` | AQL query catalog (14 query patterns) + Python-native `TopologyAnalyzer` that runs the same queries on JSON without ArangoDB. |
| `scripts/gepa_optimize.py` | `tools/leantrail/ast_aql_optimize.py` | Repo-local GEPA AST/AQL optimization: persistent AST indexes plus bounded query smoke tests. |
| `tools/lean_graph/aql_smoke_test.sh` | `tools/leantrail/aql_smoke_test.sh` and `tools/leantrail/smoke_test.py` | Live syntax graph smoke plus full current-repo LeanTrail smoke. |

## How to run the full pipeline (in this repo)

### Step 0 — Lean-native syntax dump and syntax-only ingest

```bash
lake script run leantrailSyntaxDump lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean \
  > /tmp/cuntz_lorentz_syntax.jsonl

lake script run leantrailCheckDumpShape --expect-keyword theorem \
  < /tmp/cuntz_lorentz_syntax.jsonl

tools/infra/with_arango_env.sh -- lake script run leantrailSyntaxIngest \
  /tmp/cuntz_lorentz_syntax.jsonl --execute-http

tools/infra/with_arango_env.sh -- lake script run leantrailAQLSmoke
```

### Step 1 — Extract the AST graph

```bash
lake script run leantrailAstExtract \
  --root lean/ \
  --out artifacts/leantrail/lean_ast_graph.json \
  --jsonl   # also writes nodes.jsonl + edges.jsonl for ArangoDB
```

This is the lightweight version. It uses regex on source text — fast (3500 files in ~30s), but edges are token-co-occurrence, not compiler-verified.

### Step 2 — (Optional) Build the compiler-verified leantrail snapshot

The proper dependency graph comes from the Lean compiler via `leantrail/backend/extractor.py` → `run_refresh_pipeline`. This is slow (full `lake build`) but produces `depends_type` and `depends_value` edges with mathlib references. The existing snapshot is at:

```
artifacts/leantrail/graph_snapshot.json    (467 MB, 101K nodes, 825K edges)
```

It currently has `"scope": "partial"` (InfoGeometry modules only). To include DAG modules, rebuild with wider scope.

### Step 3 — Ingest into ArangoDB (if running)

```bash
# Using the leantrail arango_ingest.py
lake script run leantrailArangoIngest \
  --input-dir artifacts/leantrail/arango/ \
  --nodes-collection ig_nodes \
  --edges-collection ig_edges

# Or using arango_dump.py to query
lake script run leantrailArangoDump \
  --database LeanAST \
  --cone-downstream "DAG.LaplacianRank::laplacian_rank_eq_add_rank" \
  --max-depth 5
```

If `python-arango` is not installed, `arango_dump.py` falls back to raw HTTP `_api/cursor` POST with Basic auth — no extra dependency needed. Connection config is read from the environment:

```bash
export ARANGO_ENDPOINT="http://localhost:8529"
export ARANGO_DATABASE="LeanAST"
export ARANGO_USERNAME="root"
export ARANGO_ROOT_PASSWORD=""
```

### Step 4 — Run topology analysis (no ArangoDB needed)

```bash
tools/infra/with_arango_env.sh -- lake script run leantrailAQLQuery <<'AQL'
RETURN {
  syntax_decls: LENGTH(FOR x IN syntax_decls RETURN 1),
  syntax_nodes: LENGTH(FOR x IN syntax_nodes RETURN 1),
  ast_child: LENGTH(FOR x IN ast_child RETURN 1),
  decl_root: LENGTH(FOR x IN decl_root RETURN 1)
}
AQL
```

For optimized AST scans:

```bash
tools/infra/with_arango_env.sh -- lake script run leantrailAstAQLOptimize --depth 5
```

```bash
# On the lightweight AST graph
lake script run leantrailAQLSchema \
  --graph artifacts/leantrail/lean_ast_graph.json \
  --closure --frontier --blast-radius

# Or on the compiler-verified leantrail snapshot
lake script run leantrailAQLSchema \
  --graph artifacts/leantrail/graph_snapshot.json \
  --closure
```

The `TopologyAnalyzer` auto-detects the format (leantrail `src`/`dst` vs AST `source`/`target`).

### Step 5 — Search for proofs to close gaps

```bash
# Semantic search (local codebase + mathlib grep first, then LLM)
lake script run leantrailOracleSearch \
  --search "rank of laplacian equals sum of ranks boundary operators"

# Generate lemmas
lake script run leantrailOracleSearch \
  --ask "Prove rank(AA^T + B^TB) = rank(A) + rank(B) given B*A=0" \
  --compile

# Fix a broken file
lake script run leantrailOracleSearch \
  --fix lean/DAG/GaussianElimination.lean --in-place --compile
```

## Key AQL queries (run in ArangoDB web UI or via arango_dump.py)

These are the most-used queries from the auto/ arsenal, adapted to the `ig_nodes`/`ig_edges` collection names used in this repo:

```aql
-- 1. Causal cone downstream (what does X depend on?)
FOR v, e, p IN 1..5 OUTBOUND "DAG.LaplacianRank::laplacian_rank_eq_add_rank" @@edges
  OPTIONS {uniqueVertices: "global", bfs: true}
  RETURN {node: v.name, depth: LENGTH(p.edges)}

-- 2. Blast radius (what depends on X?)
FOR v IN 1..99 INBOUND "some_sorried_node" @@edges
  RETURN DISTINCT v.name

-- 3. Missing bridges (disconnected SCCs with shared tokens)
-- See aql_schema.py for the full AQL

-- 4. Theory closure score
LET clean = LENGTH(FOR n IN @@nodes FILTER n.role IN ["pure_conductor","owner","translator"] RETURN n)
LET total = LENGTH(FOR n IN @@nodes FILTER n.kind != "Axiom" RETURN n)
RETURN {pct_clean: clean * 100 / total}
```

The full AQL catalog (14 query patterns) is in `tools/leantrail/aql_schema.py` class `AQLQueries`.

## Current state

| Component | Status |
|:---|:---|
| AST extractor (regex) | ✓ working — current full repo: 51,227 nodes, 526,231 capped token-reference edges |
| Leantrail snapshot (compiler) | ✓ InfoGeometry only, 101K nodes, 825K edges, 98.1% clean |
| ArangoDB ingest | ✓ `arango_ingest.py` + `arango_dump.py` (with HTTP fallback) |
| AQL causal cones | ✓ downstream, upstream, multi-apex |
| Dependency-light AQL runner | ✓ `tools/leantrail/aql_query.py`, callable through `lake script run leantrailAQLQuery` |
| GEPA AST AQL optimization | ✓ `tools/leantrail/ast_aql_optimize.py`, current live syntax graph indexed/smoked |
| TopologyAnalyzer (Python-native) | ✓ closure score, blast radius, missing bridges |
| LLM oracle | ✓ ask/fix/search/translate with local grep grounding |
| DAG modules in leantrail snapshot | ✗ pending — rebuild snapshot with wider scope |
