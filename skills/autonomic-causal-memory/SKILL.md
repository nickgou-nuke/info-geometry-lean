<!-- repository-context-rule -->
## Repository context rule

For repository work, the current checked-out codebase is the context. Search
existing implementation and trace actual carriers, definitions, imports,
instances, theorem statements, and uses before claiming a structure is missing
or incorrect. A local absence is not a repository-wide absence. Names,
heuristics, summaries, and documentation guide discovery but do not override
source. Follow `docs/REPO_DEEP_SEARCH_PROTOCOL.md` before repo-wide gap claims.

# SKILL: Autonomic Causal Memory Layer (ArangoDB)

## Intent

Use ArangoDB plus the current local DAG artifacts as an opt-in causal memory
and GraphRAG layer for the InfoGeometry Lean repository.  The skill compresses
a live task context into a `CausalApex` node and later reactivates nearby
files/declarations/tool runs via local DAG traversal or AQL traversal.

This is a navigation and context-recall layer only.

```text
Graph memory navigates.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

## When to Use

Use this skill when the user asks for one of:

- persistent memory / causal apex / holographic index / Arango brain;
- graph-native recall of prior repair context;
- dependency-aware navigation before editing a theorem;
- saving a verified task completion/suspension snapshot;
- building a bounded reflex arc: classify task -> preflight graph -> pick skill -> act -> verify -> write back.

Do **not** trigger arbitrary background writes. In this harness the skill is
opt-in unless a higher-level repo workflow explicitly invokes it. A bounded
preflight before theorem/repo-edit tasks is appropriate; blind memory writes are
not.

## Systemic Trigger Rules -> DAG/LeanTrail Reflex Arc

When a complex mathematical or structural prompt is received:
1. **Managed DAG health first:** if freshness matters, run `dagDoctor`; if stale,
   run `dagRefresh` through the repo/Lake script wrapper.
2. **Offline structural attention (preferred):** run `local-attention`, which
   uses the existing `leansearch_local` TF-IDF engine over local records. No
   Arango needed.
3. **DAG neighborhood hydration:** run `local-search` / `local-neighborhood`
   over `artifacts/dag/index/{decls,edges}.jsonl`.
4. **LeanTrail navigation:** use LeanTrail query/navigation when declaration
   lineage or source coordinates are needed.
5. **Projection fallback only:** run `attention-preflight` or live AQL over
   `ig_nodes` / `ig_edges` only when stale-cache recall is acceptable or the
   Arango mirror was just rebuilt from `artifacts/dag/index`.
6. **Context Injection:** lock the DAG/LeanTrail-supported nodes into the active
   context window.

> **Projection warning:** `ig_nodes` / `ig_edges` are not the developed graph
> lane. They are a retrieval projection and may be stale relative to
> `dagRefresh`, `dagDoctor`, the DAG library, and LeanTrail. For theorem work,
> prefer DAG/LeanTrail; use Arango projection attention only as a bounded cache
> lookup.

## Authority / Cache Hierarchy

Use the current local DAG artifacts first when freshness matters:

```text
artifacts/dag/index/decls.jsonl
artifacts/dag/index/edges.jsonl
```

The older live `ig_nodes` / `ig_edges` Arango lane is a cache.  It may be stale
relative to `dagRefresh`, `dagDoctor`, the DAG library, and LeanTrail.  Use it
only after verifying freshness or when stale-cache recall is acceptable.

## Tool

Primary tool:

```bash
python3 tools/infra/arango_causal_memory.py --help
```

Subcommands:

```bash
# Search the current local DAG index; no Arango freshness required.
python3 tools/infra/arango_causal_memory.py local-search AlbertCubicTripotent

# Run a DAG/LeanTrail-first preflight with artifact-status readback.
python3 tools/infra/arango_causal_memory.py local-preflight AlbertCubicTripotent --depth 1 --limit 5

# Traverse current local DAG edges around a declaration.
python3 tools/infra/arango_causal_memory.py local-neighborhood \
  InfoGeometry.OperatorAlgebra.Albert.tripotency_is_cubic_rank2_special \
  --depth 1 --limit 20

# Read-only AQL against live Arango by default.
python3 tools/infra/arango_causal_memory.py query 'RETURN 1'

# Bounded graph preflight on the compact retrieval projection only.
# Requires explicit stale-cache acknowledgement; prefer local-neighborhood.
python3 tools/infra/arango_causal_memory.py preflight \
  --use-projection-cache \
  --name InfoGeometry.OperatorAlgebra.AlbertCubicTripotent.tripotency_is_cubic_rank2_special \
  --depth 2 \
  --limit 20

# Write a purified causal-apex snapshot.
python3 tools/infra/arango_causal_memory.py commit-apex \
  --intent "theorem-safe TrialityG2 repair" \
  --files lean/InfoGeometry/Algebra/TrialityG2.lean docs/CATEGORICAL_INFRASTRUCTURE_MAP.md \
  --deps InfoGeometry.Algebra.TrialityG2.TrialityAutomorphism \
  --rules "Lean kernel is authoritative" "graph memory is navigation only" \
  --commands "lake build InfoGeometry.All" \
  --result "Build completed successfully"

# Offline structural attention over current artifacts/dag/index (no Arango needed).
python3 tools/infra/arango_causal_memory.py local-attention "Delaunay flip pentagon identity" --limit 10 --depth 1

# Text-to-vector attention over stale-prone Arango projection nodes.
# Requires explicit stale-cache acknowledgement; not the developed lane.
python3 tools/infra/arango_causal_memory.py attention-preflight \
  --use-projection-cache \
  --text-query "Pin(5,5) Krein isometry Delaunay flip" --limit 5

# Raw vector attention over stale-prone Arango projection nodes.
python3 tools/infra/arango_causal_memory.py attention-preflight \
  --use-projection-cache \
  --prompt-embedding '[0.1, -0.3, 0.5]' --limit 5
```

## Environment

The tool reuses repo Arango configuration through `tools.infra.arango_env`.
Preferred local config:

```bash
cp configs/local/hive_arango.env.example configs/local/hive_arango.env
# edit endpoint/database/user/password
```

Supported environment variables:

```text
ARANGO_ENDPOINT / ARANGO_URL
ARANGO_DB / ARANGO_DATABASE
ARANGO_USER
ARANGO_PASSWORD / ARANGO_PASS
ARANGO_DECL_COLLECTION          default: ig_nodes (projection cache only)
ARANGO_APEX_COLLECTION          default: causal_apex
ARANGO_MEMORY_EDGE_COLLECTION   default: causal_memory_edges
```

Existing declaration graph defaults:

```text
authoritative refresh lane: dagRefresh / dagDoctor / artifacts/dag/index
compact retrieval projection: ig_nodes / ig_edges
lossless fidelity target: raw_infotree_* and raw_info_*
```

Use `ig_nodes` / `ig_edges` for bounded retrieval/preflight only. They are stale
projection caches, not the developed graph lane. The underlying DAG/InfoTree and
LeanTrail lanes remain the truth surface documented in `lean/DAG/README.md` and
audited by `tools/infra/arango_fidelity_audit.py`.

For offline recall, prefer `local-search` / `local-neighborhood` / `local-attention`
over live AQL unless the Arango mirror was just rebuilt from `artifacts/dag/index`.

## External Alexandria corpus lane (separate from causal DAG memory)

Alexandria is a different Arango lane: it stores paper/chunk/entity/relation
retrieval graphs, not Lean declaration causality. It is useful for source
discovery before owner-file work, but it has the same non-authority status as
the DAG projection cache.

Live CLIs require the explicit `--arango` flag; `--input-dir` selects local
JSONL instead. Use `.venv/bin/python3` (the repo venv has `networkx` and
`python-arango`). Verified operational target:

```bash
.venv/bin/python3 tools/alexandria/retrieve_context.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Krein space fundamental symmetry Peirce decomposition" \
  --top-k 5 --hops 2 --format text

.venv/bin/python3 tools/alexandria/graph_context_rank.py \
  --arango --endpoint http://127.0.0.1:8538 --database alexandria_dag_brain \
  --query "Drazin inverse Riesz projector spectral decomposition" \
  --top-k 5 --hops 2 --format text
```

`retrieve_context.py` returns BM25-ranked chunks with `scoreBreakdown.bm25`,
lexical overlap, and DAG-neighbor context. `graph_context_rank.py` seeds from
BM25/lexical overlap and reranks with personalized PageRank over adjacency,
shared-entity, DAG, and optional De Bruijn edges. Observed at `:8538`: 5 BM25
hits (about `59.78`–`65.76`), and a 35-node/702-edge PageRank subgraph with
top graph score `0.0634`.

Defaults are `:8532` / database `alexandria`. `guard_alexandria_target`
rejects the core DAG port `:8530`, Hive port `:8540`, and the `infogeometry`,
`darwin_commits`, `hive_live`, `aiclaw_auto_rag` databases. Do not redirect
Alexandria retrieval into those lanes. Both packets declare
`authority = retrieval_context_only`; never promote a retrieved paper passage
to a Lean theorem without owner inspection and kernel checking. Details are in
`docs/DAGToolchainAndAlexandriaTrace.md`.

## Causal Snapshot Schema

A causal apex records the purified current state:

```json
{
  "type": "CausalApex",
  "schema": "info_geometry.causal_apex.v1",
  "intent": "short purified task summary",
  "files_touched": ["..."],
  "dependencies_requested": ["Lean decl names or graph keys"],
  "dependencies_resolved": ["..."],
  "dependencies_unresolved": ["..."],
  "rules": ["..."],
  "verification_commands": ["..."],
  "result": "verified result or suspension reason",
  "created_iso": "..."
}
```

Edges from `causal_apex` to existing declaration nodes are stored in
`causal_memory_edges` with:

```json
{
  "type": "DEPENDS_ON_PAST",
  "role": "causal_reactivation_dependency"
}
```

The tool does not fabricate Lean declaration vertices.  For theorem navigation,
resolve dependencies against `artifacts/dag/index` / LeanTrail first.  If a
causal-apex write also attempts projection-cache edge linking and the dependency
is not present in `ig_nodes`, it is stored as unresolved in the apex.

## Safe Query Patterns

Before editing a theorem/declaration, query its current local DAG neighborhood:

```bash
python3 tools/infra/arango_causal_memory.py local-neighborhood \
  InfoGeometry.OperatorAlgebra.Albert.tripotency_is_cubic_rank2_special \
  --depth 1 --limit 20
```

Use live AQL only after confirming the Arango mirror is fresh and accepting that
the result is projection-cache navigation:

```bash
python3 tools/infra/arango_causal_memory.py query \
  'FOR d IN ig_nodes
     FILTER d.name == @name OR d._key == @name
     FOR v,e,p IN 1..2 OUTBOUND d ig_edges
       RETURN {root: d.name, edge: e.kind, vertex: v.name, key: v._key}' \
  --bind-vars '{"name":"InfoGeometry.OperatorAlgebra.AlbertCubicTripotent.tripotency_is_cubic_rank2_special"}'
```

Recall recent causal apexes touching a file:

```bash
python3 tools/infra/arango_causal_memory.py query \
  'FOR a IN causal_apex
     FILTER @file IN a.files_touched
     SORT a.created_unix_ms DESC
     LIMIT 5
     RETURN KEEP(a, "intent", "result", "files_touched", "dependencies_resolved", "created_iso")' \
  --bind-vars '{"file":"lean/InfoGeometry/Algebra/TrialityG2.lean"}'
```

## Write Guardrails

- `query` refuses write AQL unless `--allow-write` is supplied.
- `commit-apex` writes only to causal memory collections and edges to existing
  declaration vertices.
- Never store secrets, API keys, browser tokens, or `.DEEPSEEK_API_KEY` content.
- Prefer a dedicated scoped Arango service account; do not rely on root in
  shared environments.

## Proof Policy

ArangoDB output and local DAG output are not mathematical evidence.  They may
identify candidate files, prior errors, dependency neighborhoods, and prior
verified tool runs.  Any Lean claim still requires owner-file inspection and
kernel checking.

Forbidden promotions:

- graph path ⇒ theorem proof;
- prior apex summary ⇒ proof evidence;
- vector similarity ⇒ import correctness;
- unresolved dependency name ⇒ fabricated declaration node.

## Completion/Suspension Ritual

At a clean task apex, save a compact memory only after verification commands have
actually run.  Include:

1. intent;
2. touched files;
3. key declarations/dependencies;
4. active rules/forbidden claims;
5. exact verification commands;
6. result or suspension blocker.

If verification failed, record the failure as the result instead of claiming
success.
