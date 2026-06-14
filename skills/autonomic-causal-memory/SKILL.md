# SKILL: Autonomic Causal Memory Layer (ArangoDB)

## Intent

Use ArangoDB as an opt-in causal memory and GraphRAG layer for the
InfoGeometry Lean repository.  The skill compresses a live task context into a
`CausalApex` node and later reactivates nearby files/declarations/tool runs via
AQL traversal.

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
- saving a verified task completion/suspension snapshot.

Do **not** trigger it automatically in the background.  In this harness the
agent acts only when prompted; this skill is opt-in unless a higher-level repo
workflow explicitly invokes it.

## Tool

Primary tool:

```bash
python3 tools/infra/arango_causal_memory.py --help
```

Subcommands:

```bash
# Read-only AQL by default.
python3 tools/infra/arango_causal_memory.py query 'RETURN 1'

# Write a purified causal-apex snapshot.
python3 tools/infra/arango_causal_memory.py commit-apex \
  --intent "theorem-safe TrialityG2 repair" \
  --files lean/InfoGeometry/Algebra/TrialityG2.lean docs/CATEGORICAL_INFRASTRUCTURE_MAP.md \
  --deps InfoGeometry.Algebra.TrialityG2.TrialityAutomorphism \
  --rules "Lean kernel is authoritative" "graph memory is navigation only" \
  --commands "lake build InfoGeometry.All" \
  --result "Build completed successfully"
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
ARANGO_DECL_COLLECTION          default: ig_nodes
ARANGO_APEX_COLLECTION          default: causal_apex
ARANGO_MEMORY_EDGE_COLLECTION   default: causal_memory_edges
```

Existing declaration graph defaults:

```text
vertex collection: ig_nodes
edge collection:   ig_edges
```

These come from the DAG/ExprArango pipeline documented in `lean/DAG/README.md`.

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

The tool does not fabricate Lean declaration vertices.  If a requested
dependency is not present in `ig_nodes`, it is stored as unresolved in the apex.

## Safe Query Patterns

Before editing a theorem/declaration, query its graph neighborhood:

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

ArangoDB output is not mathematical evidence.  It may identify candidate files,
prior errors, dependency neighborhoods, and prior verified tool runs.  Any Lean
claim still requires owner-file inspection and kernel checking.

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
