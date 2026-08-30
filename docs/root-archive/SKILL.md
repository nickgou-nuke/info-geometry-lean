# SKILL: Autonomic Causal Memory Layer (ArangoDB)

This root skill file is a thin pointer for agents that discover `SKILL.md` at
repository root.  The canonical operational protocol is:

```text
skills/autonomic-causal-memory/SKILL.md
```

Core law:

```text
Graph memory navigates.
Lean owner files decide truth.
Only kernel-checked source edits count.
```

Use `tools/infra/arango_causal_memory.py` only as an opt-in causal-memory and
GraphRAG/local-DAG interface. The authority lane is `dagDoctor` / `dagRefresh`
/ `artifacts/dag/index` plus LeanTrail read models. `ig_nodes` / `ig_edges` are
stale-prone compact retrieval projections only; do not use them as the developed
graph lane. Do not treat ArangoDB or DAG output as proof evidence, and do not
automatically write memory snapshots without an explicit task apex and verified
status.

Basic commands:

```bash
python3 tools/infra/arango_causal_memory.py local-search Delaunay
python3 tools/infra/arango_causal_memory.py local-neighborhood \
  InfoGeometry.OperatorAlgebra.Albert.tripotency_is_cubic_rank2_special
python3 tools/infra/dag_doctor.py
python3 tools/infra/dag_refresh.py --dry-run
python3 tools/infra/arango_causal_memory.py query 'RETURN 1'
python3 tools/infra/arango_causal_memory.py preflight --name Eq --depth 1 --limit 5
python3 tools/infra/arango_causal_memory.py commit-apex --help
```

For full trigger rules, environment variables, safe AQL patterns, and write
guardrails, read the canonical skill file above.
