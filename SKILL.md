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
GraphRAG interface.  Do not treat ArangoDB output as proof evidence, and do not
automatically write memory snapshots without an explicit task apex and verified
status.

Basic commands:

```bash
python3 tools/infra/arango_causal_memory.py query 'RETURN 1'
python3 tools/infra/arango_causal_memory.py commit-apex --help
```

For full trigger rules, environment variables, safe AQL patterns, and write
guardrails, read the canonical skill file above.
