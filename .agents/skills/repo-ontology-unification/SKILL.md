---
name: repo-ontology-unification
description: Unify mathematical lanes and review duplicate candidates in the info-geometry-lean repository using its Lean declaration DAG, Arango graph, and Auto-Ontology projection. Use for cross-lane ontology mapping, typed bridge discovery, freshness checks, and source-backed deduplication.
metadata:
  short-description: Unify repository ontology lanes
---

# Repository Ontology Unification

Use this skill when an agent must connect multiple mathematical lanes, build a
causal ontology view, or decide whether declarations are duplicates. Read
[`docs/ONTOLOGY_UNIFICATION_PLAYBOOK.md`](../../../docs/ONTOLOGY_UNIFICATION_PLAYBOOK.md)
for the current topology model, endpoints, import semantics, and reporting
requirements.

## Workflow

1. Read `AGENTS.md`, the canonical agent pipeline, the repository deep-search
   protocol, and the unification playbook. Inspect the actual checkout, staged
   work, and current source owners before trusting reports or index results.
2. Separate graph lanes by carrier and relation semantics. Keep Lean
   declaration dependencies (`type` / `value`) distinct from InfoTree,
   LeanTrail, Hodge, literature, and domain-specific causal graphs unless an
   explicit projection connects them.
3. Search the source and query Auto-Ontology/Arango to locate owners and
   consumers. Treat results and fingerprints as navigation evidence. Check
   exact changed declarations as freshness sentinels; a matching count is not
   a freshness proof.
4. Write a compact lane/bridge ledger with exact owner declarations, actual
   carriers and hypotheses, proposed edge kind, source evidence, and the
   smallest missing theorem or map.
5. Review hash or naming matches against Lean source and consumers. Never
   merge owners, erase hypotheses, or redirect imports solely because of a
   structural fingerprint or shared vocabulary.
6. Keep the derivation/dependency subgraph acyclic. Store symmetric
   equivalences and undirected similarity in their own typed relations; do not
   invent an orientation to force them into a DAG.
7. If a real mathematical bridge is needed, implement it in the existing
   carrier owner using explicit maps and full kernel proofs. An umbrella
   theorem should depend on these proved results, not repackage assumptions.
8. For an online declaration-graph refresh, default to the full immutable
   Arango streaming workflow in
   [`docs/ASTAQLHASH-HOWTO.md`](../../../docs/ASTAQLHASH-HOWTO.md#default-agent-workflow-online-immutable-arango-generation).
   Confirm the target and source/build fingerprint, then verify the completed
   generation and query it by its exact ID. Do not use no-flag file export as
   evidence of an online refresh, or legacy streaming that truncates `decls`
   and `edges` as a routine refresh. File-output export remains available when
   a local JSONL/topology consumer needs those artifacts.
9. Treat Auto-Ontology ingestion as a separate database write. Inspect the
   importers, current projection freshness, endpoint, target database, and
   current row counts first. The relationship importer is additive and does
   not delete stale rows; do not claim a clean projection refresh from its
   success. Never overwrite a projection unless the task explicitly
   authorizes that operation.
10. Report source scope, graph freshness, read/write commands, reviewed
   duplicates, Lean validation scope, and unresolved edges separately.

## Routing

- For service startup/recovery and OAuth, use the existing
  [Auto-Ontology operations skill](../auto-ontology-operations/SKILL.md) and
  [`docs/AUTO_ONTOLOGY_AGENT_OPERATIONS.md`](../../../docs/AUTO_ONTOLOGY_AGENT_OPERATIONS.md).
- For query syntax and multi-apex/hash work, use
  [`docs/ASTAQLHASH-HOWTO.md`](../../../docs/ASTAQLHASH-HOWTO.md).
- For graph generation and replacement procedures, use
  [`docs/ARANGO_DAG_REFRESH_METHODOLOGY.md`](../../../docs/ARANGO_DAG_REFRESH_METHODOLOGY.md).
- For Lean owner edits, use the protected-baseline and QMS semantic-kernel
  validation workflows. This skill does not relax their proof or staging gates.
