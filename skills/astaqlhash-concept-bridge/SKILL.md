---
name: astaqlhash-concept-bridge
description: Use when comparing concept corridors in the compiler-backed Arango declaration DAG without turning graph proximity into a mathematical theorem.
metadata:
  short-description: Bounded read-only AST/AQL concept comparison
---

# ASTAQLHASH concept bridge

Use this skill to locate bounded shared prerequisites between declaration-name
patterns such as Tomita/KMS and Fisher/Onsager. The result is navigation
evidence for owner selection, not a semantic equivalence or proof.

## Required boundaries

- Read `AGENTS.md`, `docs/CANONICAL_AGENT_PIPELINE.md`,
  `docs/REPO_DEEP_SEARCH_PROTOCOL.md`, and `docs/ASTAQLHASH-HOWTO.md` first.
- Search repository-owned source recursively before querying the graph.
- Use only the compiler-backed `decls` and `edges` collections for this tool.
- Edges point declaration → dependency; `OUTBOUND` finds prerequisites and
  `INBOUND` finds dependents. Edge kinds are compiler dependency kinds such as
  `type` and `value`; do not invent `INHERITS_FROM` or `HAS_PROPERTY` edges.
- Keep the query bounded and read-only. Do not use graph refresh, ingestion,
  `commit-apex`, or `--allow-write` for concept discovery.
- Fingerprints, shared nodes, and causal paths do not prove that two concepts
  are mathematically related. Read the owner declarations and prove any
  comparison in Lean.

## Command

```bash
python3 tools/infra/astaql_concept_bridge.py \
  --quantum-term tomita --quantum-term kms \
  --classical-term fisher --classical-term onsager \
  --quantum-module-prefix InfoGeometry.Canonical \
  --classical-module-prefix InfoGeometry.Canonical \
  --depth 3 --seed-limit 20 --cone-limit 200 \
  --pair-limit 200 --shared-limit 50 \
  --json-out /tmp/astaql_concept_bridge.json
```

For a precise comparison, pass exact fully qualified names instead of broad
name patterns, for example:

```bash
python3 tools/infra/astaql_concept_bridge.py \
  --quantum-name InfoGeometry.OperatorAlgebra.OperatorThermodynamics.HorizonKMSThermodynamics.observer_sees_kms \
  --classical-name InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.ParityOnsagerSystem.onsager_casimir_master_reciprocity \
  --depth 3 --json-out /tmp/kms_onsager_path.json
```

`--quantum-name`/`--classical-name` accept exact indexed declaration names and
override the corresponding term pattern. Module-prefix flags are optional;
use them to avoid selecting the first lexicographic matches across unrelated
namespaces. The result reports total matched and selected seed counts, selected
declaration fingerprints, direct bounded paths between each selected pair,
and the bounded dependency paths (including `type`/`value` edge kinds) to each
shared prerequisite. It intentionally excludes non-compiler edge kinds.

The command uses the repository Arango environment loader and emits endpoint,
database, bounds, query SHA-256, result rows, and query statistics. It never
writes to ArangoDB. An empty result distinguishes zero matching seeds from no
shared prerequisites within the configured bounds, but neither case proves a
semantic bridge absent. Hashes and graph paths are navigation evidence only.
Review owner, imports, carrier, and exact theorem statements before using any
returned row in a formalization task.

## Interpretation

Treat a returned shared declaration as a candidate prerequisite corridor. A
missing shared node does not show that a bridge is absent, because the search
is name-pattern and depth bounded. A successful match does not show that a
comparison map exists. The acceptance path is owner source inspection followed
by a native Lean theorem and the repository's locked sequential verification.
