# Arango Gravitational Context

The proving lane should not assemble context by loose association. For Lean 4 proof construction, context is extracted from already compiled Lean truth: the declaration graph exported into ArangoDB or, when Arango is not populated, the LeanTrail JSONL export.

`tools/infra/arango_gravity_context.py` builds a compact context packet from this graph:

- It prefers live ArangoDB collections `infogeometry/ig_nodes` and `infogeometry/ig_edges`.
- It falls back to `artifacts/leantrail/arango/ig_nodes.jsonl` and `ig_edges.jsonl`.
- It ranks declarations by lexical relevance, graph proximity, and proof mass.
- It emits Lean source excerpts around the proven declaration lines.
- It sets `promotion_allowed: false`; the packet is retrieval context, not proof admission.

Example:

```bash
python tools/infra/arango_gravity_context.py \
  --query "softmax variance logSumExp derivative" \
  --top-k 8 \
  --json-out artifacts/gravity_context/softmax_variance.json \
  --md-out artifacts/gravity_context/softmax_variance.md
```

The output is intended for DeepSeek/Nemotron prompt injection before tactic generation. The agent should be pulled toward nearby verified declarations instead of expanding through unconstrained prose.

Hermes loop integration:

- `tools/infra/hermes_bounded_runner.py` calls `tools/infra/arango_gravity_context.py` before each planner prompt.
- Per-packet context artifacts are written to `artifacts/hermes_loop/gravity_context/`.
- The runner injects a compact `Gravitational Lean context` section into the Nemotron planner prompt.
- If no semantically strong neighbor exists, the runner explicitly suppresses unrelated high-mass nodes and routes toward proof-local Lean/mathlib investigation.

Operational rule:

- Gemini may elaborate hypotheses.
- Codex may control the loop and prepare gates.
- Nemotron may summarize or adjudicate compact context.
- DeepSeek may search Lean-local tactics.
- Lean/lake remains the only authority for truth.

The graph context is strong gravitation: proven code is mass, and proof search should fall through the causal neighborhood of that mass.

## Known Filter Boundaries

The Arango graph is a derived memory carrier, not the raw Lean info tree. Absence
from Arango is therefore not evidence that no semantic connection exists.

Current filters and lossy boundaries include:

- `lean/DAG/Indexer.lean` drops generated or unstable declaration names such as
  names containing `._` or ending in `match_`, `proof_`, or `injEq`.
- `Indexer.lean` keeps only declarations under the selected namespace prefix and
  drops edges whose source or target is outside the filtered node set.
- Dropped edges are classified in `edge-leakage.json`, but they are not inserted
  as ordinary Arango traversal edges.
- `lean/DAG/BlockExport.lean` separates primary declarations from generated
  auxiliaries; primary dependency summaries may omit auxiliary-local structure.
- Block export reads info-tree dependencies only from new command snapshots, so
  it is a semantic block carrier, not a complete global expression graph.
- The LeanTrail Arango adapter stores snapshot nodes/edges in `ig_nodes` and
  `ig_edges`; it does not automatically include every expression node from the
  lower-level global disassembler.
- `tools/infra/arango_gravity_context.py` applies retrieval filters:
  `declarations_only`, `require_source`, `min_seed_score`, `seed_k`,
  `max_hops`, `limit_nodes`, and `limit_edges`.
- Tokenization and stopword filtering can hide a connection unless the synonym
  or equivalence dictionary expands the query first.

Operational consequence: when a proof depends on a suspected semantic pair
`A ↔ B`, run graph retrieval with equivalence expansion, then inspect the raw
owner source and, when necessary, the info-tree/block/export artifacts. Do not
let a missing Arango edge veto a connection that exists in Lean's elaborated
info tree.

## Agent-to-Agent Truth Transport

`tools/infra/hermes_bounded_runner.py` now emits a second artifact for every
planner run that produces route text:

```text
artifacts/hermes_loop/truth_transport/<run_id>.json
artifacts/hermes_loop/truth_transport/latest.json
```

This packet is the object that should move from Hermes/Codex/DeepSeek/Goedel to
the next agent. It contains:

- the parsed planner route (`ROUTE`, `EXECUTION_ALLOWED`, `NEXT_ACTION`, `RATIONALE`, `GUARDS`)
- the graph source and graph size
- compact source-backed neighbor declarations
- an explicit handoff policy
- `codex_mutation_allowed`, which is true only for `ROUTE: codex_execution_request` and `EXECUTION_ALLOWED: yes`
- `canonical_mutation_allowed: false`

Operationally, if a planner or Codex CLI proposes a plausible new theorem, the
next agent must attach this transport packet and restate the theorem relative to
the retrieved compiled neighbors. That pulls the candidate into the orbit of the
existing theory before any Lean probe or mutation is attempted.

The transport packet is still not proof admission. It is inherited context plus
gates. Lean/lake remains the only truth authority.
