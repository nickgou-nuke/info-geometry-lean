# Arango Hive Schema Implementation Spec

Status: implementation spec
Date: 2026-04-24
Scope: typed ArangoDB collections, edges, indexes, lineage, and write discipline for the Hermes Jung–Pauli Split-Step Hive.

## 1. Purpose

This document specifies the ArangoDB schema for the Hive memory spine.

It is downstream of:
- `JUNG_PAULI_SPLIT_STEP_HIVE_BLUEPRINT.md`
- `hermes_recursive_hive_architecture.md`
- `ARANGO_FAITHFUL_GRAPH.md`
- `ARANGO_GRAVITATIONAL_CONTEXT.md`

The aim is to make the Hive memory backbone:
- typed
- revision-aware
- lineage-preserving
- compatible with the existing faithful/raw/projection Arango doctrine
- suitable for recurrent symbolic cultivation, packetization, and Lean-facing formalization

## 2. Design principles

## 2.1 Layering principle

Do not collapse all memory into one graph.

The Arango deployment should maintain four distinct layers:

1. **Lean-faithful topology layer**
   - existing raw compiler / DAG / hydration / retrieval collections
   - source of truth for compiled-theory structure

2. **Hive epistemic layer**
   - symbolic seeds
   - Jung variants
   - Pauli critiques
   - invariants
   - packets
   - residues

3. **Operational lineage layer**
   - runs
   - agent roles
   - prompts
   - revisions
   - task ownership

4. **Derived overlay layer**
   - clustering
   - ranking
   - caches
   - analytics
   - candidate projections

The Hive layer must link to the Lean-faithful layer. It must not replace it.

## 2.2 Truth boundary

Arango stores memory, structure, and process state.

Arango does **not** store theorem truth by mere assertion.

Truth authority remains:

```text
Lean elaboration / REPL / lake / audit gates
```

Arango may store:
- theorem candidates
- proof attempts
- build outcomes
- audit outcomes
- promotion decisions

but these are historical/stateful objects, not truth itself.

## 2.3 Revision principle

The Hive should prefer append-first state transitions over destructive mutation.

Allowed:
- update `status`
- attach later metadata
- append new revision objects
- add edges recording replacement, refinement, or invalidation

Avoid:
- silent overwrite of semantic history
- replacing prior symbolic objects in place without lineage

## 2.4 Typed memory principle

Every important document must have:
- a typed collection
- a stable `_key`
- a `kind`
- a `status`
- a `lineage_id`
- a `revision`
- creation and update timestamps

## 3. Relationship to existing Arango collections

This schema does **not** replace the current theorem-factory graph collections such as:
- `ig_nodes`
- `ig_edges`
- `raw_info_nodes`
- `raw_info_edges`
- `raw_infotree_*`
- `topology_overlay`
- `topology_overlay_edges`
- `arango_dag_*`

Those remain the structural / compiler-memory substrate.

The Hive schema adds a parallel epistemic graph that points into those layers.

## 4. Database and graph naming

Recommended database:
- reuse existing `infogeometry` database when operationally convenient

Recommended named graphs:
- `hive_epistemic_graph`
- `hive_lineage_graph`

Optional combined named graph:
- `hive_memory_graph`

The combined graph may include both epistemic and lineage edges, but raw Lean topology should remain queryable independently.

## 5. Collection families

## 5.1 Epistemic vertex collections

### `hive_symbolic_seeds`
Raw intake objects representing a seed of emergence.

Examples:
- black-book fragment
- Socratic dialogue fragment
- obstruction note
- DAG anomaly note
- audit objection note
- operator prompt distilled into a seed

Required fields:
- `_key`
- `kind = "SymbolicSeed"`
- `status` (`draft|active|cultivated|retired`)
- `lineage_id`
- `revision`
- `seed_hash`
- `source_class`
- `source_ref`
- `source_excerpt`
- `source_locator`
- `content_text`
- `pressure_class`
- `origin_run_id`
- `created_by_agent`
- `created_at`
- `updated_at`

### `hive_formulation_variants`
Outputs of Jung excitation passes.

Required fields:
- `_key`
- `kind = "FormulationVariant"`
- `status` (`draft|active|clustered|discarded|merged`)
- `lineage_id`
- `revision`
- `seed_hash`
- `variant_index`
- `iteration_index`
- `jungle_pass_id`
- `representation_mode`
- `content_text`
- `summary`
- `backend`
- `temperature_profile`
- `confidence`
- `formal_projection_score`
- `created_by_agent`
- `origin_run_id`
- `created_at`
- `updated_at`

### `hive_resonance_clusters`
Objects representing grouped recurrent structures across variants.

Required fields:
- `_key`
- `kind = "ResonanceCluster"`
- `status` (`draft|active|stabilized|superseded`)
- `lineage_id`
- `revision`
- `cluster_method`
- `cluster_signature`
- `member_count`
- `invariant_hypothesis`
- `distinguishing_axes`
- `origin_run_id`
- `created_at`
- `updated_at`

### `hive_pauli_critiques`
Differentiation, sharpening, and admissibility-pressure outputs.

Required fields:
- `_key`
- `kind = "PauliCritique"`
- `status` (`draft|active|applied|superseded`)
- `lineage_id`
- `revision`
- `iteration_index`
- `critique_mode`
- `target_scope`
- `critique_text`
- `novelty_assessment`
- `duplication_assessment`
- `formal_target_assessment`
- `repo_anchor_assessment`
- `admissibility_state`
- `cost_class`
- `origin_run_id`
- `created_by_agent`
- `created_at`
- `updated_at`

### `hive_invariants`
Stable structural content extracted after recurrence.

Required fields:
- `_key`
- `kind = "InvariantDraft"`
- `status` (`draft|stable|translated|formalized|retired`)
- `lineage_id`
- `revision`
- `iteration_index`
- `invariant_text`
- `invariant_class`
- `bridge_claim`
- `novelty_defense_summary`
- `formal_projection_summary`
- `repo_anchor_summary`
- `confidence`
- `stability_score`
- `origin_run_id`
- `created_by_agent`
- `created_at`
- `updated_at`

### `hive_packets`
Legalized packet objects ready for downstream gates.

Required fields:
- `_key`
- `kind` (see packet kinds below)
- `status`
- `lineage_id`
- `revision`
- `packet_version`
- `packet_hash`
- `origin_run_id`
- `created_by_agent`
- `created_at`
- `updated_at`

Supported `kind` values at this layer:
- `TheoremCandidatePacket`
- `RetrievalHypothesisPacket`
- `CritiquePacket`
- `TranslationPacket`
- `ExecutionIntentPacket`
- `ResiduePacket`

### `hive_lean_targets`
Lean-facing projections derived from invariants or packets.

Required fields:
- `_key`
- `kind = "LeanTarget"`
- `status` (`draft|probe_ready|probed|invalid|promoted`)
- `lineage_id`
- `revision`
- `namespace_candidate`
- `declaration_name_candidate`
- `signature_text`
- `imports_candidate`
- `module_candidate`
- `dependency_candidates`
- `probe_plan`
- `origin_run_id`
- `created_at`
- `updated_at`

### `hive_failure_residues`
Structured retained failures and unresolved tensions.

Required fields:
- `_key`
- `kind = "FailureResidue"`
- `status` (`active|recycled|closed|archived`)
- `lineage_id`
- `revision`
- `failure_class`
- `failure_stage`
- `failure_text`
- `recoverability`
- `next_cultivation_hint`
- `origin_run_id`
- `created_by_agent`
- `created_at`
- `updated_at`

### `hive_promotion_decisions`
Persistent records of admission or rejection at canonical boundaries.

Required fields:
- `_key`
- `kind = "PromotionDecision"`
- `status` (`accepted|rejected|deferred|rolled_back`)
- `lineage_id`
- `revision`
- `decision_scope`
- `decision_text`
- `authority_gate`
- `evidence_refs`
- `decided_by_agent`
- `origin_run_id`
- `created_at`
- `updated_at`

## 5.2 Operational vertex collections

### `hive_agent_runs`
One document per bounded Hive run/pass.

Required fields:
- `_key`
- `kind = "AgentRun"`
- `run_id`
- `session_key`
- `task_id`
- `lineage_id`
- `agent_role`
- `backend`
- `runtime_envelope`
- `start_time`
- `end_time`
- `outcome`
- `error_class`
- `created_at`
- `updated_at`

### `hive_lineages`
Top-level continuity objects spanning multiple runs.

Required fields:
- `_key`
- `kind = "Lineage"`
- `lineage_id`
- `status`
- `root_seed_key`
- `current_focus`
- `owner_role`
- `created_at`
- `updated_at`

### `hive_tasks`
User-visible or system-generated work packets spanning multiple runs.

Required fields:
- `_key`
- `kind = "HiveTask"`
- `task_id`
- `status`
- `task_class`
- `title`
- `description`
- `owner_role`
- `lineage_id`
- `priority`
- `created_at`
- `updated_at`

### `hive_skills`
Skill snapshots or references used by runs.

Required fields:
- `_key`
- `kind = "SkillRef"`
- `skill_name`
- `skill_version`
- `skill_path`
- `skill_hash`
- `created_at`
- `updated_at`

## 5.3 Derived/cache collections

These are optional and may be dropped/rebuilt.

Recommended:
- `hive_cluster_cache`
- `hive_rank_cache`
- `hive_query_views`
- `hive_merge_candidates`

Rule: derived/cache collections must never be the only location of semantically important state.

## 6. Edge collections

## 6.1 Core epistemic edges

### `hive_epistemic_edges`
Primary edge collection for semantic transformation relationships.

Allowed `role` values include:
- `seed_of`
- `excites`
- `reformulates_as`
- `clusters_with`
- `sharpens`
- `extracts_invariant`
- `legalizes_as`
- `translates_to`
- `probes`
- `fails_into`
- `revives_from`
- `supersedes`
- `duplicates`
- `criticizes`
- `supports`
- `blocks`
- `promotes_to`

Required edge fields:
- `_key`
- `_from`
- `_to`
- `role`
- `lineage_id`
- `revision`
- `origin_run_id`
- `weight`
- `evidence_class`
- `created_at`
- `updated_at`

## 6.2 Operational lineage edges

### `hive_lineage_edges`
Tracks ownership, generation, task assignment, and revision flow.

Allowed `role` values include:
- `generated_by`
- `created_in_run`
- `belongs_to_lineage`
- `belongs_to_task`
- `uses_skill`
- `owned_by`
- `refines`
- `revises`
- `invalidates`
- `forks_from`
- `merges_from`

Required fields:
- `_key`
- `_from`
- `_to`
- `role`
- `lineage_id`
- `origin_run_id`
- `created_at`
- `updated_at`

## 6.3 Cross-layer anchor edges

### `hive_anchor_edges`
Connects Hive epistemic objects to faithful Lean/DAG/overlay objects.

This is essential. The Hive must anchor back into compiled-theory geometry.

Allowed `role` values include:
- `anchors_to_decl`
- `anchors_to_raw_node`
- `anchors_to_scc`
- `anchors_to_retrieval_node`
- `anchors_to_source_fragment`
- `validated_by_build`
- `validated_by_audit`
- `validated_by_probe`

Required fields:
- `_key`
- `_from`
- `_to`
- `role`
- `anchor_strength`
- `anchor_method`
- `origin_run_id`
- `created_at`
- `updated_at`

## 7. Packet kinds and minimum content

The concrete JSON schema for packets should be specified separately, but Arango documents in `hive_packets` should already reserve the following minimum fields.

## 7.1 `TheoremCandidatePacket`
Minimum document payload:
- `symbolic_origin_refs`
- `formal_target`
- `bridge_claim`
- `novelty_defense`
- `repo_anchor_refs`
- `candidate_dependencies`
- `admissibility_state`
- `cost_class`

## 7.2 `RetrievalHypothesisPacket`
Minimum payload:
- `query_text`
- `seed_refs`
- `candidate_anchor_refs`
- `graph_mode`
- `retrieval_summary`
- `promotion_allowed = false`

## 7.3 `CritiquePacket`
Minimum payload:
- `target_refs`
- `critique_summary`
- `distinctions`
- `risk_flags`
- `admissibility_recommendation`

## 7.4 `TranslationPacket`
Minimum payload:
- `invariant_refs`
- `namespace_candidate`
- `signature_candidates`
- `module_candidate`
- `imports_candidate`
- `minimal_probe_plan`

## 7.5 `ExecutionIntentPacket`
Minimum payload:
- `target_refs`
- `intended_actions`
- `required_tools`
- `required_gates`
- `mutation_scope`
- `execution_allowed`

## 7.6 `ResiduePacket`
Minimum payload:
- `failure_refs`
- `failure_class`
- `stage`
- `recovery_hint`
- `return_route`

## 8. Key format recommendations

Use stable, readable keys where possible.

Suggested patterns:
- `seed_<shorthash>`
- `variant_<lineage>_<iter>_<n>`
- `cluster_<lineage>_<iter>_<shorthash>`
- `critique_<lineage>_<iter>_<shorthash>`
- `invariant_<lineage>_<iter>_<shorthash>`
- `packet_<kind>_<lineage>_<rev>`
- `target_<lineage>_<rev>`
- `residue_<lineage>_<iter>_<shorthash>`
- `run_<timestamp>_<shorthash>`
- `lineage_<shorthash>`
- `task_<shorthash>`

Do not encode full mutable semantics into `_key`.
The mutable state belongs in document fields.

## 9. Common field definitions

Recommended common fields for all Hive documents:
- `_key`
- `kind`
- `status`
- `lineage_id`
- `revision`
- `origin_run_id`
- `created_at`
- `updated_at`
- `created_by_agent`
- `backend`
- `tags`
- `notes`

Optional but recommended:
- `session_key`
- `task_id`
- `parent_refs`
- `evidence_refs`
- `source_hashes`

## 10. Status vocabularies

Use small controlled vocabularies.

### Symbolic lifecycle
- `draft`
- `active`
- `stabilized`
- `translated`
- `formalized`
- `retired`
- `archived`

### Packet lifecycle
- `draft`
- `legalized`
- `probe_ready`
- `gated`
- `executed`
- `accepted`
- `rejected`
- `deferred`

### Failure lifecycle
- `active`
- `recycled`
- `closed`
- `archived`

## 11. Index plan

## 11.1 Required persistent indexes

For every main vertex collection:
- persistent index on `lineage_id`
- persistent index on `status`
- persistent index on `origin_run_id`
- persistent index on `created_at`

For frequently filtered collections:
- `hive_formulation_variants`: index on `(lineage_id, iteration_index)`
- `hive_pauli_critiques`: index on `(lineage_id, iteration_index)`
- `hive_invariants`: index on `(lineage_id, status)`
- `hive_packets`: index on `(kind, status)`
- `hive_failure_residues`: index on `(failure_class, status)`
- `hive_agent_runs`: index on `(task_id, start_time)`

For edge collections:
- persistent index on `role`
- persistent index on `lineage_id`
- persistent index on `origin_run_id`

## 11.2 Full-text / search recommendations

Use ArangoSearch views or equivalent only as a secondary capability.

Suggested indexed text fields:
- `content_text`
- `summary`
- `invariant_text`
- `critique_text`
- `failure_text`
- packet payload text surfaces

Important: search views are convenience layers, not canonical storage.

## 12. Write discipline

## 12.1 Allowed mutation patterns

Good:
- create new symbolic objects per pass
- update statuses after a gate
- create refinement/revision edges
- attach anchor edges after graph retrieval or build validation
- append promotion decisions

Bad:
- overwrite a seed with a later invariant
- overwrite a variant with a merged text without revision trail
- delete residues because they “failed”
- repurpose a packet key for a different packet kind

## 12.2 Revision policy

Recommended revision handling:
- `revision` starts at `1`
- semantic replacement creates a new document or a new packet revision
- connect old to new with `revises` or `supersedes`
- statuses on older revisions become `superseded` or `retired`

## 12.3 Idempotency

Writers should be idempotent where practical.

At minimum:
- packet hash or content hash should prevent accidental duplicate writes in the same run
- run writers should store deterministic `run_id`
- lineage creation should upsert by `lineage_id`

## 13. Cross-layer anchors and faithful retrieval

The Hive must explicitly bind its symbolic objects to the faithful theorem graph.

Minimum required anchor flow before expensive formalization:

```text
seed / invariant / theorem packet
  -> retrieval hypothesis
  -> SCC or declaration anchor
  -> raw witness descent where needed
  -> Lean-facing target proposal
```

No packet intended for serious formalization should remain completely unanchored to repository structure.

However, absence of anchor in a retrieval projection is not proof of semantic absence.
In those cases, the system must fall back to raw/faithful layers per existing Arango doctrine.

## 14. Residue taxonomy

Recommended controlled `failure_class` values:
- `symbolic_overheat`
- `formal_target_missing`
- `repo_anchor_missing`
- `novelty_collapse`
- `proof_obstruction`
- `translation_failure`
- `architecture_illegality`
- `transport_failure`
- `build_failure`
- `audit_rejection`
- `merge_instability`

Recommended `recoverability` values:
- `high`
- `medium`
- `low`
- `unknown`

## 15. Minimal AQL usage patterns

## 15.1 Active lineage view

```aql
FOR d IN hive_invariants
  FILTER d.lineage_id == @lineage_id
  FILTER d.status IN ["draft", "stable", "translated"]
  SORT d.updated_at DESC
  RETURN d
```

## 15.2 Residue return queue

```aql
FOR r IN hive_failure_residues
  FILTER r.status == "active"
  SORT r.updated_at DESC
  LIMIT 50
  RETURN r
```

## 15.3 Anchored theorem candidates

```aql
FOR p IN hive_packets
  FILTER p.kind == "TheoremCandidatePacket"
  FILTER p.status IN ["legalized", "probe_ready", "gated"]
  LET anchors = (
    FOR e IN hive_anchor_edges
      FILTER e._from == CONCAT("hive_packets/", p._key)
      RETURN e
  )
  FILTER LENGTH(anchors) > 0
  RETURN MERGE(p, {anchors})
```

## 15.4 Recent run lineage trace

```aql
FOR r IN hive_agent_runs
  SORT r.start_time DESC
  LIMIT 20
  LET objects = (
    FOR e IN hive_lineage_edges
      FILTER e.origin_run_id == r.run_id
      RETURN e
  )
  RETURN {run: r, edges: objects}
```

## 16. Phased rollout

## Phase A — core collections
Create:
- `hive_symbolic_seeds`
- `hive_formulation_variants`
- `hive_pauli_critiques`
- `hive_invariants`
- `hive_packets`
- `hive_failure_residues`
- `hive_agent_runs`
- `hive_lineages`
- `hive_epistemic_edges`
- `hive_lineage_edges`
- `hive_anchor_edges`

This is the minimum viable Hive memory spine.

## Phase B — cluster and target surfaces
Add:
- `hive_resonance_clusters`
- `hive_lean_targets`
- `hive_tasks`
- `hive_promotion_decisions`

## Phase C — overlays and search views
Add:
- search views
- cache collections
- ranking overlays
- merge candidate surfaces

## 17. Non-negotiables

- The Hive schema must not replace faithful Lean/raw topology collections.
- All semantically important objects must carry lineage and revision.
- Packets must be stored as typed objects, not loose blobs.
- Residue must be preserved.
- Expensive formalization should require anchor edges or an explicit faithful-layer fallback record.
- Arango stores memory and process state; Lean stores truth authority.

## 18. Compressed implementation doctrine

```text
Preserve raw Lean truth separately.
Store Hive emergence as typed epistemic objects.
Link every important object into lineage.
Anchor candidates back to theory geometry.
Record failure as residue, not deletion.
Promote by gates, not by prose.
```
