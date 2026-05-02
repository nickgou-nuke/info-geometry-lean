# Hive Packet JSON Schemas

> Status: `reference memory`
> Audited: 2026-05-02
> Note: Re-audit against current code before using for policy, design claims, or status.
> See: [README.md](../README.md), [docs/README.md](README.md), [docs/CODEBASE_STATUS.md](CODEBASE_STATUS.md)

Status: implementation spec
Date: 2026-05-22
Scope: concrete JSON packet schemas for the Jung–Pauli Split-Step Hive, aligned with `JUNG_PAULI_SPLIT_STEP_HIVE_BLUEPRINT.md` and `ARANGO_HIVE_SCHEMA_IMPLEMENTATION_SPEC.md`.

## 1. Purpose

This document defines concrete JSON shapes for the Hive's symbolic objects, legal packets, and residue objects.

It is downstream of:
- `JUNG_PAULI_SPLIT_STEP_HIVE_BLUEPRINT.md`
- `ARANGO_HIVE_SCHEMA_IMPLEMENTATION_SPEC.md`
- `docs/hermes_recursive_hive_architecture.md`
- existing repo Arango layering doctrine (`ARANGO_FAITHFUL_GRAPH.md`, faithful/raw/projection layering)

These schemas are for:
- packet legalization discipline
- Arango document shaping
- file/artifact interchange
- worker handoff contracts
- future validator implementation

They are not theorem-truth certificates.

Truth authority remains:
- Lean elaboration / kernel contact
- targeted build
- audit gates
- promotion gates

## 2. Doctrine summary

The Hive distinguishes three classes of objects:

1. Pre-legal symbolic objects
   - `SymbolicSeed`
   - `FormulationVariant`
   - `ResonanceCluster`
   - `PauliCritique`
   - `InvariantDraft`

2. Legal packet surfaces
   - `TheoremCandidatePacket`
   - `TranslationPacket`
   - `ResiduePacket`
   - plus repo-allowed supporting packet forms such as `RetrievalHypothesisPacket`, `CritiquePacket`, `ExecutionIntentPacket`

3. Authority-gate outputs
   - `LeanVerificationPacket`
   - `BuildPacket`
   - `AuditPacket`
   - `PromotionDecisionPacket`

This document focuses on the packet families:
- `SymbolicSeed`
- `FormulationVariant`
- `ResonanceCluster`
- `PauliCritique`
- `InvariantDraft`
- `TheoremCandidatePacket`
- `TranslationPacket`
- `ResiduePacket`
- `LeanVerificationPacket`
- `BuildPacket`
- `AuditPacket`
- `PromotionDecisionPacket`

## 3. Shared envelope

Every object should carry a shared envelope.

```json
{
  "id": "packet_theorem_candidate_lineage_ab12_rev1",
  "kind": "TheoremCandidatePacket",
  "status": "legalized",
  "lineage_id": "lineage_ab12cd34",
  "revision": 1,
  "origin_run_id": "run_20260424T072500Z_f81d",
  "created_by_agent": "translation-bee",
  "agent_role": "translation",
  "backend": "codex-cli",
  "task_id": "task_7c9e",
  "session_key": "local-session-20260424",
  "created_at": "2026-04-24T07:25:00Z",
  "updated_at": "2026-04-24T07:25:00Z",
  "tags": ["jung-pauli", "hive", "formalization"],
  "notes": "Optional operator or worker notes.",
  "parent_refs": [],
  "evidence_refs": [],
  "source_hashes": []
}
```

## 4. Shared field semantics

### 4.1 Required on all objects
- `id`: stable external identifier; should match or derive from Arango `_key`
- `kind`: controlled object type
- `status`: controlled lifecycle state
- `lineage_id`: top-level continuity id
- `revision`: integer, starts at 1
- `origin_run_id`: run that emitted this object
- `created_at`, `updated_at`: ISO-8601 UTC timestamps

### 4.2 Recommended on all objects
- `created_by_agent`
- `agent_role`
- `backend`
- `task_id`
- `session_key`
- `tags`
- `notes`
- `parent_refs`
- `evidence_refs`
- `source_hashes`

### 4.3 Reference object shape
When a schema uses `*_refs`, each element should be an object rather than a bare string when possible.

```json
{
  "ref": "hive_invariants/invariant_lineage_ab12_3e91",
  "kind": "InvariantDraft",
  "role": "primary_invariant",
  "confidence": 0.82
}
```

Minimum fallback form:

```json
"hive_invariants/invariant_lineage_ab12_3e91"
```

## 5. Controlled vocabularies

### 5.1 Common status vocabularies

Pre-legal symbolic objects:
- `draft`
- `active`
- `stabilized`
- `translated`
- `formalized`
- `retired`
- `archived`

Packet objects:
- `draft`
- `legalized`
- `probe_ready`
- `gated`
- `executed`
- `accepted`
- `rejected`
- `deferred`

Authority-gate status (specific):
- `passed`
- `failed`
- `approved`
- `promoted`
- `in_progress`
- `needs_retry`

Residues:
- `active`
- `recycled`
- `closed`
- `archived`

### 5.2 Admissibility states
- `unknown`
- `emergent`
- `plausible`
- `needs_anchor`
- `needs_translation`
- `inadmissible`
- `admissible_for_probe`
- `admissible_for_build`

### 5.3 Cost classes
- `low`
- `medium`
- `high`
- `very_high`
- `unknown`

### 5.4 Residue classes
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

## 6. Pre-legal symbolic object schemas

## 6.1 `SymbolicSeed`

Purpose:
- root intake object for symbolic pressure
- not yet a legal theorem-factory packet

Required fields:
- shared envelope
- `kind = "SymbolicSeed"`
- `seed_hash`
- `source_class`
- `source_ref`
- `source_excerpt`
- `source_locator`
- `content_text`
- `pressure_class`

Suggested `source_class`:
- `black_book_fragment`
- `dialogue_fragment`
- `dag_anomaly`
- `audit_objection`
- `operator_prompt`
- `alexandria_extract`
- `residue_return`

Suggested `pressure_class`:
- `definition_pressure`
- `theorem_pressure`
- `bridge_pressure`
- `obstruction_pressure`
- `audit_pressure`
- `graph_pressure`

Example:

```json
{
  "id": "seed_9e9fd2",
  "kind": "SymbolicSeed",
  "status": "active",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "origin_run_id": "run_20260424T080000Z_aa12",
  "created_by_agent": "mother-bee",
  "agent_role": "orchestrator",
  "backend": "local",
  "created_at": "2026-04-24T08:00:00Z",
  "updated_at": "2026-04-24T08:00:00Z",
  "seed_hash": "sha256:...",
  "source_class": "black_book_fragment",
  "source_ref": "docs/black_books/191_conformal_bridge.md#fragment-12",
  "source_excerpt": "The operatorial bridge appears only after symmetry splitting...",
  "source_locator": {
    "path": "docs/black_books/191_conformal_bridge.md",
    "section": "fragment-12"
  },
  "content_text": "Potential invariant relating split-step recurrence to admissible theorem shaping.",
  "pressure_class": "bridge_pressure",
  "tags": ["split-step", "operatorial", "bridge"]
}
```

Validation notes:
- must not claim theorem truth
- must not include Lean/build success claims unless only as cited evidence in `evidence_refs`

## 6.2 `FormulationVariant`

Purpose:
- one Jung-pass reformulation or alternate representational rendering

Required fields:
- shared envelope
- `kind = "FormulationVariant"`
- `seed_hash`
- `variant_index`
- `iteration_index`
- `jung_pass_id`
- `representation_mode`
- `content_text`
- `summary`
- `temperature_profile`
- `confidence`
- `formal_projection_score`

Suggested `representation_mode`:
- `geometric`
- `categorical`
- `operatorial`
- `lean_facing`
- `thermodynamic`
- `semantic_bridge`
- `namespace_shaping`

Example:

```json
{
  "id": "variant_lineage_9f22d1c1_1_3",
  "kind": "FormulationVariant",
  "status": "active",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "origin_run_id": "run_20260424T081000Z_bb12",
  "created_by_agent": "jung-bee-2",
  "agent_role": "jung",
  "backend": "codex-cli",
  "created_at": "2026-04-24T08:10:00Z",
  "updated_at": "2026-04-24T08:10:00Z",
  "seed_hash": "sha256:...",
  "variant_index": 3,
  "iteration_index": 1,
  "jung_pass_id": "jungpass_lineage_9f22d1c1_iter1",
  "representation_mode": "lean_facing",
  "content_text": "A split-step admissibility lemma may be phrased as stability under alternating excitation and exclusion operators.",
  "summary": "Lean-facing theorem phrasing of the split-step doctrine.",
  "temperature_profile": "high",
  "confidence": 0.61,
  "formal_projection_score": 0.67
}
```

Validation notes:
- `variant_index` should be unique within `(lineage_id, iteration_index)`
- `formal_projection_score` should be numeric in `[0,1]`

## 6.3 `ResonanceCluster`

Purpose:
- group of recurrent motifs across variants
- first coarse candidate for invariant-bearing structure

Required fields:
- shared envelope
- `kind = "ResonanceCluster"`
- `cluster_method`
- `cluster_signature`
- `member_count`
- `invariant_hypothesis`
- `distinguishing_axes`

Example:

```json
{
  "id": "cluster_lineage_9f22d1c1_2_7b14",
  "kind": "ResonanceCluster",
  "status": "active",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "origin_run_id": "run_20260424T082500Z_cc12",
  "created_by_agent": "jung-clusterer",
  "agent_role": "jung",
  "backend": "local",
  "created_at": "2026-04-24T08:25:00Z",
  "updated_at": "2026-04-24T08:25:00Z",
  "cluster_method": "semantic-signature-overlap",
  "cluster_signature": "split-step|admissibility|invariant-extraction",
  "member_count": 5,
  "invariant_hypothesis": "Repeated alternation between excitation and exclusion yields a stable admissible theorem shape.",
  "distinguishing_axes": [
    "operatorial_vs_geometric",
    "formal_target_specificity",
    "anchor_density"
  ]
}
```

Validation notes:
- `member_count >= 1`
- should be derivable from actual variant membership edges in Arango

## 6.4 `PauliCritique`

Purpose:
- post-family distinction and anti-inflation object
- separates genuinely distinct branches from decorative restatement

Required fields:
- shared envelope
- `kind = "PauliCritique"`
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

Suggested `critique_mode`:
- `branch_separation`
- `novelty_defense`
- `duplication_collapse`
- `formal_projection_pressure`
- `repo_anchor_pressure`
- `architecture_legality`

Example:

```json
{
  "id": "critique_lineage_9f22d1c1_2_a411",
  "kind": "PauliCritique",
  "status": "active",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "origin_run_id": "run_20260424T083000Z_dd12",
  "created_by_agent": "pauli-bee-1",
  "agent_role": "pauli",
  "backend": "codex-cli",
  "created_at": "2026-04-24T08:30:00Z",
  "updated_at": "2026-04-24T08:30:00Z",
  "iteration_index": 2,
  "critique_mode": "repo_anchor_pressure",
  "target_scope": {
    "variant_refs": ["variant_lineage_9f22d1c1_2_1", "variant_lineage_9f22d1c1_2_4"],
    "cluster_refs": ["cluster_lineage_9f22d1c1_2_7b14"]
  },
  "critique_text": "The family is semantically promising but remains unanchored to current SCC/decl structure; do not legalize yet.",
  "novelty_assessment": "non_trivial_but_unproven",
  "duplication_assessment": "partial_restating_overlap",
  "formal_target_assessment": "coherent_but_underspecified",
  "repo_anchor_assessment": "missing_required_anchor",
  "admissibility_state": "needs_anchor",
  "cost_class": "medium"
}
```

Validation notes:
- should operate on an existing family, not a single seed at birth
- must not claim final rejection unless routed through a legal packet or gate object

## 6.5 `InvariantDraft`

Purpose:
- stabilized structural content extracted after recurrence
- still pre-legal, but closer to packetization

Required fields:
- shared envelope
- `kind = "InvariantDraft"`
- `iteration_index`
- `invariant_text`
- `invariant_class`
- `bridge_claim`
- `novelty_defense_summary`
- `formal_projection_summary`
- `repo_anchor_summary`
- `confidence`
- `stability_score`

Suggested `invariant_class`:
- `theorem_shape`
- `definition_need`
- `bridge_relation`
- `lemma_family`
- `obstruction_pattern`

Example:

```json
{
  "id": "invariant_lineage_9f22d1c1_2_3e91",
  "kind": "InvariantDraft",
  "status": "stabilized",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "origin_run_id": "run_20260424T084500Z_ee12",
  "created_by_agent": "pauli-bee-2",
  "agent_role": "pauli",
  "backend": "codex-cli",
  "created_at": "2026-04-24T08:45:00Z",
  "updated_at": "2026-04-24T08:45:00Z",
  "iteration_index": 2,
  "invariant_text": "Admissible theorem emergence requires alternation between semantic expansion and exclusion-driven sharpening until a stable repository-anchored formal target appears.",
  "invariant_class": "bridge_relation",
  "bridge_claim": "Jung excitation and Pauli sharpening form a lawful pre-formal recurrence prior to Lean translation.",
  "novelty_defense_summary": "Not mere metaphor; predicts a packetizable control flow and anchor discipline absent from the prior architecture.",
  "formal_projection_summary": "Projects to a theorem-factory control invariant and packet admission law.",
  "repo_anchor_summary": "Anchors expected near Hive packet/legalization and Arango overlay discipline docs.",
  "confidence": 0.79,
  "stability_score": 0.83
}
```

Validation notes:
- should summarize stable structure, not merely restate one variant
- `stability_score` should reflect recurrence evidence, not just stylistic confidence

## 7. Legal packet schemas

## 7.1 `TheoremCandidatePacket`

Purpose:
- first legalized theorem-facing packet
- legal target for downstream translation/probe/build routing

Required fields:
- shared envelope
- `kind = "TheoremCandidatePacket"`
- `packet_version`
- `packet_hash`
- `symbolic_origin_refs`
- `formal_target`
- `bridge_claim`
- `novelty_defense`
- `repo_anchor_refs`
- `candidate_dependencies`
- `admissibility_state`
- `cost_class`

Recommended fields:
- `promotion_allowed` (default `false`)
- `anchor_completeness`
- `target_namespace_candidates`
- `target_module_candidates`

Example:

```json
{
  "id": "packet_theorem_candidate_lineage_9f22d1c1_rev1",
  "kind": "TheoremCandidatePacket",
  "status": "legalized",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260424T090000Z_ff12",
  "created_by_agent": "translation-bee",
  "agent_role": "translation",
  "backend": "codex-cli",
  "created_at": "2026-04-24T09:00:00Z",
  "updated_at": "2026-04-24T09:00:00Z",
  "symbolic_origin_refs": [
    {"ref": "hive_symbolic_seeds/seed_9e9fd2", "kind": "SymbolicSeed"},
    {"ref": "hive_invariants/invariant_lineage_9f22d1c1_2_3e91", "kind": "InvariantDraft", "role": "primary_invariant"}
  ],
  "formal_target": {
    "target_kind": "theorem_family",
    "summary": "Admissibility law for split-step Hive packet emergence",
    "candidate_shape": "A recurrence satisfying excitation/sharpening/anchor conditions yields a legalizable theorem candidate."
  },
  "bridge_claim": "The split-step Jung–Pauli recurrence admits a formal theorem-factory control invariant.",
  "novelty_defense": {
    "summary": "The doctrine is operational and packetizable, not merely rhetorical.",
    "duplication_assessment": "No exact duplicate in current hive docs.",
    "pressure_points": ["admission law", "anchor discipline", "residue return"]
  },
  "repo_anchor_refs": [
    {"ref": "topology_overlay/scc_123", "kind": "SCCNode", "role": "anchors_to_scc"},
    {"ref": "raw_info_nodes/node_abc", "kind": "RawInfoNode", "role": "anchors_to_raw_node"}
  ],
  "candidate_dependencies": [
    "Lean packet authority discipline",
    "Arango anchor-edge implementation",
    "Hive packet legality checker"
  ],
  "admissibility_state": "admissible_for_probe",
  "cost_class": "medium",
  "promotion_allowed": false,
  "anchor_completeness": "partial"
}
```

Validation notes:
- must have at least one symbolic or invariant origin ref
- must include non-empty `formal_target`
- must include non-empty `novelty_defense`
- serious formalization targets should not have empty `repo_anchor_refs`
- cannot by itself assert Lean/build/audit success

## 7.2 `TranslationPacket`

Purpose:
- Lean-facing translation of invariants or theorem candidates
- proposes namespace/module/signature/probe shape

Required fields:
- shared envelope
- `kind = "TranslationPacket"`
- `packet_version`
- `packet_hash`
- `invariant_refs`
- `namespace_candidate`
- `signature_candidates`
- `module_candidate`
- `imports_candidate`
- `minimal_probe_plan`

Recommended fields:
- `declaration_name_candidates`
- `dependency_candidates`
- `target_surface`
- `anchor_refs`

Example:

```json
{
  "id": "packet_translation_lineage_9f22d1c1_rev1",
  "kind": "TranslationPacket",
  "status": "probe_ready",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260424T091500Z_0012",
  "created_by_agent": "translation-bee",
  "agent_role": "translation",
  "backend": "codex-cli",
  "created_at": "2026-04-24T09:15:00Z",
  "updated_at": "2026-04-24T09:15:00Z",
  "invariant_refs": [
    {"ref": "hive_invariants/invariant_lineage_9f22d1c1_2_3e91", "kind": "InvariantDraft"}
  ],
  "namespace_candidate": "InfoGeometry.Hive",
  "signature_candidates": [
    "theorem splitStepAdmissibility : Preconditions -> LegalizableCandidate",
    "theorem splitStepAdmissibility_of_anchor : AnchorDiscipline -> AdmissionReady"
  ],
  "module_candidate": "InfoGeometry/Hive/SplitStep",
  "imports_candidate": [
    "InfoGeometry.Hive.PacketAuthority",
    "InfoGeometry.Hive.AnchorDiscipline"
  ],
  "minimal_probe_plan": {
    "probe_kind": "token_free_repl_then_targeted_build",
    "steps": [
      "check imports",
      "check namespace availability",
      "stub theorem signature",
      "run targeted build surface"
    ]
  },
  "declaration_name_candidates": ["splitStepAdmissibility", "splitStepAdmissibility_of_anchor"],
  "dependency_candidates": ["PacketAuthority", "AnchorDiscipline"]
}
```

Validation notes:
- `signature_candidates` must be a non-empty array
- `minimal_probe_plan` must be operational, not just aspirational prose
- should not mark `promotion_allowed = true`

## 7.3 `ResiduePacket`

Purpose:
- structured retained failure or unresolved tension
- return route into future cultivation, not deletion

Required fields:
- shared envelope
- `kind = "ResiduePacket"`
- `packet_version`
- `packet_hash`
- `failure_refs`
- `failure_class`
- `stage`
- `recovery_hint`
- `return_route`

Recommended fields:
- `recoverability`
- `next_cultivation_hint`
- `blocked_packet_refs`
- `anchor_gap_summary`

Suggested `stage`:
- `seed_intake`
- `jung_excitation`
- `resonance_clustering`
- `pauli_differentiation`
- `invariant_extraction`
- `packet_legalization`
- `translation`
- `formal_probe`
- `build`
- `audit`
- `promotion`

Example:

```json
{
  "id": "packet_residue_lineage_9f22d1c1_rev1",
  "kind": "ResiduePacket",
  "status": "active",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260424T092500Z_1012",
  "created_by_agent": "pauli-bee-1",
  "agent_role": "pauli",
  "backend": "codex-cli",
  "created_at": "2026-04-24T09:25:00Z",
  "updated_at": "2026-04-24T09:25:00Z",
  "failure_refs": [
    {"ref": "hive_packets/packet_theorem_candidate_lineage_9f22d1c1_rev1", "kind": "TheoremCandidatePacket"},
    {"ref": "hive_pauli_critiques/critique_lineage_9f22d1c1_2_a411", "kind": "PauliCritique"}
  ],
  "failure_class": "repo_anchor_missing",
  "stage": "packet_legalization",
  "recovery_hint": "Perform SCC-first retrieval and raw witness descent before relaunching translation.",
  "return_route": "return_to_residue",
  "recoverability": "high",
  "next_cultivation_hint": "Revive after anchor edges exist into faithful raw/overlay layers.",
  "anchor_gap_summary": "No durable anchor into raw_info_nodes or topology_overlay was attached."
}
```

Validation notes:
- failure is structured return, not deletion
- every residue should remain revivable through lineage and edge connections

## 8. Authority-gate output schemas

## 8.1 `LeanVerificationPacket`

Purpose:
- Records the result of a Lean verification attempt (REPL probe or build).
- Authority: `lean_checked`.

Required fields:
- shared envelope
- `kind = "LeanVerificationPacket"`
- `packet_version`
- `packet_hash`
- `execution_intent_ref`
- `execution_allowed` (boolean)
- `verification_key`
- `verification_outcome` (`passed`, `failed`, `not_executed`, `skipped`)
- `kernel_summary`
- `proof_status` (`pending`, `verified`, `blocked`, `rejected`)

Recommended fields:
- `proof_code`
- `error_excerpt`
- `lean_output`

Example:

```json
{
  "id": "packet_lean_verification_lineage_9f22d1c1_rev1",
  "kind": "LeanVerificationPacket",
  "status": "gated",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260522T100000Z_abcd",
  "created_by_agent": "verification-bee",
  "agent_role": "verification",
  "backend": "lean-cli",
  "created_at": "2026-05-22T10:00:00Z",
  "updated_at": "2026-05-22T10:00:00Z",
  "execution_intent_ref": {
    "ref": "hive_packets/packet_execution_intent_lineage_9f22d1c1_rev1",
    "kind": "ExecutionIntentPacket"
  },
  "execution_allowed": true,
  "verification_key": "vkey_split_step_001",
  "verification_outcome": "passed",
  "kernel_summary": "Theorem splitStepAdmissibility accepted by Lean kernel.",
  "proof_status": "verified",
  "proof_code": "theorem splitStepAdmissibility ... := by ...",
  "authority": "lean_checked",
  "representation_class": "owner",
  "representation_depth": "categorical"
}
```

## 8.2 `BuildPacket`

Purpose:
- Records the result of a project-wide or targeted build verification.
- Authority: `build_checked`.

Required fields:
- shared envelope
- `kind = "BuildPacket"`
- `packet_version`
- `packet_hash`
- `lean_verification_ref`
- `build_key`
- `build_command`
- `build_exit_code` (integer)
- `build_success` (boolean)

Recommended fields:
- `build_output_excerpt`
- `build_artifacts`

Example:

```json
{
  "id": "packet_build_lineage_9f22d1c1_rev1",
  "kind": "BuildPacket",
  "status": "passed",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260522T101000Z_efgh",
  "created_by_agent": "build-bee",
  "agent_role": "build",
  "backend": "lake-cli",
  "created_at": "2026-05-22T10:10:00Z",
  "updated_at": "2026-05-22T10:10:00Z",
  "lean_verification_ref": {
    "ref": "hive_packets/packet_lean_verification_lineage_9f22d1c1_rev1",
    "kind": "LeanVerificationPacket"
  },
  "build_key": "build_split_step_001",
  "build_command": "lake build InfoGeometry.Hive.SplitStep",
  "build_exit_code": 0,
  "build_success": true,
  "build_output_excerpt": "Building InfoGeometry.Hive.SplitStep... success.",
  "authority": "build_checked",
  "representation_class": "owner",
  "representation_depth": "categorical"
}
```

## 8.3 `AuditPacket`

Purpose:
- Records the result of a human or agentic audit gate.
- Authority: `audit_checked`.

Required fields:
- shared envelope
- `kind = "AuditPacket"`
- `packet_version`
- `packet_hash`
- `build_ref`
- `audit_key`
- `audit_scope` (`correctness`, `safety`, `build`, `promotion`)
- `audit_findings` (array of strings)
- `audit_outcome` (`approved`, `rejected`, `deferred`)
- `evidence_summary`

Example:

```json
{
  "id": "packet_audit_lineage_9f22d1c1_rev1",
  "kind": "AuditPacket",
  "status": "approved",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260522T102000Z_ijkl",
  "created_by_agent": "audit-bee",
  "agent_role": "auditor",
  "backend": "local",
  "created_at": "2026-05-22T10:20:00Z",
  "updated_at": "2026-05-22T10:20:00Z",
  "build_ref": {
    "ref": "hive_packets/packet_build_lineage_9f22d1c1_rev1",
    "kind": "BuildPacket"
  },
  "audit_key": "audit_split_step_001",
  "audit_scope": "promotion",
  "audit_findings": [
    "Formal target matches symbolic intent.",
    "Repo anchors are verified in Arango.",
    "Lean proof is complete and checked."
  ],
  "audit_outcome": "approved",
  "evidence_summary": "Full lineage and verification trail confirmed.",
  "authority": "audit_checked",
  "representation_class": "owner",
  "representation_depth": "categorical"
}
```

## 8.4 `PromotionDecisionPacket`

Purpose:
- Records the final decision to promote a packet to a higher status or different repository layer.
- Authority: `promoted`.

Required fields:
- shared envelope
- `kind = "PromotionDecisionPacket"`
- `packet_version`
- `packet_hash`
- `audit_ref`
- `promotion_key`
- `decision` (`approved`, `deferred`, `rejected`)
- `decision_rationale`

Recommended fields:
- `promotion_targets`
- `conditions`

Example:

```json
{
  "id": "packet_promotion_decision_lineage_9f22d1c1_rev1",
  "kind": "PromotionDecisionPacket",
  "status": "promoted",
  "lineage_id": "lineage_9f22d1c1",
  "revision": 1,
  "packet_version": "1.0.0",
  "packet_hash": "sha256:...",
  "origin_run_id": "run_20260522T103000Z_mnop",
  "created_by_agent": "promotion-bee",
  "agent_role": "orchestrator",
  "backend": "local",
  "created_at": "2026-05-22T10:30:00Z",
  "updated_at": "2026-05-22T10:30:00Z",
  "audit_ref": {
    "ref": "hive_packets/packet_audit_lineage_9f22d1c1_rev1",
    "kind": "AuditPacket"
  },
  "promotion_key": "promo_split_step_001",
  "decision": "approved",
  "decision_rationale": "All verification and audit gates passed successfully.",
  "promotion_targets": ["canonical_layer", "alexandria_index"],
  "authority": "promoted",
  "representation_class": "owner",
  "representation_depth": "categorical"
}
```

## 9. Supporting packet shapes (recommended)

These are not the main focus of this document, but they are part of the repo doctrine and should remain compatible.

## 9.1 `RetrievalHypothesisPacket`

Required payload:
- `query_text`
- `seed_refs`
- `candidate_anchor_refs`
- `graph_mode`
- `retrieval_summary`
- `promotion_allowed = false`

## 9.2 `CritiquePacket`

Required payload:
- `target_refs`
- `critique_summary`
- `distinctions`
- `risk_flags`
- `admissibility_recommendation`

## 9.3 `ExecutionIntentPacket`

Required payload:
- `target_refs`
- `intended_actions`
- `required_tools`
- `required_gates`
- `mutation_scope`
- `execution_allowed`

## 10. Core invariants

## 10.1 Layering invariants
- Hive packet objects must not replace faithful Lean/Arango graph objects.
- Symbolic or packet objects may anchor into raw/projection/topology layers through anchor refs and anchor edges.
- Absence from a retrieval projection is not proof of semantic absence.

## 10.2 Legalization invariants
- `SymbolicSeed`, `FormulationVariant`, `ResonanceCluster`, `PauliCritique`, and `InvariantDraft` are pre-legal objects.
- Only legal packet kinds should cross legalization boundaries.
- Packet hashes must change when semantic content changes materially.

## 10.3 Authority invariants
- No object in this document alone certifies theorem truth.
- A `TheoremCandidatePacket` is intent/legalization, not evidence.
- A `TranslationPacket` is a Lean-facing proposal, not proof.
- A `ResiduePacket` preserves failure pressure; it does not erase lineage.

## 10.4 Revision invariants
- `revision` starts at `1`.
- Semantic replacement should create a new revision or new object.
- Older superseded objects should remain connected by lineage edges.

## 11. Arango storage mapping

Recommended collection mapping:
- `SymbolicSeed` -> `hive_symbolic_seeds`
- `FormulationVariant` -> `hive_formulation_variants`
- `ResonanceCluster` -> `hive_resonance_clusters`
- `PauliCritique` -> `hive_pauli_critiques`
- `InvariantDraft` -> `hive_invariants`
- `TheoremCandidatePacket` -> `hive_packets`
- `TranslationPacket` -> `hive_packets`
- `ResiduePacket` -> `hive_packets` and/or `hive_failure_residues` mirror, depending on implementation choice
- `LeanVerificationPacket` -> `hive_packets`
- `BuildPacket` -> `hive_packets`
- `AuditPacket` -> `hive_packets`
- `PromotionDecisionPacket` -> `hive_packets`

Recommended cross-layer anchor edge usage:
- `anchors_to_decl`
- `anchors_to_raw_node`
- `anchors_to_scc`
- `anchors_to_retrieval_node`
- `validated_by_probe`
- `validated_by_build`
- `validated_by_audit`

## 12. Minimal validator checklist

A future schema validator should check at least:

1. shared envelope present
2. `kind` matches collection family
3. `status` in allowed vocabulary
4. `revision >= 1`
5. timestamps parse as UTC ISO-8601
6. required payload fields present for the specific kind
7. packet kinds include `packet_version` and `packet_hash`
8. `TheoremCandidatePacket` has non-empty:
   - `symbolic_origin_refs`
   - `formal_target`
   - `novelty_defense`
9. `TranslationPacket` has non-empty:
   - `invariant_refs`
   - `signature_candidates`
   - `minimal_probe_plan`
10. `ResiduePacket` has non-empty:
   - `failure_refs`
   - `failure_class`
   - `stage`
   - `recovery_hint`
11. `LeanVerificationPacket`, `BuildPacket`, `AuditPacket`, `PromotionDecisionPacket` carry required authority metadata
12. pre-legal symbolic objects do not claim authority-gate success directly

## 13. Compressed law

```text
Seeds carry pressure.
Variants spread it.
Clusters stabilize it.
Critiques sharpen it.
Invariants condense it.
Packets legalize it.
Lean-facing translations probe it.
Residues preserve what fails.
Lean/build/audit decide what survives.
Promotion seals the morphism.
```

## 14. Next implementation step

The natural next move after this document is:
- implement JSON validators for these schemas
- add packet writers/readers under `tools/infra/`
- wire packet writes into the bounded Hive runner and Arango ingestion layer
- add anchor-edge attachment routines before expensive formalization
