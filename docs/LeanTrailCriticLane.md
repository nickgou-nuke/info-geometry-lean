# LeanTrail Critic Lane

## Purpose

The Critic Lane formalizes a safer role for LLM programmer agents inside the LeanTrail toolchain.

LLMs are not trusted authors of formal mathematics. They are useful critics over a structured evidence space: they can identify suspicious names, docstring/type mismatches, proof-shape inflation, hidden proof debt, orphan-genuine components, and likely bridge obligations. Lean remains the only semantic authority.

## Core policy

```text
LLM creates hypotheses about problems.
LeanTrail stores and ranks them.
Humans review them.
Lean kernel validates any resulting code.
```

The Critic Lane is review-only:

```text
No source edits.
No automatic proof generation.
No deletion authorization.
No unvalidated patch suggestions.
No bypass of lake build or kernel checks.
```

## Relationship to Honest Sorry

The Critic Lane assumes the v1.3 Honest Sorry protocol:

```text
explicit sorry
  honest proof debt; track and triage

transitive sorry
  quarantined dependency; expose blocker path

laundered sorry / local axiom / opaque stand-in
  unsafe closure; reject or quarantine
```

This avoids the bad incentive where an agent invents synonyms for `sorry` to satisfy a “no sorry” rule. Explicit `sorry` is preferable to hidden proof debt.

## Evidence inputs

The deterministic generator consumes:

```text
artifacts/leantrail/graph_snapshot.vacuity.json
artifacts/leantrail/proof_hole_packets.jsonl
artifacts/leantrail/bridge_packets.jsonl
artifacts/leantrail/alignment_packets.jsonl
```

Optional future inputs:

```text
artifacts/leantrail/hodge/*.json
artifacts/leantrail/graphrag/*.json
artifacts/leantrail/vacuity/certificates/*.json
```

## Outputs

```text
artifacts/leantrail/critic_packets.jsonl
artifacts/leantrail/critic_report.json
artifacts/leantrail/critic_report.md
artifacts/leantrail/critic_prompts.jsonl
artifacts/leantrail/graph_snapshot.critic.json
```

`critic_packets.jsonl` contains bounded audit objects. These are not patches.

## Critic kinds

### `proof_shape_name_mismatch`

A declaration name suggests a substantive theorem or bridge, but `attrs.vacuity.role` is `fake_transport`, `pure_conductor`, or `dead_socket`.

### `docstring_statement_mismatch`

The documentation claims strong mathematical content, but the local proof-shape audit is weak or transport-only.

### `honest_sorry_triage`

Visible proof debt. Route it to proof-hole triage, not surgery.

### `obfuscation_suspicion`

Possible hidden proof debt: local axioms, opaque placeholders, certificate sockets, witness fields, readback fields, or renamed admit mechanisms.

### `orphan_genuine_review`

Dense valid mathematics without a protected-root path. Preserve and bridge/expose it; do not delete.

### `axiomatic_frontier_review`

A theorem region supported by axioms/opaque boundaries. Quarantine or bridge it; do not vacuum it.

### `alignment_candidate_review`

A Hodge/de Bruijn/structural overlap that may indicate a bridge candidate. Any route must become a Lean kernel obligation.

### `educational_alias_protection`

GraphRAG or documentation suggests a wrapper may be pedagogical. Destructive surgery should be blocked or manual.

## Pipeline placement

```text
Phase A:
  Lean biopsy emits vacuity / contamination / source_patch.

Phase B:
  LeanTrail ingest merges attrs.

Phase B.5:
  critic_packets.py generates deterministic critic tasks.

Phase B.6:
  optional LLM critic reviews bounded prompt packets.

Phase C:
  surgery_plan.py uses critic state as a policy input:
    high-severity critic blocks deletion;
    educational alias protects;
    obfuscation suspicion quarantines;
    bridge suggestion enriches bridge_packets.

Phase D/E:
  unchanged; only Lean-verified patches can apply.
```

## LLM prompt contract

The optional prompt builder emits this role contract:

```text
You may identify problems.
You may propose review actions.
You may recommend bridge obligations.
You may rank proof holes.
You may not modify source.
You may not certify theorem truth.
You may not hide proof debt.
```

Responses must be schema-validated before ingestion.

## Metrics

Measure critic value using:

```text
confirmed_critic_packets
false_positive_rate
bridge_conversion_rate
proof_hole_resolution_rate
obfuscation_detection_rate
semantic_inflation_detection_rate
educational_alias_preservation_rate
```

Do not measure the critic by generated code volume.

## UI recommendation

Use two surfaces:

```text
Trouble Tickets:
  sortable workflow queue for manual_refactor_required and critic packets.

Graph overlays:
  contextual markers only; not the execution surface.
```

Alignment packets should open in the existing 4-pane Compare view: source declaration, target declaration, normalized skeleton diff, and kernel obligation.
