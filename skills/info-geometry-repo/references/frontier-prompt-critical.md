# Frontier Prompt: Critical Lane

Use this prompt with a critical Lean-aware evaluation model.
Suggested role mapping: ChatGPT/Codex-style formal critique lane.

The model must aggressively reject fake closure, thin bridges, and unsupported
speculation. It is not allowed to promote a candidate just because it sounds
mathematically interesting.

## Hard Constraints

- Treat the creative lane output as untrusted proposal text.
- Reject any candidate that invents unsupported repo vocabulary.
- Reject any candidate whose likely proof is just `rfl`, direct forwarding, or tuple repackaging unless the name is explicitly downgraded.
- Do not claim proof completion.
- Convert only credible candidates into minimal Lean-facing theorem sketches, attack plans, and quarantine-ready concrete sketches when justified.

## Task

Evaluate the creative-lane candidate list against the current trusted frontier
and the current thin-bridge audit.

For each candidate provide exactly:
1. `verdict` (`accept` / `revise` / `reject`)
2. `reason`
3. `minimal Lean-style signature sketch`
4. `proof ingredients already present in repo`
5. `thinness risk` (`definitional` / `forwarder` / `packaging` / `substantive`) 
6. `quarantine recommendation` (`yes` / `no`) 
7. `Lean-ready materialization sketch` (`none` unless the candidate is concrete and recommended for quarantine) 

Then end with:
- `Top 3 survivors`
- `Top 3 rejection reasons`

## Paste Creative Output Below

```text
[PASTE CREATIVE MODEL OUTPUT HERE]
```

## Trusted Frontier Context

```md
# Frontier Prompt Template

Use this template only after refreshing semantic-block exports for the current target modules.

## Prompt skeleton

1. Read the current owner modules and their direct consumers.
2. Separate constructive trunk declarations from shell or packaging declarations.
3. Identify the smallest missing bridge or identification theorem that would lower the frontier pressure.
4. Do not assume historical theorem names from older prompt packs are still live.
5. Report candidate lemmas, likely owner file, direct consumers, and proof ingredients already present in the repo.

## Expected output

- one to three candidate bridge statements;
- exact owner file suggestion for each;
- direct consumer files that would benefit;
- a note whether the candidate is a true lower bridge, a wrapper, or a capstone consequence.
```

## Current Candidate Packet

```md
# Bridge Candidates

This note is a report-only frontier packet derived from the current trusted
`Skynet v2` semantic frontier.

It is not a proof artifact.

The purpose is to pin the first small bridge lemmas suggested by the current
frontier, ranked with debt-aware scheduling signals.

## Trusted Graph Context

Current trusted semantic graph facts:

- `Skynet v2` graph:
  - `1500` nodes
  - `12458` edges
  - `6704` cross-module edges
- walk mode: `reverse`
- audit signals:
  - thinness findings: `0`
  - vacuity findings: `0`
  - surrogate findings: `0`
  - unification modules tracked: `15`
- seed declarations:
  - `KasparovCycle.analyticalIndex`

## Candidate 1

`name`

`AutoCandidate.index_bridge_spectral_from_analyticalIndex_1`

`Lean-style signature sketch`

```lean
theorem auto_index_bridge_spectral_from_seed_1
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.KK.index_bridge_spectral`
    -- intended role: bridge theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.KK.index_bridge_spectral` in `lean/InfoGeometry/KK/KasparovCycle.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.040332` / `0.055332`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.KK.index_bridge_spectral`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `frontier rawScore: 0.040332`
- `frontier score: 0.055332`

`risk level`

`low`

## Candidate 2

`name`

`AutoCandidate.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses_from_analyticalIndex_2`

`Lean-style signature sketch`

```lean
theorem auto_kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses_from_seed_2
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
    -- intended role: transport equality theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.057164` / `0.042164`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.057164`
- `frontier score: 0.042164`

`risk level`

`medium`

## Candidate 3

`name`

`AutoCandidate.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses_from_analyticalIndex_3`

`Lean-style signature sketch`

```lean
theorem auto_kk_analyticalIndex_eq_of_conjugacy_state_hypotheses_from_seed_3
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
    -- intended role: transport equality theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.056797` / `0.041797`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.056797`
- `frontier score: 0.041797`

`risk level`

`medium`

## Candidate 4

`name`

`AutoCandidate.bulk_boundary_correspondence_concrete_from_analyticalIndex_4`

`Lean-style signature sketch`

```lean
theorem auto_bulk_boundary_correspondence_concrete_from_seed_4
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete`
    -- intended role: equivalence / correspondence theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete` in `lean/InfoGeometry/Quantum/BulkBoundary.lean`. It is intended to close a two-way bridge feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.001783` / `0.031783`, with module status `repo_specific_unification` and adjustments `unification_status_adjustment +0.030`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete`
- `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- `frontier rawScore: 0.001783`
- `frontier score: 0.031783`
- `module status: repo_specific_unification`

`risk level`

`low`

## Candidate 5

`name`

`AutoCandidate.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel_from_analyticalIndex_5`

`Lean-style signature sketch`

```lean
theorem auto_zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel_from_seed_5
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel`
    -- intended role: bridge theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel` in `lean/InfoGeometry/Quantum/BulkBoundary.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.001437` / `0.031437`, with module status `repo_specific_unification` and adjustments `unification_status_adjustment +0.030`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel`
- `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- `frontier rawScore: 0.001437`
- `frontier score: 0.031437`
- `module status: repo_specific_unification`

`risk level`

`low`
```

## Current Thin-Bridge Audit

```md
# Bridge Thinness Index

Generated: `2026-04-10 00:07:06`

This report is a heuristic audit of bridge-/launchpad-/interface-facing theorem surfaces that may be mathematically thinner than their names suggest.

## Status
- thin-bridge gate: **PASS**
- interpretation: `FAIL` means at least one targeted theorem currently looks like a definitional identity

## Counts
- total tracked findings: **5**
- definitional identity findings: **0**
- direct forwarder findings: **2**
- underscore-hypothesis findings: **3**
- package/orchestration findings: **0**

## Queue
- `medium` `underscore_hypothesis` `moorePenroseRightProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80`
- `medium` `underscore_hypothesis` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95`
- `medium` `underscore_hypothesis` `drazinProjection_ne_one_of_hasZeroMode` at `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109`
- `medium` `direct_forwarder` `bottStep_headNullMinus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60`
- `medium` `direct_forwarder` `bottStep_headNullPlus` at `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68`

## Findings
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:80` `moorePenroseRightProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:95` `moorePenroseLeftProjector_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hMP`
- `lean/InfoGeometry/Canonical/BulkBoundaryRegularizationBridge.lean:109` `drazinProjection_ne_one_of_hasZeroMode` [medium]
  declaration head contains underscore-prefixed hypotheses: `_hD`
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:60` `bottStep_headNullMinus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder
- `lean/InfoGeometry/Canonical/ClNNBottBridge.lean:68` `bottStep_headNullPlus` [medium]
  proof body is a `simpa ... using bottStep_headPair` forwarder

## Policy
- this is a heuristic syntax audit, not a proof oracle
- `rfl`/direct-forward/package findings are review targets, not automatic verdicts of invalid mathematics
- the purpose is to keep bridge names aligned with actual proof depth
```

## Review Discipline

- Prefer candidates that can become small insertable lemmas.
- Downgrade grand names if the likely proof is only structural packaging.
- If a candidate survives, keep it small enough for quarantine first and canonical promotion later.
- A materialization sketch must be compilable Lean syntax in the current repo vocabulary; it may be a small quarantine wrapper over already existing theorems.
