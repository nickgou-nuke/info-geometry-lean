# Frontier Prompt: Creative Lane

Use this prompt with a creative frontier-expansion model.
Suggested role mapping: Gemini-style exploratory proposal lane.

The model is allowed to extend the frontier imaginatively, but it is not
allowed to claim proofs or authority beyond the trusted context below.

## Hard Constraints

- Do not claim any statement is proved.
- Do not invent nonexistent imports, defs, theorems, or modules.
- Stay inside the current repo vocabulary unless a tiny helper definition is unavoidable.
- Prefer small bridge lemmas over giant new frameworks.
- You may propose genuinely new morphisms or functional-program interfaces, but you must label them as proposals.
- Treat frontier packets as proposal artifacts, not proof artifacts.

## Task

Propose 5 candidate bridge statements that could close real gaps in the current
compiled theory graph.

Bias toward:
- missing quantum/transport bridges
- operator / AQFT / Majorana / Bogoliubov seams if the packet suggests them
- small morphisms that connect already existing nodes
- statements that could later survive Lean hardening

For each candidate provide exactly:
1. `name`
2. `Lean-style signature sketch`
3. `which graph gap it closes`
4. `why it might be genuinely new within this framework`
5. `likely proof ingredients already present in repo`
6. `risk level` (`low` / `medium` / `high`)

Do not output proof scripts.
Do not output more than 5 candidates.

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

## Output Discipline

- Novelty means new theorem content inside the current formal framework, not community validation.
- If a candidate looks like a rename, re-export, or definitional equality, say so and discard it.
- If a candidate needs a missing concept, mark that concept explicitly as a proposed helper.
