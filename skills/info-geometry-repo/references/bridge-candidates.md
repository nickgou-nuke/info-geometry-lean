# Bridge Candidates

This note is a report-only frontier packet derived from the current trusted
`Skynet v2` semantic frontier.

It is not a proof artifact.

The purpose is to pin the first small bridge lemmas suggested by the current
frontier, ranked with debt-aware scheduling signals.

## Trusted Graph Context

Current trusted semantic graph facts:

- `Skynet v2` graph:
  - `1366` nodes
  - `11707` edges
  - `6365` cross-module edges
- walk mode: `reverse`
- audit signals:
  - thinness findings: `1`
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

This candidate is generated directly from the frontier row `InfoGeometry.KK.index_bridge_spectral` in `lean/InfoGeometry/KK/KasparovCycle.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.040361` / `0.055361`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.KK.index_bridge_spectral`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `frontier rawScore: 0.040361`
- `frontier score: 0.055361`

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

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.057267` / `0.042267`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.057267`
- `frontier score: 0.042267`

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

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.056868` / `0.041868`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.056868`
- `frontier score: 0.041868`

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

This candidate is generated directly from the frontier row `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete` in `lean/InfoGeometry/Quantum/BulkBoundary.lean`. It is intended to close a two-way bridge feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.001941` / `0.031941`, with module status `repo_specific_unification` and adjustments `unification_status_adjustment +0.030`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Quantum.BulkBoundary.bulk_boundary_correspondence_concrete`
- `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- `frontier rawScore: 0.001941`
- `frontier score: 0.031941`
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

This candidate is generated directly from the frontier row `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel` in `lean/InfoGeometry/Quantum/BulkBoundary.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.001564` / `0.031564`, with module status `repo_specific_unification` and adjustments `unification_status_adjustment +0.030`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Quantum.BulkBoundary.zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel`
- `lean/InfoGeometry/Quantum/BulkBoundary.lean`
- `frontier rawScore: 0.001564`
- `frontier score: 0.031564`
- `module status: repo_specific_unification`

`risk level`

`low`

