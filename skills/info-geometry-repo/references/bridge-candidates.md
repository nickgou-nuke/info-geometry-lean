# Bridge Candidates

This note is a report-only frontier packet derived from the current trusted
`Skynet v2` semantic frontier.

It is not a proof artifact.

The purpose is to pin the first small bridge lemmas suggested by the current
frontier, ranked with debt-aware scheduling signals.

## Trusted Graph Context

Current trusted semantic graph facts:

- `Skynet v2` graph:
  - `143` nodes
  - `753` edges
  - `378` cross-module edges
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

This candidate is generated directly from the frontier row `InfoGeometry.KK.index_bridge_spectral` in `lean/InfoGeometry/KK/KasparovCycle.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.043428` / `0.058428`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.KK.index_bridge_spectral`
- `lean/InfoGeometry/KK/KasparovCycle.lean`
- `frontier rawScore: 0.043428`
- `frontier score: 0.058428`

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

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.066003` / `0.051003`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_modularCliffordTransport_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.066003`
- `frontier score: 0.051003`

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

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/GrandSynthesis.lean`. It is intended to derive a nontrivial equality that feeds the frontier declaration. The seed-to-frontier link kinds currently visible are `primaryDep`. The current raw/priority scores are `0.063047` / `0.048047`, with module status `mixed_capstone_surface` and adjustments `unification_status_adjustment -0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.KK.KasparovCycle.analyticalIndex`
- `InfoGeometry.Canonical.GrandSynthesis.kk_analyticalIndex_eq_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/GrandSynthesis.lean`
- `frontier rawScore: 0.063047`
- `frontier score: 0.048047`

`risk level`

`medium`

## Candidate 4

`name`

`AutoCandidate.chiralSliceIsoAlong_of_noZeroEigenCrossing_from_analyticalIndex_4`

`Lean-style signature sketch`

```lean
theorem auto_chiralSliceIsoAlong_of_noZeroEigenCrossing_from_seed_4
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
    -- intended role: bridge theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing` in `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`. It is intended to insert a small bridge theorem feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.015689` / `0.030689`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.AnalyticalIndex.chiralSliceIsoAlong_of_noZeroEigenCrossing`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
- `frontier rawScore: 0.015689`
- `frontier score: 0.030689`
- `module status: classical_adjacent_model`

`risk level`

`low`

## Candidate 5

`name`

`AutoCandidate.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses_from_analyticalIndex_5`

`Lean-style signature sketch`

```lean
theorem auto_sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses_from_seed_5
    -- seed anchor: `KasparovCycle.analyticalIndex`
    -- frontier target: `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
    -- intended role: transport / invariance theorem
    (... local hypotheses specialized to the target declaration ...)
    : (... direct transport / invariance / closure statement feeding the frontier ...) := by
  -- quarantine sketch only
```

`why this closes a real frontier edge`

This candidate is generated directly from the frontier row `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses` in `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`. It is intended to close an invariance step feeding the frontier declaration. The seed-to-frontier link kinds currently visible are `-`. The current raw/priority scores are `0.014499` / `0.029499`, with module status `classical_adjacent_model` and adjustments `unification_status_adjustment +0.015`.

`likely proof ingredients already present in repo`

- `InfoGeometry.Canonical.AnalyticalIndex.sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses`
- `lean/InfoGeometry/Canonical/AnalyticalIndex.lean`
- `frontier rawScore: 0.014499`
- `frontier score: 0.029499`
- `module status: classical_adjacent_model`

`risk level`

`low`

