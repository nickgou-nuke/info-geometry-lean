# Gromov–Jaynes Probability Note

Status: reference memory / interpretive note.

This file is **not** a theorem source and does **not** validate historical or philosophical claims. It only records the repo-native finite counting surfaces that match a Gromov/Jaynes-style reading of probability.

## Repo-owned Lean surfaces

- `lean/InfoGeometry/GromovProbability.lean`
- `lean/InfoGeometry/Probability/GromovFiniteCounting.lean`
- `lean/InfoGeometry/GromovJaynesProbability.lean`
- `lean/InfoGeometry/Canonical/CountProbabilityState.lean`

## Theorem-safe reading

The live Lean content supports:

- finite counting as the primary object
- projection bounds on finite subsets
- product-state counting by cardinality
- inductive permutation counting
- normalization as a derived rational ratio

In particular, the following theorem names exist in the repo:

- `gromov_measure_disjoint_union`
- `projection_bound`
- `perm_count_pos`
- `normalization_secondary`
- `product_state_measure`
- `count_is_inductive`
- `sum_state_count`
- `secondary_normalization_bound`

## Open debt

Still not formalized here:

- symmetric-group quotient / concentration as a full theorem package
- any Stirling-style asymptotic bound
- any analytic law-of-large-numbers claim
- any claim that external lectures “validate” the Lean architecture

## Reading note

Treat external lecture transcripts/notes as **background interpretation only**. The proof authority remains the Lean files above.
