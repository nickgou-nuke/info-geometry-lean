# Causal balance: constructive alternative

The source `Probability/CausalDetailedBalanceObstruction.lean` proves that a
lower-triangular row-stochastic matrix with positive-weight detailed balance is
the identity. Preserve that theorem; do not demand all three properties from a
nontrivial transition matrix.

The alternative uses `Physics/FiniteStationaryCurrent.weightedSelfPart`, already
defined as half the sum of a matrix and its weighted adjoint. Existing lemmas
prove its weighted self-adjointness and recovery of the original matrix by
adding the weighted skew part. `Probability/FiniteMarkovWeightedAdjoint` owns
the matrix-valued `DetailedBalance` predicate. The new module proves
nonnegativity, row sums, stationarity, and detailed balance for that existing
construction. The exact flux identity specifies what changes: directed fluxes
are averaged. The proved zero-entry equivalence states that an averaged entry
vanishes exactly when both directed entries vanish. This does not retain a triangular mask or claim that every
directed chain has a strictly positive stationary distribution.

Carrier and conventions: `Matrix n n ℝ`, finite state type `n`, row sums one,
stationarity `∑ i, π i * P i j = π j`, positive `π` for nonnegativity and
nonzero `π` for algebraic identities. No normalization of `π` is necessary.
No new hypothesis structure or renamed construction is introduced.

Search scope: recursive Lean searches for detailed balance, reversibilization,
weighted adjoints and `weightedSelfPart`; direct inspection of the above owners
and `Probability/FiniteResamplingGap`. The latter already provides a concrete
resampling family with stochasticity, stationarity and detailed balance.
These searches establish the local integration context, not repository-wide
absence of other formulations.

Verification: the locked build of
`InfoGeometry.Probability.CausalDetailedBalanceObstructionAudit` passed (8930
jobs), including the new audit module. All eight new theorems report only
`propext`, `Classical.choice`, and `Quot.sound`. The new module has no warnings;
existing dependency warnings remain. OpenGauss static screening reports zero
traps and the semantic-vacuity scan reports zero findings. These automated
checks do not replace independent OpenGauss semantic audit and QA, which remain
pending. The full repository counterexample-realignment goal remains open.
