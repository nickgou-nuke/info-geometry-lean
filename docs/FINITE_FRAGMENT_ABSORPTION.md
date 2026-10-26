# Finite fragmentation absorption and quantitative response evidence

## Scope and dependency base

Additive follow-up to PR #221 at `756646098b235aa8b8a0111fea552d921634afd5`,
stacked on `feat/ms-experimental-evidence`. Existing owners, dependency pins,
umbrella imports, main, and the parent branch are not changed.

The dependency order is:

strict rank support -> power support -> transient nilpotence -> exact absorbing
projection -> finite fundamental inverse -> quantitative response bounds ->
conditional experimental identification.

The existing `FragmentationDAG`, `StochasticGrammar`, `absorbingCompletion`,
`SignedNetwork.RankedDAGResolvent.finiteGreen`, `UniformErrorBound`, and
`MultiEnergyForwardModel` are reused. There is no duplicate inverse predicate,
Markov carrier, chemistry-equivalence predicate, or global matrix-norm instance.

## Modules

- `Algebra.RankedMatrixPowers`: a generic semiring support theorem for native
  matrix powers, quantitative rank drop, and the explicit finite rank horizon.
- `MassSpectrometry.FiniteFragmentAbsorption`: the existing transient matrix and
  Option-indexed completion, all four power blocks, exact row normalization,
  state-local absorption, absorbing projection laws, and finite stabilization.
- `MassSpectrometry.FragmentationGreenResponse`: reuse of the existing finite
  Green sum and two inverse laws; horizon independence, a native unit, unique
  response, nonnegativity, substochastic powers, and row-mass bounds.
- `MassSpectrometry.FragmentationOccupancyBounds`: the rank-local finite row
  bound and `1 <= occupancyPotential u <= rank u + 1`, plus response positivity.
- `MassSpectrometry.FragmentationResponseStability`: maximum-absolute-row-sum
  matrix norm bounds, noncommutative resolvent identity, kernel and reward
  perturbation estimates, and a constructed uniform certificate on bounded inputs.
- `MassSpectrometry.FragmentationResponseEvidence`: condition- and candidate-
  dependent response models, their derived uniform numerical-error certificate,
  and direct application of #221's robust identification theorem.
- `MassSpectrometry.FiniteFragmentAbsorptionAudit`: exact non-diagonal chain
  fixtures, sharp final-step boundary, persistent absorption row, positive
  self-loop counterexample, and ten API checks.

## Exact theorem contracts

For a strict natural-valued rank, a nonzero `(K^m) u v` implies
`rank v + m <= rank u`. Thus `K^N = 0` for every strict bound `rank u < N`.
The automatic horizon is `Finset.univ.sup rank + 1`. It is one on the empty
original-state type, and is not asserted to be the minimal exponent. Rank gaps
or offsets can make it loose. A terminal original state requires one final
transition to the absorber even when its rank is zero.

The completion satisfies

```
Khat^m (some u) (some v) = (K^m) u v
Khat^m (some u) none     = 1 - sum_v (K^m) u v
Khat^m none none         = 1
Khat^m none (some v)     = 0.
```

Its eventual value is the idempotent matrix Pi with absorbing column all ones
and every original-state column zero. Both `Khat * Pi = Pi` and `Pi * Khat = Pi`
hold, and `Khat^(N+t) = Pi` at the automatic horizon for every natural t. Khat
is never nilpotent: its absorbing row persists.

The finite sum F = sum_(j<N) K^j has `(I-K)*F = F*(I-K) = I` and is independent
of which valid cutoff is used. The equation `(I-K) x = g`, equivalently
`x = g + K x`, has unique solution `F *v g`. The inversion is for the original
transient block, not for the singular completed generator `I-Khat`.

For two possibly different strict ranked grammars on the same original index
set, with horizons N and M:

```
F_K - F_L = F_K * (K-L) * F_L
||F_K||_infinity <= N
||F_K-F_L||_infinity <= N*M*||K-L||_infinity
||F_K g-F_L h||_infinity <=
  N*||g-h||_infinity + N*M*||K-L||_infinity*||h||_infinity.
```

These use `open scoped Matrix.Norms.Operator`, Mathlib's actual infinity
operator norm, not an elementwise matrix norm. Reward vectors use the native
finite-product supremum norm. An NNReal bound delta on kernel error and bound
C on reward amplitude construct `UniformErrorBound` with error N*M*delta*C.
Both horizons and the transition-error bound remain explicit.

`responseModelError` permits a different ranked graph and grammar at every
(condition, candidate). With uniform horizon bounds N,M, kernel bound delta,
and reward bound C, the corresponding approximate response model deviates by
at most N*M*delta*C. The existing robust identification theorem is then applied
with margin strictly greater than `2*(epsilon + N*M*delta*C)`. The conclusion
is the supplied chemical setoid relation, not equality of candidate labels.
Separation of the reference signatures remains an explicit hypothesis.

## Verification and nonclaims

Acceptance requires the dedicated pinned-toolchain workflow. Its report names
the exact tested merge revision. It compiles the complete selected source
closure and enumerates all declarations owned by the seven new modules,
collecting their axiom dependencies transitively. It does not enumerate every
unreferenced declaration in the old dependency modules or certify the full root
package. No axiom-collector exemption or dependency-pin change is introduced.
The successful artifact and final PR body are the acceptance record; historical
failed attempts are not successful verification evidence.

Exact support is essential. Tiny nonzero self-loops can destroy finite cutoff;
the general family still needs its proved support hypotheses. Numerical
residuals and the supplementary rational tests are not universal refinement
proofs. The norm constant is a safe bound, not an optimal condition number.

The occupancy potential is a finite algebraic quantity. No probability-space
path law, random hitting time, or expectation theorem is constructed. No optimal
transport optimizer, tagged physical quantity redesign, file parser, unit
calibration, isotope table, learned model, or statistically calibrated confidence
level is added. The response observation is a finite vector; an instrument
spectrum interpretation or further readout map needs an explicit adapter and
its own error contract. Additivity lowers direct editing risk, not all regression
or integration risk. No branch is merged by this addition.

## Use

```lean
import InfoGeometry.MassSpectrometry.FragmentationResponseEvidence

open InfoGeometry.MassSpectrometry

#check StochasticGrammar.absorbingCompletion_stabilizes
#check StochasticGrammar.occupancyPotential_bounds
#check StochasticGrammar.response_uniformErrorBound
#check FragmentationResponseEvidence.robust_identification_from_transition_error
```

With root dependencies available:

```sh
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.MassSpectrometry.FiniteFragmentAbsorptionAudit
```
