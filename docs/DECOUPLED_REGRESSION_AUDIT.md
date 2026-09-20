# Decoupled regression: reuse and verification

## Existing implementation

The supplied mathematical requirements already have owners in this repository:

- `Spectrometry/RobustThermodynamicRegression.lean`: CLR identities and
  positive-semidefinite quadratic energies.
- `Spectrometry/DecoupledThermodynamicRegression.lean`: the zero-sum submodule,
  scale-invariant CLR vectors, two-state partition, logistic weights, additive
  free energy, genuine Fréchet derivatives, quadratic redescending scores,
  retained-support bounds, and a finite dependency partial order.
- `Spectrometry/DecoupledThermodynamics.lean`: independent Bernoulli state
  probabilities, zero cross-line partial derivatives, and temperature limits.

Recursive content searches included hidden/ignored and recovered Lean files;
`/tmp/decoupled-reuse.txt` contains 817 matching lines, including recovery copies.
Further owners cover Bernoulli moments, fluctuations, and Fisher information.
Those additional modules were navigation evidence, not part of this audit's
compilation claim.

No second `clr_coord`, `line_weight`, partition function, or free-energy
definition is introduced. Existing source owners remain unchanged. The new
`Spectrometry/DecoupledRegressionAudit.lean` exercises their actual APIs.

## Mathematical distinctions

The owner proves `HasFDerivAt` and `fderiv` identities, not merely a formal
algebraic rearrangement labelled a derivative. The energy maps have explicitly
supplied derivatives. Cutoff and temperature are fixed parameters in this
calculation; a varying cutoff or temperature needs additional derivative terms.

Weights depend only on their own energy when cutoff and temperature are fixed.
They can still change together when a fitted common parameter changes the
energies. Global Gibbs normalization is a different model, not a mathematical
inconsistency.

The cutoff condition implies only a weight of at least one half, not a weight
near one. The existing margin theorem gives the quantitative bound
`1 / (1 + exp(-margin))` when energy is at most `cutoff - margin * temperature`.
A ten-out-of-eleven regression test applies this bound to a retained subset
without making any assumption about the omitted line's energy.

Finite-temperature weights are strictly between zero and one; they do not
delete lines exactly. The active support is a real-valued sum, not an integer.
The zero-temperature one-sided limits require strict separation from cutoff;
at equality the weight is one half. Lean's value at temperature zero also
equals one half because division is total, so it must not be confused with
the one-sided limit.

Redescending influence is verified for the scalar quadratic residual score,
in both tails. The result is not claimed for arbitrary energy maps solely
because their weights vanish. No physical cause of a particular measured
gamma line's residual, calibrated covariance pseudoinverse, or global
optimization convergence is inferred.

## Causal structure

The existing `ProofDependency` poset has a separate CLR branch. Partition
precedes both logistic weights and free energy; weights and free energy
jointly precede the derivative theorem. Retained support depends on weights,
not on differentiability. Derivative and retention branches are incomparable.
The audit checks these existing poset theorems rather than inventing a false
linear dependency chain.

## Validation environment

Checks run serially under the shared build lock with installed Lean 4.28.x,
cached Mathlib, and isolated outputs. Pinned Lean 4.28.1 remains unavailable;
no toolchain, dependency metadata, existing source owner, or cache is changed.
This is not a pinned-toolchain or full-repository build.

`SvdClrEquivalence`, `RobustThermodynamicRegression`,
`DecoupledThermodynamicRegression`, and `DecoupledThermodynamics` compiled,
followed by the new audit module. All eleven regression examples pass. The
21 audited theorems use only subsets of `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axioms appear in those audits.
Targeted staged-diff whitespace checks pass.
