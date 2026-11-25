## Why

`GaussianBlockSpin.EffectiveForm` already proves the block-spin Gaussian
integral using a vector satisfying the effective-stiffness normal equation.
Repeated or weighted block transformations also need a canonical harmonic
extension, the corresponding precision/covariance identities, and a theorem
that preserves the order of rectangular observation maps under composition.

## Changes

Add a native finite-matrix API over `RCLike` for positive definite fine and
coarse precision matrices `A` and `R`, with arbitrary rectangular `Q`:

\[
H=A+Q^\dagger RQ,\qquad
S^{-1}=R^{-1}+QA^{-1}Q^\dagger,\qquad
E=H^{-1}Q^\dagger R.
\]

The contribution proves positivity, both Woodbury identities, both normal
equations, exact quadratic completion, uniqueness of the canonical minimizer,
and ordered two-stage covariance transport and joint minimization. It does
not require commuting matrices or a coisometric observation map.

`WeightedEffectiveForm` specializes `R` to `α • 1` on real Euclidean spaces.
It identifies the canonical extension with `α • w`, constructs the required
normal-equation solution, and invokes the existing
`integral_blockKernel_mul_gaussian` theorem. The final theorem retains the
existing determinant normalization and reads its exponent as the coarse
precision quadratic form.

`WeightedKernel` adds the normalized density for arbitrary positive-definite
matrix `R`, proves its total mass is one, recovers the scalar density, and
integrates out the fine Gaussian. `WeightedKernelConvolution` proves the
Schur determinant identity and full normalized convolution with ordered
observation map `Q2 * Q1`. No rank or commutativity assumption is added.

The scalar specialization keeps the actual upstream parameter `s` in
`alpha*beta/(beta+s*alpha)`. The weighted-adjoint bridge counts the ratio of
inner-product weights exactly once. An explicit 2-by-2 example has proved
positive-definite precisions and a computed noncommuting inverse-covariance
sandwich.

`WeightedMarkovKernel` turns the normalized density into a native
`ProbabilityTheory.Kernel` with a proved `IsMarkovKernel` instance. It proves
joint measurability, measure/integral readback, and equality of the native
composite kernel with the Gaussian whose parameters are `Q2 * Q1` and
`(R2^-1 + Q2 * R1^-1 * Q2^transpose)^-1`. The KL corollary applies native
Mathlib data processing to two finite measures using the same kernel; for
probability measures this is ordinary relative-entropy monotonicity.

`ReflectionPositiveCovariance` proves a finite matrix criterion for preserving
the reflected covariance form on selected test spaces. It requires both a
positive reflected fine form and a positive reflected noise form, reflection
intertwining, and preservation of the selected tests by the dual blocking map.
`WeightedReflectionPositive` applies it to the actual Schur covariance.
A proved 2-by-2 counterexample shows why ordinary covariance positivity and
reflection commutation alone cannot replace those hypotheses.

The three matrix owners are adapted from InfoGeometry commit
`5e6396f87f8d4d0959c88896975b1aaaf3979009`. Apache notices and the separate
license are retained; the new modules depend only on Mathlib and this project.

## Validation

**Verified:** exact destination Lean 4.34.0-rc2 passed in
[run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006800`, at preparation source
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`. The warnings-as-errors build,
**80 fresh axiom reports**, source-hash comparison and unchanged dependency-pin
checks all passed. All fifteen Lean files in this patch match that successful
source inventory. The eight original mathematical Gaussian owners are unchanged.

The patch includes a focused workflow and an audit of 78 public theorems plus
the native kernel definition and its Markov instance (80 reports).
From `LEAN/Libraries/GaussianBlockSpin`, the reproducible commands are:

```sh
lake exe cache get
lake --wfail build GaussianBlockSpin.WeightedCoarseGrainingAudit
lake env lean GaussianBlockSpin/WeightedCoarseGrainingAudit.lean
```

The workflow checks the fresh axiom inventory against only `propext`,
`Classical.choice`, and `Quot.sound`, preserves existing dependency
configuration, and archives its logs. Its scope is this contribution and its
transitive imports. Compiler results and checked source hashes are recorded
separately in the contribution's validation evidence.

## Scope

The operator identities are finite real/complex Hermitian mathematics; the
integration consumer is real finite-dimensional Gaussian integration.
Gauge-fixed coercivity on the physical compressed carrier, holomorphic
complex-symmetric Gaussian continuation, and cutoff-uniform RG estimates
remain separate inputs. The upstream toolchain and dependency pins are
unchanged.

The covariance reflection theorem does not assert a measure-level OS theorem
for arbitrary nonlinear observables. The KL result supplies monotonicity for
a fixed shared kernel; strict contraction, Fisher-divergence bounds and QFT
`c`/`a` theorems require additional arguments. The Gaussian composition formula
assumes fixed matrices at each step.
