# Weighted Gaussian coarse-graining contribution

## Source provenance and destination

Adapted from `nickgou-nuke/info-geometry-lean` at
`5e6396f87f8d4d0959c88896975b1aaaf3979009`:
`OperatorAlgebra/PositiveCoarseGraining`, `CoarseGrainingVariational`, and
`CoarseGrainingComposition`. Apache-2.0 notices and the license are retained.
The destination is the existing standalone `LEAN/Libraries/GaussianBlockSpin`
project. Its existing dependency and toolchain pins remain unchanged.

The concrete use is the Gaussian RG step with fine field covariance `A^-1`
and observation `y = Q x + eta`, where the independent Gaussian noise has
covariance `R^-1`. The library provides its normalized transition law,
effective coarse covariance, quadratic conditional minimizer and composition.
These results can discharge the finite Gaussian part of a larger RG argument
once its actual matrices and inner-product conventions are identified.

## Exact contract

For arbitrary finite fine, intermediate, and coarse index types and native
`RCLike` matrix coefficients, with arbitrary rectangular observation matrices,
construct the conditioned fine precision, coarse precision/covariance, and
harmonic extension. Under positive definiteness of each precision, prove
positivity, both Woodbury identities, both normal equations, exact quadratic
completion, unique minimizers, and ordered two-stage covariance composition.
No commutation, coisometry, or diagonalization hypothesis is introduced.

For real Euclidean spaces, prove that coarse weight `α • 1` specializes exactly
to `GaussianBlockSpin.effStiffness`. Its canonical harmonic extension equals
`α • w` when `effStiffness α H Q w = adjoint Q ψ`. Construct the normal-equation
solution canonically and consume `integral_blockKernel_mul_gaussian`, retaining
its determinant normalization and identifying its exponent with the coarse
precision. This is the integration-level consumer of the new matrix API.

## General matrix-weighted Gaussian integration and composition

The real Euclidean kernel now uses arbitrary positive-definite matrix precision
`R`: `sqrt(det R) / (2*pi)^(dim/2) * exp(-inner(y-Qx, R(y-Qx))/2)`.
`WeightedKernel` proves its positivity, normalization, exact scalar-density
specialization, and Gaussian elimination with the full determinant factor.
`WeightedKernelConvolution` derives `det H * det S = det R * det A` from
native block determinant identities, then proves normalized two-kernel
convolution with observation map `Q2 * Q1` and precision
`(R2^-1 + Q2 * R1^-1 * Q2^adjoint)^-1`.

`WeightedCoarseGrainingSpecialization` retains the actual upstream scalar
factor `alpha*beta/(beta+s*alpha)`, consumes the existing convolution theorem,
and proves the weighted-adjoint ratio `coarseWeight/fineWeight` and the
single-counting scale identities. No identification with a particular lattice
spacing is asserted without its inner-product weights.
`WeightedCoarseGrainingExamples` proves positive definiteness of both explicit
2-by-2 precisions and demonstrates the inverse-covariance product order.

The original matrix and integration owners passed independent statement-level
review and the exact destination build recorded below. The extension adds a
native probability interface and a finite reflected-covariance theorem.

## Native Markov kernels and KL data processing

`WeightedMarkovKernel` uses `ProbabilityTheory.Kernel.withDensity` on the
constant Euclidean Lebesgue kernel. It proves joint continuity and
measurability of the existing density, integrability, normalization, measure
and integral readback, and an actual `IsMarkovKernel` instance.

Tonelli's theorem and the proved real integral convolution identify native
kernel composition with the kernel having observation map `Q2 * Q1` and
precision `(R2^-1 + Q2 * R1^-1 * Q2^transpose)^-1`. This is an equality of
kernels, including their values on measurable sets.

The KL theorem invokes native `InformationTheory.klDiv_comp_right_le` for two
finite input measures processed by the **same** kernel. Mathlib's finite-measure
definition includes the mass correction; on probability measures this is the
usual KL divergence. Extended infinite values are allowed. The theorem gives
monotonicity, with no strict contraction constant. The Gaussian composition
formula uses fixed matrices at each stage; field-dependent coefficients
require a separate theorem.

## Reflected covariance and the Schur operator

`ReflectionPositiveCovariance` works with native real matrices and selected
test-space inclusions `Uf` and `Uc`. If

```
theta_c * Q = Q * theta_f
Q^transpose * Uc = Uf * B
```

then it proves the exact identity

```
Uc^transpose * theta_c * (N + Q * C * Q^transpose) * Uc
  = Uc^transpose * theta_c * N * Uc
    + B^transpose * (Uf^transpose * theta_f * C * Uf) * B.
```

Consequently, separate positive-semidefiniteness hypotheses for the fine and
noise reflected forms imply positivity of the coarse reflected form.
`WeightedReflectionPositive` applies this identity to the actual
`coarsePrecision A R Q` inverse, taking `C = A^-1` and `N = R^-1` and consuming
`coarsePrecision_inv`. Positive definiteness of `A` and `R` supplies its inverse
hypotheses; it does not replace either reflected-positivity hypothesis.

An explicit two-coordinate counterexample proves that a positive-definite
covariance may commute with the symmetric reflection and still have a negative
reflected form. The same example shows that adding such noise can destroy
reflected positivity of an initially reflection-positive covariance, even
with identity blocking. This guards the precise noise hypothesis.

The standalone theorem proves finite covariance-form positivity. A Gaussian
measure theorem for nonlinear positive-time observables and a continuum OS
reconstruction need further arguments.

## Native owners reused

- `Matrix.add_mul_mul_inv_eq_sub`, positivity and nonsingular inverses.
- `Matrix.schur_complement_eq₂₂` and Hermitian quadratic forms.
- `Matrix.toEuclideanLin`, its multiplication and adjoint compatibility.
- Existing `GaussianBlockSpin.effStiffness` and
  `GaussianBlockSpin.integral_blockKernel_mul_gaussian`.
- Native `Kernel.withDensity`, kernel composition, Tonelli and KL data processing.
- Native matrix positivity under congruence and the existing coarse covariance identity.

## Scope and remaining obligations

The matrix theory is finite real/Hermitian operator algebra. The scalar adapter and matrix-weighted
kernel theorems use real finite-dimensional Gaussian integration. Target-specific gauge fixing
and positivity/coercivity on compressed carriers must be supplied separately.
Complex symmetric bilinear holomorphic Gaussian forms require their own
real-part-coercivity/continuation bridge. No polymer bound, Wilson counterterm,
cutoff-uniform estimate, continuum theorem, or mass gap is asserted.

## Validation status

The combined audit and its mathematical owner dependency closure passed the exact destination build in
[run 45571203500](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/45571203500),
job `139058006800`, at preparation commit
`ff8e1632b45569d88da1c73c0ec160c913fe55f9`:
Lean 4.34.0-rc2 and Mathlib `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`.

The warnings-as-errors build, separate fresh audit of all **78 public theorems**
plus the kernel definition and Markov instance (**80 reports**), source-hash
comparison, and unchanged dependency-pin checks all passed. The reports contain
no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

All fifteen Lean source files match the successful source inventory, including
the optional focused audit entry points. The eight original mathematical
Gaussian owners remain byte-for-byte unchanged.
The combined audit includes the new native kernel, exact kernel composition,
KL theorem, covariance transport, actual Schur adapter, and all counterexamples,
including noncommutation of reflection with the selected-time projection.
Independent semantic reviews inspected the actual carriers and hypotheses.

The [preparation validation package](https://github.com/nickgou-nuke/info-geometry-lean/tree/codex/wilson-upstream-contributions-20261124/contributions/wilson/validation)
preserves the source inventory, dependency revisions, build log, fresh axiom
transcript and artifact digest under `evidence/exact-gaussian-ff8e163`.
Earlier 54-theorem checks remain historical evidence. The final certificate is
the exact destination CI run above; an interrupted local Markov build is not
counted as a compiler success.

## Integration edits

Place the Lean files under `GaussianBlockSpin/`; place the scoped license notice
and the full Apache license beside that directory at the library root. Add imports of
`GaussianBlockSpin.WeightedCoarseGrainingComposition` and
`GaussianBlockSpin.WeightedEffectiveForm`,
`GaussianBlockSpin.WeightedCoarseGrainingSpecialization`, and
`GaussianBlockSpin.WeightedKernelConvolution`,
`GaussianBlockSpin.WeightedMarkovKernel`, and
`GaussianBlockSpin.WeightedReflectionPositive` to the existing library umbrella.
Keep the audit opt-in as a focused build target rather than importing its
`#print axioms` commands through the main library.
