# Real matrix Gaussian kernels: theorem contract

The implementation is in the four owners listed in the verification profile.
Compilation, fresh owner elaboration, and the complete declaration-axiom audit
are reported separately from mathematical/source review in the PR evidence.

## Intake and source authority

The supplied comparison is preserved verbatim in
`verification/matrix-gaussian-kernels/intake-20261124.txt`.
The source baseline is `fe24e350b08fdea04f74c0748ef9fd9417c47529`.
The existing Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins remain unchanged.

The external comparison concerns `MathePhysics/4D_Wilson_Loop_RG` at
`9a4492cc6bdf3338379123a085af59dfd8018a9c`, especially its
`LEAN/Libraries/GaussianBlockSpin` package. That package uses Lean
4.34.0-rc2 and Mathlib `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`.
No compilation under our pin certifies a port to that different environment.
The external repository is not modified by this contribution.

## Existing owners and the missing implication

`OperatorAlgebra.PositiveCoarseGraining` already defines the actual
rectangular matrix operators

```
H = A + Qᴴ * R * Q
E = H⁻¹ * Qᴴ * R
S = R - R * Q * H⁻¹ * Qᴴ * R
```

and proves positivity, the normal equations, and
`S⁻¹ = R⁻¹ + Q * A⁻¹ * Qᴴ`. `CoarseGrainingVariational` proves exact
square completion and the unique minimizer. `CoarseGrainingComposition`
proves the two-stage covariance expansion and joint minimization. These
results do not require commuting matrices or a rank hypothesis on Q.

The missing probabilistic object is a native, real Markov kernel whose
actual probability laws have those covariances. A covariance matrix equation
alone is not a theorem about composition of probability measures.

Mathlib's `ProbabilityTheory.multivariateGaussian` already supplies Gaussian
probability measures, joint parameter measurability, their means and their
covariance forms. Reuse that construction instead of introducing a new
Gaussian measure, a new carrier, or assumed normalization fields.

## Real carriers and conventions

The input and output spaces are `EuclideanSpace ℝ n` and
`EuclideanSpace ℝ m`, with arbitrary finite index types. A rectangular
`Q : Matrix m n ℝ` acts through the native Euclidean coordinate equivalence:

```
linearMean Q x = WithLp.toLp 2 (Q *ᵥ WithLp.ofLp x)
```

For a strictly positive definite real precision matrix R, the channel is

```
gaussianKernel Q R x = multivariateGaussian (linearMean Q x) R⁻¹.
```

The public vector spaces, precision matrices, means, and covariance
operators are real. Native complex characteristic functions may be used
inside proofs of measure equality; they introduce no complex state carrier
or physical phase parameter.

Mathlib's Gaussian construction is total and always gives a probability
measure. The interpretation of the supplied matrix as its covariance must
retain the positive-semidefinite hypothesis. Here the corresponding
precision/covariance identification uses `R.PosDef` and `R⁻¹.PosSemidef`.
An unconditional Markov instance must not be advertised as an unconditional
covariance-identification theorem for arbitrary R.

## Acceptance statements

### 1. Actual probability kernel

Construct `ProbabilityTheory.Kernel` with a proved measurable dependence on
the input. Establish `IsMarkovKernel`, the pointwise Gaussian law, the mean,
and the covariance form with the stated positivity hypotheses. Reuse native
KL data processing for arbitrary finite input measures. This proves
monotonicity; it does not imply a strict contraction or an RG convergence
rate.

### 2. Collapse of the positive precision operators

For Q1 from the fine to intermediate space and Q2 from the intermediate to
coarse space, and positive definite R1,R2, use the existing operator

```
N = coarsePrecision R1 R2 Q2
N⁻¹ = R2⁻¹ + Q2 * R1⁻¹ * Q2ᴴ.
```

Prove that successive elimination with an initial positive precision A
equals one elimination with N and Q2*Q1. Preserve the order of every matrix
factor. No scalar, coisometry, or commutation assumption belongs in this
general theorem.

### 3. Composition of actual kernels

Prove equality of the native probability kernels:

```
gaussianKernel Q2 R2 ∘ₖ gaussianKernel Q1 R1
  = gaussianKernel (Q2 * Q1) (coarsePrecision R1 R2 Q2).
```

The proof must establish equality of measures, not merely equality of
their displayed covariance expressions. Pointwise Gaussian characteristic
functions and native uniqueness of measures are one valid proof route.

Derive normalized Gaussian elimination as a corollary:

```
gaussianKernel Q R ∘ₘ multivariateGaussian μ A⁻¹
  = multivariateGaussian (linearMean Q μ) (coarsePrecision A R Q)⁻¹.
```

### 4. Scalar specialization and a noncommuting example

Under R1 = βI, R2 = αI, Q2*Q2ᵀ = sI, with α,β positive and s nonnegative,
the collapsed precision must be `(α*β/(β+s*α))I`, matching the external
package's scalar coefficient. Specialize equality of the native kernels as
`gaussianKernel_comp_scalar_noise`, using this same coefficient.

The concrete real example uses

```
Q1 = [[1,0,1],[0,1,1]], Q2 = [[1,2],[0,1]],
R1 = [[2,1],[1,2]],     R2 = [[3,0],[0,1]].
```

R1 and R2 do not commute, and Q2 is not a scalar coisometry. The exact
collapsed covariance is `[[7/3,1],[1,5/3]]`; its inverse is
`[[15/26,-9/26],[-9/26,21/26]]`. The composite observation is
`[[1,2,3],[0,1,1]]`. This example must specialize the actual kernel theorem.

## External integration boundary

The external GaussianBlockSpin package already integrates arbitrary
positive symmetric fine operators, but its block density uses scalar coarse
precision and its current convolution theorem additionally assumes a scalar
coisometry. The contribution here supplies a reusable native measure-level
interface and exact general composition in our existing pinned environment.

The remaining density bridge is explicit: identify this native Gaussian law
with their normalized Lebesgue density, preserve their volume/adjoint
convention, and compile any port at their exact pins. Their current Bałaban
application absorbs lattice weights into plain Euclidean-coordinate
operators. Changing the inner product also changes the adjoint and volume;
one must not retain a density prefactor after changing coordinates without
the corresponding Jacobian theorem.

No result here removes gauge zero modes, proves uniform UV bounds, controls
interacting RG errors, or establishes Wilson-loop convergence or a mass gap.

## State and GNS proposal

The attachment's summable-compatibility proposal is a separate target. Our
native GNS owners consume exactly compatible positive normalized states;
they do not construct that compatibility from the model's approximate RG
estimates. No Markov operator is promoted to a star-algebra homomorphism.
No exact recovery of the original stage states is asserted when only
nonzero summable defects are supplied.

## Verification

Use `verification/matrix-gaussian-kernels/check.py` for the exact source
closure, maintained shared compiler lock, fixed dependencies, fresh owner
elaboration with warnings as errors, and a complete declaration-axiom audit.
Permitted foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No proof holes, custom axioms, or unsafe proof bypasses may
enter the contributed owners.

The focused receipt covers the selected owners only. Root-package and
publication-gate acceptance remain separately reported.
