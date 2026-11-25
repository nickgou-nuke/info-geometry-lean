# Source-grounded review of the Gaussian/RG intake

Intake: `Pasted text(20261124-150457).txt`, SHA256
`9bc02582c6f750ed96e115afc764ecbf9bab2c80bd9f6f3ca6feb1571e6ffb55`.

Reviewed against upstream `9a4492cc6bdf3338379123a085af59dfd8018a9c`
and the previously prepared Gaussian contribution. This records the read-only
intake audit; it is not an acceptance certificate for the new integration code.

## Corrected source claims

1. `EffectiveForm.lean` implements `effStiffness` with the plain Euclidean
   adjoint. Its comment gives the separate lattice relation
   `Q_k* = L^(k*d) Qᵀ`. The attachment's asserted names `blockAdjoint`,
   `blockMatrix`, `effectiveHessian`, `minimizerField`, and `effectiveOperator`
   were not found in the inspected `GaussianBlockSpin` library.
2. `Convolution.lean` proves the coefficient `α*β/(β+s*α)` under
   `Q ∘ adjoint Q = s • id`. The source identifies `s = L^(-d)` for the plain
   Euclidean block averages. The attachment's `s=1` expression is a
   specialization, not the upstream theorem's literal general coefficient.
3. With `B=w*Qᵀ`, `M=B*Q`, and `R_lat=α*w*R`, the attachment's identity at
   `R=I` incorrectly uses `α*w*M`, double-counting `w`. The correct expression
   is `α*M`. In dimension one, `A=0,Q=R=1,α=1,w=2` refutes the original
   statement by reducing it to `2=4`.
4. The attachment's matrix example states symmetry and noncommutation but
   does not assert positive definiteness. It also uses `R₁` in the sandwich
   while its description claims a result about `R₁⁻¹`. The separate
   specialization/example candidate repairs both statement-level omissions.
5. The attachment's limit theorem concerns arbitrary real functions. It does
   not supply `CStarStateColimit.Native.State`, whose functional is a native
   complex positive linear map normalized at `1`. The separate state-limit
   contribution proves the additional algebraic properties explicitly.

## Scope of the earlier scalar integration adapter

`WeightedEffectiveForm.integral_blockKernel_mul_gaussian_coarsePrecision`
consumes the actual upstream integral for scalar coarse precision `α I`.
The existing general matrix operators and square-completion theorems do not,
on their own, define a normalized matrix-weighted probability density or prove
its integral convolution. The new `WeightedKernel` and
`WeightedKernelConvolution` owners address that precise gap; their successful
exact-version build and fresh axiom audit are recorded in
[the theorem contract](THEOREM_CONTRACT.md).

## New integration proof route

- `WeightedKernel` defines the gated density with coefficient
  `sqrt(det R)/(2π)^(dim/2)` and proves normalization using the upstream
  `integral_exp_neg_half_inner` plus translation invariance.
- The existing matrix square completion is transported to real Euclidean
  inner products. The harmonic extension supplies the translation in the
  determinant-normalized elimination integral.
- `WeightedKernelConvolution` applies both native block determinant formulas
  to the same matrix to establish `det H * det S = det R * det A`.
  This identity combines the normalization constants in two-kernel convolution.
- Scalar density specialization preserves the upstream normalizing factor.

The integration claims are conditional on finite-dimensional real positive
definiteness. No Markov-kernel structure, gauge fixing, UV-uniform bounds,
reflection positivity, or Wilson-loop continuum theorem is asserted.
