# Matrix-weighted Gaussian elimination and composition

This extension uses the existing Gaussian integral and canonical Euclidean
volume. The density is available on finite-dimensional real inner product
spaces; the elimination and convolution theorems below use `EuclideanSpace ℝ n`
and native `Matrix.toEuclideanLin` for arbitrary finite index types.

For positive definite real matrices A and R and any rectangular Q, let

- K = A + Qᵀ R Q;
- E = K⁻¹ Qᵀ R;
- S = R − R Q K⁻¹ Qᵀ R.

`MatrixWeighted.Positive` establishes K,S > 0, both normal equations,
S⁻¹ = R⁻¹ + Q A⁻¹ Qᵀ, and det(S)det(K) = det(R)det(A).
`MatrixWeighted.Variational` proves exact square completion and identifies E y
as the unique global minimizer. `MatrixWeighted.Composition` gives the ordered
two-step covariance and joint minimizer, and collapse to the composite map.
No commutation or rank assumption on Q is required.

`MatrixWeighted.Kernel` defines the normalized density

```
sqrt(det R) / (2π)^(dim F / 2) * exp (−½ ⟪y−Qx, R(y−Qx)⟫).
```

It proves positivity, joint continuity, measurability, normalization,
integrability, and exact readback to the original scalar `blockKernel`.
`MatrixWeighted.Coordinates` preserves the adjoint, determinant, and quadratic
form in the standard orthonormal coordinates. `MatrixWeighted.EffectiveForm`
integrates the completed square, including its determinant normalizer.
`MatrixWeighted.Convolution` proves the actual integral composition law:

```
∫ z, K(R₂,Q₂)(y,z) * K(R₁,Q₁)(z,x) = K(S,Q₂ Q₁)(y,x)
S = coarsePrecision R₁ R₂ Q₂
S⁻¹ = R₂⁻¹ + Q₂ R₁⁻¹ Q₂ᵀ.
```

For R₁ = βI, R₂ = αI, and Q₂ Q₂ᵀ = sI, α,β > 0 and s ≥ 0,
`integral_blockKernel_mul_blockKernel_of_matrix` derives the existing scalar
coefficient αβ/(β+sα) from the new matrix theorem.

The exact 2×2 example has A=[[2,1],[1,2]], R=[[3,1],[1,2]], Q=[[1,1],[0,1]].
Both precisions are positive definite and do not commute. The response is
[[7/20,−3/10],[1/4,1/2]], and the output precision is
[[19/20,−1/10],[−1/10,4/5]]. The example proves the factor-order obstruction
and specializes the unique-minimizer theorem.

## Conventions and boundaries

All integrals use the existing canonical inner-product-space volume. The
current Bałaban specialization uses plain Euclidean coordinates and absorbs
lattice scale factors into its operators. No weighted lattice adjoint is
silently identified with a transpose. Changing the inner product/volume needs
an additional coordinate/Jacobian argument.

The old EffectiveForm witness w satisfies K w = Q†y, and its minimizer is αw.
The new E y includes R, so for R=αI its normal equation is K(E y)=αQ†y.
The theorem concerns strictly positive fine precisions on the declared space;
it does not eliminate gauge zero modes, prove uniform UV estimates, construct
a Markov kernel, or establish interacting Wilson-loop convergence.

## Attribution

Positive, Variational, and Composition adapt the Apache-2.0 InfoGeometry owners
`PositiveCoarseGraining`, `CoarseGrainingVariational`, and
`CoarseGrainingComposition` at fe24e350b08fdea04f74c0748ef9fd9417c47529 from
https://github.com/nickgou-nuke/info-geometry-lean . They specialize the field
to real matrices and add determinant normalization and scalar readback.
Examples follows the Gram-plus-identity construction of the source tests.
Coordinates transports these results to the native Euclidean linear maps.
Their original copyright/author notices are retained; see
`LICENSE-InfoGeometry-Apache-2.0` and `NOTICE-InfoGeometry`. Those notices govern
the attributed files independently of the upstream root CC0 license.
