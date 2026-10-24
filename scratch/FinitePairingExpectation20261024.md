# Finite pairing first-factor expectation contract

Status: G-A scratch candidate, uncompiled; parent owns promotion and locked QA.

## Exact statement

For arbitrary `c s : ℝ` and `X : M2C`, use the native `ChainOp` product-index
carrier and the native operators from `FinitePairingReducedVacuum`:

- `U = FinitePairingImplementer.rotor b₁ B₁ b₂ B₂ c s`;
- `vacuum = (b₁ * B₁) * (b₂ * B₂)`;
- ordinary matrix trace and actual conjugate transpose.

Prove

`trace ((X ⊗ₖ I) * (U * vacuum * U.conjTranspose))
 = (c : ℂ)^2 * X 0 0 + (s : ℂ)^2 * X 1 1`.

The candidate declaration is
`InfoGeometry.OperatorAlgebra.FinitePairingExpectation.firstFactor_expectation`.
No normalization or self-adjointness of `X` is assumed.

## Owner reuse and proof

Import only `InfoGeometry.OperatorAlgebra.FinitePairingReducedVacuum`.
Its import surface provides
`InfoGeometry.QuantumContext.MatrixStagePartialTrace.trace_mul_partialTraceSecondOp`:
`trace (X * partialTraceSecondOp D) = trace ((X ⊗ₖ I) * D)`.
Rewrite backwards with this theorem, then use native `reducedVacuum` to obtain
`c² • (a * A) + s² • (A * a)`. Evaluate the ordinary two-dimensional trace
using the existing complexified matrix units. No partial-trace definition,
CAR representation, state carrier, or conclusion bundle is introduced.

## Scope

The polynomial identity is unconditional in the real coefficients. The native
`reducedVacuum_posSemidef` supplies positivity; `reducedVacuum_trace` gives mass
`c² + s²`. Calling the resulting functional a normalized positive state requires
`c² + s² = 1`. This does not assert that the reduced state is pure, tracial,
faithful, or KMS for arbitrary coefficients. It uses ordinary partial trace,
not the tower's half-scaled `normalizedPartialTraceStep`.

## Acceptance

Parent QA should elaborate the candidate and audit the single theorem's axioms.
No builds or tests were run by the author. No live owner was changed.
