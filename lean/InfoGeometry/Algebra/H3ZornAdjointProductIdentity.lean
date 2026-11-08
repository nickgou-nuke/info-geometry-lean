import InfoGeometry.Algebra.H3ZornJordanIdentity

/-!
# The cubic adjoint-product identity on the native split-Albert carrier

This theorem reuses the existing `H3Zorn ℝ` carrier, Jordan product, cubic
norm, and McCrimmon trace identities. It introduces no second Albert model.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- Multiplying an Albert element by its quadratic adjoint gives its cubic
norm times the unit. This is distinct from the adjoint-square identity
`(X#)# = N(X) X`. -/
theorem h3zorn_jordan_mul_adjoint_eq_norm_one (X : H3Zorn ℝ) :
    candidateJordanMul X (adjointQuad X) =
      normCubic X • (1 : H3Zorn ℝ) := by
  rw [candidateJordanMul_trace_formula]
  rw [mccrimmon_identity_16 X (adjointQuad X),
    traceBilin_symm X (adjointQuad X), mccrimmon_identity_13 X]
  rw [crossProduct_symm X (adjointQuad X), mccrimmon_identity_18 X]
  module

end InfoGeometry.Algebra
