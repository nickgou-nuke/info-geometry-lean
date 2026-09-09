import InfoGeometry.Algebra.H3ZornJordanIdentity

/-!
# H₃ Zorn product-law re-export

This module exists for import compatibility.  It re-exports both the
pointwise formulation and the native global proof from
`H3ZornJordanIdentity`.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- The product-law proposition is definitionally the expected pointwise equality. -/
theorem H3ZornJordanProductLawAt_iff (x y : H3Zorn ℝ) :
    H3ZornJordanProductLawAt x y ↔
      candidateJordanMul (candidateJordanMul x y) (candidateJordanMul x x) =
        candidateJordanMul x (candidateJordanMul y (candidateJordanMul x x)) := by
  rfl

/-- Compatibility re-export of the native global Jordan product law. -/
theorem H3ZornJordanProductLaw_verified : H3ZornJordanProductLaw :=
  H3ZornJordanProductLaw_proof

end InfoGeometry.Algebra
