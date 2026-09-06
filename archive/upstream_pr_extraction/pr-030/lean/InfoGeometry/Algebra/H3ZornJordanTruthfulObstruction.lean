import InfoGeometry.Algebra.H3ZornJordanObstruction

/-!
# Certified status packet for the `H3Zorn ℝ` Jordan closure surface

This file packages the native global Jordan-law and `T`-commutation proofs.
-/

namespace InfoGeometry.Algebra

open H3Zorn

/-- Combined native closure package for the product and `T` formulations. -/
def H3ZornJordanTotalValidity : Prop :=
  H3ZornJordanProductLaw ∧ TJordanCommutation

/-- The total closure package follows from the McCrimmon operator proof. -/
theorem H3ZornJordanTotalValidity_proof : H3ZornJordanTotalValidity :=
  ⟨H3ZornJordanProductLaw_proof, TJordanCommutation_proof⟩

/-- Total validity contains the product law as its first field. -/
theorem H3ZornJordanProductLaw_of_totalValidity
    (h : H3ZornJordanTotalValidity) : H3ZornJordanProductLaw :=
  h.1

/-- Total validity contains the `T`-commutation law as its second field. -/
theorem TJordanCommutation_of_totalValidity
    (h : H3ZornJordanTotalValidity) : TJordanCommutation :=
  h.2

end InfoGeometry.Algebra
