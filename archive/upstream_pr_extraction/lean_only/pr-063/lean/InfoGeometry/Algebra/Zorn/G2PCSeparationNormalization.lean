import InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoPCGroup

namespace InfoGeometry.Algebra.Zorn.G2PCSeparationNormalization

open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

/-! Group-theoretic normalization of a PC/Weyl separation equality.

This owner deliberately contains no finite enumeration.  It isolates the
exact cancellation boundary needed by the matrix relative-Weyl argument.
-/

theorem ne_iff_mul_inv_ne_one
    {G : Type*} [Group G] {a b : G} :
    a ≠ b ↔ a * b⁻¹ ≠ 1 := by
  constructor
  · intro hab hab1
    apply hab
    calc
      a = (a * b⁻¹) * b := by simp [mul_assoc]
      _ = 1 * b := by rw [hab1]
      _ = b := one_mul b
  · intro hab hEq
    apply hab
    rw [hEq]
    simp

theorem pc_weyl_separation_iff_normalized_ne_one
    {w₁ w₂ : SplitOctF2Aut}
    (a c d : PCWordExp) :
    pcWord c * w₂ ≠ pcWord a * w₁ * pcWord d ↔
      (pcWord c * w₂) * (pcWord a * w₁ * pcWord d)⁻¹ ≠ 1 := by
  exact ne_iff_mul_inv_ne_one

end InfoGeometry.Algebra.Zorn.G2PCSeparationNormalization
