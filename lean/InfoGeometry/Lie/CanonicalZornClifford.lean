import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

/-!
# Split Cl(1,1) Clifford Algebra on Canonical Zorn Matrices

This module establishes the split Cl(1,1) representation on `CanonicalZorn` endomorphisms:
- generator e₀ = ι(1, 0) acts as `circularHodgeStar` (e₀² = +1)
- generator e₁ = ι(0, 1) acts as `circularHodgeStar * circularGradedChirality` (e₁² = -1)
- pseudoscalar ω = e₀ e₁ acts as `circularGradedChirality` (ω² = +1)
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornClifford

open InfoGeometry.Lie.CanonicalZornCircularHodgeTransport

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The split quadratic form Q₁₁ of signature (1, 1) on ℝ × ℝ: u² - v². -/
def Q11 : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) -
    QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma Q11_apply (v : ℝ × ℝ) :
    Q11 v = v.1 ^ 2 - v.2 ^ 2 := by
  simp [Q11, sq]

/-- Linear map sending (u, v) to u • ⋆ + v • (⋆Γ). -/
def cl11LinearMap : (ℝ × ℝ) →ₗ[ℝ] EndCZ where
  toFun v := v.1 • circularHodgeStar + v.2 • (circularHodgeStar * circularGradedChirality)
  map_add' v w := by
    dsimp
    simp only [add_smul]
    abel
  map_smul' a v := by
    dsimp
    simp only [smul_add, mul_smul]

/-- The Clifford relation for Q₁₁: (u • ⋆ + v • (⋆Γ))² = (u² - v²) • 1. -/
theorem cl11_clifford_condition (v : ℝ × ℝ) :
    cl11LinearMap v * cl11LinearMap v = (Q11 v) • (1 : EndCZ) := by
  have h_star := circularHodgeStar_sq
  have h_comp := circularComplexStructure_sq
  have h_anti : circularGradedChirality * circularHodgeStar =
      -(circularHodgeStar * circularGradedChirality) := by
    rw [← neg_neg (circularGradedChirality * circularHodgeStar),
        ← circularHodgeStar_gradedChirality_anticommutes]
  simp only [cl11LinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    add_mul, mul_add, smul_mul_smul, sq, Q11_apply]
  rw [h_star, h_comp]
  have h_cross1 : (circularHodgeStar * (circularHodgeStar * circularGradedChirality)) =
      circularGradedChirality := by
    rw [← mul_assoc, h_star, one_mul]
  have h_cross2 : ((circularHodgeStar * circularGradedChirality) * circularHodgeStar) =
      -circularGradedChirality := by
    rw [mul_assoc, h_anti, mul_neg, ← mul_assoc, h_star, one_mul]
  rw [h_cross1, h_cross2, smul_neg, mul_comm v.2 v.1]
  rw [add_assoc, neg_add_cancel_left, smul_neg, ← sub_eq_add_neg, sub_smul]

/-- The canonical Cl(1,1) algebra representation on EndCZ. -/
def cl11Rep : CliffordAlgebra Q11 →ₐ[ℝ] EndCZ :=
  CliffordAlgebra.lift Q11 ⟨cl11LinearMap, cl11_clifford_condition⟩

/-- The Clifford action on the carrier CZ. -/
instance : SMul (CliffordAlgebra Q11) CZ where
  smul a x := cl11Rep a x

@[simp] theorem cl11Rep_ι_star :
    cl11Rep (CliffordAlgebra.ι Q11 (1, 0)) = circularHodgeStar := by
  rw [cl11Rep, CliffordAlgebra.lift_ι_apply]
  simp [cl11LinearMap]

@[simp] theorem cl11Rep_ι_complex :
    cl11Rep (CliffordAlgebra.ι Q11 (0, 1)) =
      circularHodgeStar * circularGradedChirality := by
  rw [cl11Rep, CliffordAlgebra.lift_ι_apply]
  simp [cl11LinearMap]

@[simp] theorem cl11Rep_pseudoscalar :
    cl11Rep (CliffordAlgebra.ι Q11 (1, 0) * CliffordAlgebra.ι Q11 (0, 1)) =
      circularGradedChirality := by
  rw [map_mul, cl11Rep_ι_star, cl11Rep_ι_complex, ← mul_assoc, circularHodgeStar_sq, one_mul]

end InfoGeometry.Lie.CanonicalZornClifford
