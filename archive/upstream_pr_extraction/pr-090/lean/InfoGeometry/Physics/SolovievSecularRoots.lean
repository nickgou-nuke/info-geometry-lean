import Mathlib
import InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

noncomputable section

namespace InfoGeometry.Physics.SolovievSecularRoots

open InfoGeometry.Physics.SolovievFiniteSecularEigenproblem

def discriminant (eQ eP v : ℝ) : ℝ := (eQ - eP) ^ 2 + 4 * v ^ 2

def lowerRoot (eQ eP v : ℝ) : ℝ :=
  (eQ + eP - Real.sqrt (discriminant eQ eP v)) / 2

def upperRoot (eQ eP v : ℝ) : ℝ :=
  (eQ + eP + Real.sqrt (discriminant eQ eP v)) / 2

theorem discriminant_nonneg (eQ eP v : ℝ) : 0 ≤ discriminant eQ eP v := by
  dsimp [discriminant]
  nlinarith [sq_nonneg (eQ - eP), sq_nonneg v]

theorem lowerRoot_is_secular_root (eQ eP v : ℝ) :
    secularPolynomial eQ eP v (lowerRoot eQ eP v) = 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg eQ eP v)
  dsimp [discriminant] at hs
  dsimp [secularPolynomial, lowerRoot, discriminant]
  field_simp
  nlinarith

theorem upperRoot_is_secular_root (eQ eP v : ℝ) :
    secularPolynomial eQ eP v (upperRoot eQ eP v) = 0 := by
  have hs := Real.sq_sqrt (discriminant_nonneg eQ eP v)
  dsimp [discriminant] at hs
  dsimp [secularPolynomial, upperRoot, discriminant]
  field_simp
  nlinarith

/-! The closed-form spectral separation is the square root of the
discriminant. -/
theorem upperRoot_sub_lowerRoot (eQ eP v : ℝ) :
    upperRoot eQ eP v - lowerRoot eQ eP v =
      Real.sqrt (discriminant eQ eP v) := by
  dsimp [upperRoot, lowerRoot]
  ring

theorem upperRoot_ne_lowerRoot_of_v_ne_zero
    (eQ eP v : ℝ) (hv : v ≠ 0) :
    upperRoot eQ eP v ≠ lowerRoot eQ eP v := by
  have hdisc : 0 < discriminant eQ eP v := by
    dsimp [discriminant]
    nlinarith [sq_nonneg (eQ - eP), sq_pos_of_ne_zero hv]
  have hsep : 0 < upperRoot eQ eP v - lowerRoot eQ eP v := by
    rw [upperRoot_sub_lowerRoot]
    exact Real.sqrt_pos.2 hdisc
  exact sub_ne_zero.mp (ne_of_gt hsep)

theorem lowerRoot_add_upperRoot (eQ eP v : ℝ) :
    lowerRoot eQ eP v + upperRoot eQ eP v = eQ + eP := by
  dsimp [lowerRoot, upperRoot]
  ring

theorem lowerRoot_mul_upperRoot (eQ eP v : ℝ) :
    lowerRoot eQ eP v * upperRoot eQ eP v = eQ * eP - v ^ 2 := by
  have hs := Real.sq_sqrt (discriminant_nonneg eQ eP v)
  dsimp [lowerRoot, upperRoot, discriminant] at hs ⊢
  field_simp
  nlinarith

end InfoGeometry.Physics.SolovievSecularRoots
