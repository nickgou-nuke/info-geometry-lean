import Mathlib
import proofs.CuntzPeirceLogicalQubit

noncomputable section

open CuntzPeirceLogicalCorner CuntzWordSpaceQEC

namespace CuntzLogicalHodge

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (S : Fin 2 → A) [hC : CuntzO2 (S 0) (S 1)]

axiom cuntzLogicalMatrixUnit_mul_eq (a b c d : Fin 2) :
    cuntzLogicalMatrixUnit S a b * cuntzLogicalMatrixUnit S c d =
      if b = c then cuntzLogicalMatrixUnit S a d else 0

def logicalGrading : A :=
  cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1

def logicalCodeUnit : A :=
  cuntzLogicalMatrixUnit S 0 0 + cuntzLogicalMatrixUnit S 1 1

theorem logicalGrading_star :
    star (logicalGrading S) = logicalGrading S := by
  unfold logicalGrading
  rw [star_sub, cuntzLogicalMatrixUnit_star, cuntzLogicalMatrixUnit_star]

theorem logicalGrading_sq :
    logicalGrading S * logicalGrading S = logicalCodeUnit S := by
  unfold logicalGrading logicalCodeUnit
  rw [sub_mul, mul_sub, mul_sub]
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  rw [h1, h2, h3, h4]
  ring

def logicalGradingDerivation (a : A) : A :=
  logicalGrading S * a - a * logicalGrading S

theorem logicalGradingDerivation_mul (a b : A) :
    logicalGradingDerivation S (a * b) =
      logicalGradingDerivation S a * b + a * logicalGradingDerivation S b := by
  unfold logicalGradingDerivation
  rw [sub_mul, mul_sub, add_mul, mul_add, mul_sub, sub_mul]
  have h_add : logicalGrading S * a * b - a * logicalGrading S * b + (a * logicalGrading S * b - a * b * logicalGrading S) = logicalGrading S * a * b - a * b * logicalGrading S := by
    abel
  rw [h_add]
  exact mul_assoc a b (logicalGrading S) |>.symm ▸ mul_assoc (logicalGrading S) a b |>.symm ▸ rfl

def logicalHodgeLaplacian (a : A) : A :=
  logicalGradingDerivation S (logicalGradingDerivation S a)

theorem logicalHodgeLaplacian_eq (a : A)
    (hleft : logicalCodeUnit S * a = a)
    (hright : a * logicalCodeUnit S = a) :
    logicalHodgeLaplacian S a =
      (2 : ℂ) • a - (2 : ℂ) • (logicalGrading S * a * logicalGrading S) := by
  unfold logicalHodgeLaplacian logicalGradingDerivation
  rw [mul_sub, sub_mul, ← mul_assoc, mul_assoc a]
  rw [logicalGrading_sq S]
  rw [hleft, hright]
  have h1 : a - logicalGrading S * a * logicalGrading S - logicalGrading S * a * logicalGrading S + a = a + a - (logicalGrading S * a * logicalGrading S + logicalGrading S * a * logicalGrading S) := by abel
  rw [h1, two_smul, two_smul]

def logicalDiagonalPart (a : A) : A :=
  ((2 : ℂ)⁻¹) • (a + logicalGrading S * a * logicalGrading S)

def logicalOffDiagonalPart (a : A) : A :=
  ((2 : ℂ)⁻¹) • (a - logicalGrading S * a * logicalGrading S)

theorem logicalDiagonalPart_add_offDiagonalPart (a : A) :
    logicalDiagonalPart S a + logicalOffDiagonalPart S a = a := by
  unfold logicalDiagonalPart logicalOffDiagonalPart
  rw [← smul_add]
  have h : a + logicalGrading S * a * logicalGrading S + (a - logicalGrading S * a * logicalGrading S) = a + a := by abel
  rw [h]
  have h2 : a + a = (2 : ℂ) • a := by rw [two_smul]
  rw [h2]
  rw [← smul_assoc]
  have h3 : ((2 : ℂ)⁻¹ * 2) = 1 := by norm_num
  rw [h3, one_smul]

theorem logicalHodgeLaplacian_eq_four_smul_offDiagonalPart (a : A)
    (hleft : logicalCodeUnit S * a = a)
    (hright : a * logicalCodeUnit S = a) :
    logicalHodgeLaplacian S a = (4 : ℂ) • logicalOffDiagonalPart S a := by
  rw [logicalHodgeLaplacian_eq S a hleft hright]
  unfold logicalOffDiagonalPart
  rw [smul_smul]
  have h : (4 : ℂ) * (2 : ℂ)⁻¹ = 2 := by norm_num
  rw [h, smul_sub]

theorem logicalDiagonalPart_L00 :
    logicalDiagonalPart S (cuntzLogicalMatrixUnit S 0 0) = cuntzLogicalMatrixUnit S 0 0 := by
  unfold logicalDiagonalPart logicalGrading
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h : (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) * cuntzLogicalMatrixUnit S 0 0 * (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) = cuntzLogicalMatrixUnit S 0 0 := by
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, h4]; simp
  rw [h]
  have hd : cuntzLogicalMatrixUnit S 0 0 + cuntzLogicalMatrixUnit S 0 0 = (2 : ℂ) • cuntzLogicalMatrixUnit S 0 0 := by rw [two_smul]
  rw [hd, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDiagonalPart_L11 :
    logicalDiagonalPart S (cuntzLogicalMatrixUnit S 1 1) = cuntzLogicalMatrixUnit S 1 1 := by
  unfold logicalDiagonalPart logicalGrading
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 0 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 1 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h : (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) * cuntzLogicalMatrixUnit S 1 1 * (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) = cuntzLogicalMatrixUnit S 1 1 := by
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, h4]; simp
  rw [h]
  have hd : cuntzLogicalMatrixUnit S 1 1 + cuntzLogicalMatrixUnit S 1 1 = (2 : ℂ) • cuntzLogicalMatrixUnit S 1 1 := by rw [two_smul]
  rw [hd, ← mul_smul, inv_mul_cancel two_ne_zero, one_smul]

theorem logicalDiagonalPart_L01 :
    logicalDiagonalPart S (cuntzLogicalMatrixUnit S 0 1) = 0 := by
  unfold logicalDiagonalPart logicalGrading
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 0 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 0 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 0 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 0 1 * cuntzLogicalMatrixUnit S 1 1 = cuntzLogicalMatrixUnit S 0 1 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h : (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) * cuntzLogicalMatrixUnit S 0 1 * (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) = - cuntzLogicalMatrixUnit S 0 1 := by
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, h4]; simp
  rw [h]
  have hd : cuntzLogicalMatrixUnit S 0 1 + -cuntzLogicalMatrixUnit S 0 1 = 0 := add_neg_cancel _
  rw [hd, smul_zero]

theorem logicalDiagonalPart_L10 :
    logicalDiagonalPart S (cuntzLogicalMatrixUnit S 1 0) = 0 := by
  unfold logicalDiagonalPart logicalGrading
  have h1 : cuntzLogicalMatrixUnit S 0 0 * cuntzLogicalMatrixUnit S 1 0 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h2 : cuntzLogicalMatrixUnit S 1 1 * cuntzLogicalMatrixUnit S 1 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h3 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 0 0 = cuntzLogicalMatrixUnit S 1 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h4 : cuntzLogicalMatrixUnit S 1 0 * cuntzLogicalMatrixUnit S 1 1 = 0 := by rw [cuntzLogicalMatrixUnit_mul_eq]; simp
  have h : (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) * cuntzLogicalMatrixUnit S 1 0 * (cuntzLogicalMatrixUnit S 0 0 - cuntzLogicalMatrixUnit S 1 1) = - cuntzLogicalMatrixUnit S 1 0 := by
    rw [sub_mul, mul_sub, mul_sub, h1, h2, h3, h4]; simp
  rw [h]
  have hd : cuntzLogicalMatrixUnit S 1 0 + -cuntzLogicalMatrixUnit S 1 0 = 0 := add_neg_cancel _
  rw [hd, smul_zero]

def logicalDecoherenceSemigroup (t : ℝ) (a : A) : A :=
  logicalDiagonalPart S a + algebraMap ℂ A (Complex.exp (-4 * (t : ℂ))) * logicalOffDiagonalPart S a

theorem logicalDecoherenceSemigroup_zero (a : A) :
    logicalDecoherenceSemigroup S 0 a = a := by
  unfold logicalDecoherenceSemigroup
  have h1 : (0 : ℝ) = (0 : ℂ) := by rfl
  have h2 : (-4 * (0 : ℂ)) = 0 := by ring
  rw [h2, Complex.exp_zero]
  have h3 : algebraMap ℂ A 1 = 1 := map_one (algebraMap ℂ A)
  rw [h3, one_mul]
  exact logicalDiagonalPart_add_offDiagonalPart S a

theorem logicalDecoherenceSemigroup_add (s t : ℝ) (a : A) :
    logicalDecoherenceSemigroup S (s + t) a =
      logicalDecoherenceSemigroup S s (logicalDecoherenceSemigroup S t a) := by
  sorry

end CuntzLogicalHodge
