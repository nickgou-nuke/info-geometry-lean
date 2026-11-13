/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.TripotentParity
import InfoGeometry.Core.PeirceCoupledCorners
import Mathlib.Algebra.Star.Module

/-!
# Ordered pairing through the zero sector of a tripotent

The three factors retain their order: `(P₊ a P₀) (P₀ w P₀) (P₀ b P₋)`.
Moving the middle-sector factor to the far left instead annihilates the first
transition. The correctly ordered product belongs to the existing `+2` grade.
Its adjoint belongs to `-2`; their sum preserves zero-sector parity and
annihilates the zero sector, while its Cartan commutator detects the pairing.

All identities hold in an arbitrary associative real algebra. No invertibility,
strict positivity, spectral gap, equality of kernels, or physical scattering
claim follows from support or a nonzero pairing alone.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TripotentMiddlePairing

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The middle operator is composed between its incoming and outgoing corners. -/
def middlePairing (S a w b : A) : A :=
  (projPos S * a * projZero S) * (projZero S * w * projZero S) *
    (projZero S * b * projNeg S)

/-- An internal zero-sector coefficient placed before the incoming corner
kills it. This is an ordered product identity, not a scalar cancellation. -/
theorem wrong_left_order_zero {S : A} (hS : S * S * S = S) (a w : A) :
    (projZero S * w * projZero S) * (projPos S * a * projZero S) = 0 := by
  calc
    _ = projZero S * w * (projZero S * projPos S) * a * projZero S := by
      simp only [mul_assoc]
    _ = 0 := by rw [projZero_mul_projPos_eq_zero hS]; simp

/-- Contract only the repeated zero projectors; preserve the order `a,w,b`. -/
theorem middlePairing_contract {S : A} (hS : S * S * S = S) (a w b : A) :
    middlePairing S a w b =
      projPos S * a * projZero S * w * projZero S * b * projNeg S := by
  unfold middlePairing
  calc
    _ = projPos S * a * (projZero S * projZero S) * w *
        (projZero S * projZero S) * b * projNeg S := by
      simp only [mul_assoc]
    _ = _ := by simp only [projZero_idempotent hS]

/-- The constructed middle pairing is supported from the negative to positive sector. -/
theorem middlePairing_support {S : A} (hS : S * S * S = S) (a w b : A) :
    projPos S * middlePairing S a w b * projNeg S = middlePairing S a w b := by
  simp only [middlePairing_contract hS]
  calc
    _ = (projPos S * projPos S) * a * projZero S * w * projZero S * b *
        (projNeg S * projNeg S) := by simp only [mul_assoc]
    _ = _ := by rw [projPos_idempotent hS, projNeg_idempotent hS]

/-- Extreme corner support gives membership in the native positive-two grade. -/
theorem extreme_mem_posTwo {S B : A} (hB : projPos S * B * projNeg S = B) :
    B ∈ fiveGradeRange S .posTwo := by
  refine ⟨B, ?_⟩
  change projPos S * (B * projNeg S) = B
  simpa only [mul_assoc] using hB

/-- The ordered construction discharges the extreme-support premise. -/
theorem middlePairing_mem_posTwo {S : A} (hS : S * S * S = S) (a w b : A) :
    middlePairing S a w b ∈ fiveGradeRange S .posTwo :=
  extreme_mem_posTwo (middlePairing_support hS a w b)

/-- The same extreme corner sits in the established two-sector Peirce owner. -/
theorem extreme_mem_peirce10 {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) : B ∈ peirce10 (projPos S) := by
  have hm : projNeg S * (1 - projPos S) = projNeg S := by
    rw [mul_sub, mul_one, projNeg_mul_projPos_eq_zero hS, sub_zero]
  refine ⟨B * projNeg S, ?_⟩
  change B = projPos S * (B * projNeg S) * (1 - projPos S)
  calc
    B = projPos S * B * projNeg S := hB.symm
    _ = projPos S * (B * (projNeg S * (1 - projPos S))) := by
      rw [hm]
      simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- No path through either side of the zero sector remains in an extreme corner. -/
theorem extreme_zero_sector {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) :
    projZero S * B = 0 ∧ B * projZero S = 0 := by
  constructor
  · calc
      projZero S * B = projZero S * (projPos S * B * projNeg S) := by rw [hB]
      _ = (projZero S * projPos S) * B * projNeg S := by simp only [mul_assoc]
      _ = 0 := by rw [projZero_mul_projPos_eq_zero hS]; simp
  · calc
      B * projZero S = (projPos S * B * projNeg S) * projZero S := by rw [hB]
      _ = projPos S * B * (projNeg S * projZero S) := by simp only [mul_assoc]
      _ = 0 := by rw [projNeg_mul_projZero_eq_zero hS]; simp

/-- Same-sign extreme pairing is nilpotent by the existing directed-corner law. -/
theorem extreme_square_zero {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) : B * B = 0 := by
  exact peirce10_mul_peirce10_eq_zero (projPos S) (projPos_idempotent hS)
    (extreme_mem_peirce10 hS hB) (extreme_mem_peirce10 hS hB)

/-- The Cartan charge is the existing native grade eigenvalue. -/
theorem extreme_charge {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) :
    S * B - B * S = (2 : ℝ) • B := by
  simpa [fiveGradeValue] using
    mem_fiveGradeRange_implies_adjoint_eigen hS .posTwo (extreme_mem_posTwo hB)

/-- The `+2` corner is even for the owned zero-mode parity action. -/
theorem extreme_parity {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) :
    parityConj (projZero S) B = B := by
  simpa using parityConj_projZero_of_mem_fiveGradeRange hS .posTwo
    (extreme_mem_posTwo hB)

section Star

variable [StarRing A]

/-- The reversed adjoint corner is also square-zero, without a positivity assumption. -/
theorem star_extreme_square_zero {S B : A} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B) : star B * star B = 0 := by
  simpa only [star_mul, star_zero] using congrArg star (extreme_square_zero hS hB)

variable [StarModule ℝ A]

/-- Polynomial positive projectors inherit the adjoint of the Cartan operator. -/
theorem star_projPos {S : A} (hS : star S = S) : star (projPos S) = projPos S := by
  simp [projPos, star_smul, star_mul, hS]

/-- Polynomial negative projectors inherit the adjoint of the Cartan operator. -/
theorem star_projNeg {S : A} (hS : star S = S) : star (projNeg S) = projNeg S := by
  simp [projNeg, star_smul, star_mul, hS]

/-- The zero projector inherits self-adjointness independently of tripotence. -/
theorem star_projZero {S : A} (hS : star S = S) : star (projZero S) = projZero S := by
  simp [projZero, star_mul, hS]

/-- Adjoint reverses the two extreme supports. -/
theorem star_extreme_support {S B : A} (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    projNeg S * star B * projPos S = star B := by
  simpa only [star_mul, star_projNeg hSs, star_projPos hSs, mul_assoc] using
    congrArg star hB

/-- The paired adjoint has native grade `-2`. -/
theorem star_extreme_mem_negTwo {S B : A} (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) : star B ∈ fiveGradeRange S .negTwo := by
  refine ⟨star B, ?_⟩
  change projNeg S * (star B * projPos S) = star B
  simpa only [mul_assoc] using star_extreme_support hSs hB

/-- Reuse the opposite-corner square theorem for the supported adjoint sum. -/
theorem paired_square {S B : A} (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    (B + star B) ^ 2 = B * star B + star B * B := by
  have hp : IsSelfAdjoint (projPos S) := star_projPos hSs
  have hu := extreme_mem_peirce10 hS hB
  exact coupled_square (projPos_idempotent hS) hu (star_mem_peirce01 hp hu)

/-- Both annihilation identities survive forming the adjoint-paired operator. -/
theorem paired_zero_sector {S B : A} (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    projZero S * (B + star B) = 0 ∧ (B + star B) * projZero S = 0 := by
  obtain ⟨hleft, hright⟩ := extreme_zero_sector hS hB
  have hsleft : projZero S * star B = 0 := by
    simpa only [star_mul, star_projZero hSs, star_zero] using congrArg star hright
  have hsright : star B * projZero S = 0 := by
    simpa only [star_mul, star_projZero hSs, star_zero] using congrArg star hleft
  constructor
  · rw [mul_add, hleft, hsleft, add_zero]
  · rw [add_mul, hright, hsright, add_zero]

/-- The square also annihilates the zero sector; this supplies a kernel inclusion. -/
theorem paired_square_zero_sector {S B : A}
    (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    projZero S * (B + star B) ^ 2 = 0 ∧ (B + star B) ^ 2 * projZero S = 0 := by
  obtain ⟨hleft, hright⟩ := paired_zero_sector hS hSs hB
  constructor
  · rw [pow_two, ← mul_assoc, hleft, zero_mul]
  · rw [pow_two, mul_assoc, hright, mul_zero]

/-- Pairing carries opposite Cartan charges; its commutator is their difference. -/
theorem paired_charge {S B : A} (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    S * (B + star B) - (B + star B) * S = (2 : ℝ) • (B - star B) := by
  have hneg : S * star B - star B * S = (-2 : ℝ) • star B := by
    simpa [fiveGradeValue] using mem_fiveGradeRange_implies_adjoint_eigen hS .negTwo
      (star_extreme_mem_negTwo hSs hB)
  calc
    _ = (S * B - B * S) + (S * star B - star B * S) := by noncomm_ring
    _ = (2 : ℝ) • B + (-2 : ℝ) • star B := by rw [extreme_charge hS hB, hneg]
    _ = _ := by rw [smul_sub, neg_smul, sub_eq_add_neg]

/-- A nonzero supported pairing genuinely breaks the Cartan commutation relation. -/
theorem paired_charge_eq_zero_iff {S B : A}
    (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    S * (B + star B) - (B + star B) * S = 0 ↔ B = 0 := by
  constructor
  · intro hc
    have hp : IsSelfAdjoint (projPos S) := star_projPos hSs
    have hu := extreme_mem_peirce10 hS hB
    have hsleft : projPos S * star B = 0 :=
      left_support01 (projPos_idempotent hS) (star_mem_peirce01 hp hu)
    have hcompressed := congrArg (fun X : A => projPos S * X * projNeg S) hc
    rw [paired_charge hS hSs hB, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      mul_sub, sub_mul, hB, hsleft, zero_mul, sub_zero,
      mul_zero, zero_mul] at hcompressed
    exact (smul_eq_zero.mp hcompressed).resolve_left (by norm_num)
  · intro hzero
    simp [hzero]

/-- The same paired operator preserves the owned zero-mode parity. Its grading
involution is the negative of `2 S² - 1`, which has the same conjugation action. -/
theorem paired_parity {S B : A} (hS : S * S * S = S) (hSs : star S = S)
    (hB : projPos S * B * projNeg S = B) :
    parityConj (projZero S) (B + star B) = B + star B := by
  apply (parityConj_fixed_iff_commutes_with_grading (projZero_idempotent hS) _).mpr
  obtain ⟨hleft, hright⟩ := paired_zero_sector hS hSs hB
  simp only [invS, sub_mul, mul_sub, one_mul, mul_one, hleft, hright]

end Star

end InfoGeometry.OperatorAlgebra.TripotentMiddlePairing
