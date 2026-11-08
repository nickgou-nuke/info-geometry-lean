/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceDefect
import InfoGeometry.Core.PeirceAdjointCycle
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Native adjoint corrections and the three Peirce projectors

The quadratic frame's double-adjoint corrections keep the full operator
`K*K-K`. The final section identifies the existing normalized tripotent
projectors of `ad p` with the even and two directed Peirce components.
-/

namespace InfoGeometry.Core.PeirceDefectAdjoint

attribute [local instance 100] LieRing.ofAssociativeRing

open IdempotencyDefect PeirceDecomposition PeirceGrading
open PeirceCoupledCorners PeirceQuadraticFrame

variable {A : Type*} [Ring A]

section Adjoint

variable {R : Type*} [CommRing R] [Algebra R A]

/-- On an anticommuting input, the native double adjoint retains the generator square. -/
theorem ad_sq_apply_of_anticommute {a x : A} (hax : a * x + x * a = 0) :
    (LieAlgebra.ad R A a ^ 2) x = 4 • (a ^ 2 * x) := by
  have hxa : x * a = -(a * x) := eq_neg_of_add_eq_zero_right hax
  have hc : ⁅a, x⁆ = 2 • (a * x) := by
    change a * x - x * a = 2 • (a * x)
    rw [hxa, sub_neg_eq_add, two_nsmul]
  change ⁅a, ⁅a, x⁆⁆ = 4 • (a ^ 2 * x)
  rw [hc, lie_nsmul, Ring.lie_def]
  rw [mul_assoc a x a, hxa, mul_neg, ← mul_assoc a a x]
  simp only [pow_two, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

/-- Both adjoint squares act on the same full matrix/operator input. -/
theorem negative_ad_squares_sum_eq_defect {p u v : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    -((LieAlgebra.ad R A ⁅u, v⁆ ^ 2) (u + v)) -
        (LieAlgebra.ad R A (u - v) ^ 2) (u + v) =
      -(4 • (defect (u * v + v * u) * (u + v))) := by
  have hc : (LieAlgebra.ad R A ⁅u, v⁆ ^ 2) (u + v) =
      4 • ((u * v + v * u) ^ 2 * (u + v)) := double_bracket_sum hp hu hv
  have hj := ad_sq_apply_of_anticommute (R := R)
    (show (u - v) * (u + v) + (u + v) * (u - v) = 0 by
      simpa only [add_comm] using sum_difference_anticommute hp hu hv)
  rw [difference_square hp hu hv] at hj
  rw [hc, hj]
  simp only [defect, pow_two, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

theorem ad_squares_sub_eq_defect {p u v : A} (hp : IsIdempotentElem p)
    (hu : u ∈ peirce10 p) (hv : v ∈ peirce01 p) :
    (LieAlgebra.ad R A ⁅u, v⁆ ^ 2 - LieAlgebra.ad R A (u + v) ^ 2) (u - v) =
      4 • (defect (u * v + v * u) * (u - v)) := by
  have hc : (LieAlgebra.ad R A ⁅u, v⁆ ^ 2) (u - v) =
      4 • ((u * v + v * u) ^ 2 * (u - v)) := double_bracket_difference hp hu hv
  have he := ad_sq_apply_of_anticommute (R := R)
    (sum_difference_anticommute hp hu hv)
  rw [coupled_square hp hu hv] at he
  rw [LinearMap.sub_apply, hc, he]
  simp only [defect, pow_two, nsmul_eq_mul, Nat.cast_ofNat]
  noncomm_ring

end Adjoint

section RealProjectors

variable [Algebra ℝ A] {p : A}

open InfoGeometry.Physics.Algebra

/-- Scalar extension of the owned integer-linear annihilating identity. -/
theorem real_ad_cube_eq_ad (hp : IsIdempotentElem p) :
    LieAlgebra.ad ℝ A p ^ 3 = LieAlgebra.ad ℝ A p := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun f : Module.End ℤ A => f x) (PeirceAdjointCycle.ad_cube_eq_ad hp)

theorem projZero_ad_apply (hp : IsIdempotentElem p) (x : A) :
    projZero (LieAlgebra.ad ℝ A p) x = even p x := by
  change x - (p * (p * x - x * p) - (p * x - x * p) * p) = even p x
  rw [← (odd_reconstruction hp x).2]
  exact (eq_sub_iff_add_eq.mpr (even_add_odd p x)).symm

theorem projPos_ad_apply (hp : IsIdempotentElem p) (x : A) :
    projPos (LieAlgebra.ad ℝ A p) x = component10 p x := by
  change (1 / 2 : ℝ) •
    (p * (p * x - x * p) - (p * x - x * p) * p + (p * x - x * p)) = _
  have h : p * (p * x - x * p) - (p * x - x * p) * p + (p * x - x * p) =
      (2 : ℝ) • component10 p x := by
    rw [two_smul ℝ]
    simp only [component10, complementIdempotent]
    noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]
  rw [h, smul_smul]
  norm_num

theorem projNeg_ad_apply (hp : IsIdempotentElem p) (x : A) :
    projNeg (LieAlgebra.ad ℝ A p) x = component01 p x := by
  change (1 / 2 : ℝ) •
    (p * (p * x - x * p) - (p * x - x * p) * p - (p * x - x * p)) = _
  have h : p * (p * x - x * p) - (p * x - x * p) * p - (p * x - x * p) =
      (2 : ℝ) • component01 p x := by
    rw [two_smul ℝ]
    simp only [component01, complementIdempotent]
    noncomm_ring [hp.eq, idempotent_mul_nested p hp.eq]
  rw [h, smul_smul]
  norm_num

end RealProjectors

end InfoGeometry.Core.PeirceDefectAdjoint
