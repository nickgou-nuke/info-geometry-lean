/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.TripotentMiddlePairing
import InfoGeometry.OperatorAlgebra.UnitaryCornerCompression
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.LinearAlgebra.Projection

/-!
# Preserved tripotent sectors and exact paired-operator kernels

A generator commuting with a tripotent preserves its polynomial cuts under
the native exponential. Such a cut cannot simultaneously have cross-sector
transfer from that exponential.

For native real module endomorphisms, two oppositely supported operators
have exactly the middle-sector kernel when each is injective on its source
outer sector. The same holds for their square. No finite-dimensional,
adjoint, positivity, or uniform spectral-gap assumption is used or inferred.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.TripotentCornerDynamics

open InfoGeometry.Physics.Algebra
open InfoGeometry.OperatorAlgebra.TripotentMiddlePairing

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem commute_projPos {a S : A} (h : Commute a S) : Commute a (projPos S) := by
  unfold projPos
  exact ((h.mul_right h).add_right h).smul_right _

theorem commute_projNeg {a S : A} (h : Commute a S) : Commute a (projNeg S) := by
  unfold projNeg
  exact ((h.mul_right h).sub_right h).smul_right _

theorem commute_projZero {a S : A} (h : Commute a S) : Commute a (projZero S) := by
  unfold projZero
  exact (Commute.one_right a).sub_right (h.mul_right h)

section Star

variable [StarRing A] [StarModule ℝ A]

/-- The single complementary transfer resolves into the middle and negative
channels. Orthogonality removes the two cross terms in their Gram square. -/
theorem tripotent_schwarz_defect (S x : A) (u : unitary A)
    (hS : S * S * S = S) (hSs : star S = S) :
    UnitaryCornerCompression.compress (projPos S) u (star x * x) -
        star (UnitaryCornerCompression.compress (projPos S) u x) *
          UnitaryCornerCompression.compress (projPos S) u x =
      star (projZero S * Unitary.conjStarAlgAut ℤ A u x * projPos S) *
        (projZero S * Unitary.conjStarAlgAut ℤ A u x * projPos S) +
      star (projNeg S * Unitary.conjStarAlgAut ℤ A u x * projPos S) *
        (projNeg S * Unitary.conjStarAlgAut ℤ A u x * projPos S) := by
  let y := Unitary.conjStarAlgAut ℤ A u x
  have hp : IsStarProjection (projPos S) :=
    ⟨projPos_idempotent hS, star_projPos hSs⟩
  have hsplit : 1 - projPos S = projZero S + projNeg S := by
    calc
      _ = (projPos S + projZero S + projNeg S) - projPos S := by
        rw [proj_sum_eq_id]
      _ = _ := by abel
  have hcross : star (projZero S * y * projPos S) *
      (projNeg S * y * projPos S) = 0 := by
    simp only [star_mul, star_projPos hSs, star_projZero hSs]
    calc
      _ = projPos S * star y * (projZero S * projNeg S) * y * projPos S := by
        simp only [mul_assoc]
      _ = 0 := by rw [projZero_mul_projNeg_eq_zero hS]; simp
  have hcross' : star (projNeg S * y * projPos S) *
      (projZero S * y * projPos S) = 0 := by
    simp only [star_mul, star_projPos hSs, star_projNeg hSs]
    calc
      _ = projPos S * star y * (projNeg S * projZero S) * y * projPos S := by
        simp only [mul_assoc]
      _ = 0 := by rw [projNeg_mul_projZero_eq_zero hS]; simp
  rw [UnitaryCornerCompression.schwarz_defect _ _ _ _ hp]
  simp only [UnitaryCornerCompression.transfer, hsplit, add_mul, star_add,
    mul_add, hcross, hcross', add_zero, zero_add]

end Star

private theorem opposite_zero_sector {S C : A} (hS : S * S * S = S)
    (hC : projNeg S * C * projPos S = C) :
    projZero S * C = 0 ∧ C * projZero S = 0 := by
  constructor
  · calc
      projZero S * C = projZero S * (projNeg S * C * projPos S) := by rw [hC]
      _ = (projZero S * projNeg S) * C * projPos S := by simp only [mul_assoc]
      _ = 0 := by rw [projZero_mul_projNeg_eq_zero hS]; simp
  · calc
      C * projZero S = (projNeg S * C * projPos S) * projZero S := by rw [hC]
      _ = projNeg S * C * (projPos S * projZero S) := by simp only [mul_assoc]
      _ = 0 := by rw [projPos_mul_projZero_eq_zero hS]; simp

/-- Mutually inverse transitions between the two outer sectors give an exact
algebraic normalization. The two ordered product equations are explicit
premises, not consequences of nonzero pairing or middle-sector support. -/
theorem paired_square_of_partial_inverses {S B C : A}
    (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B)
    (hC : projNeg S * C * projPos S = C)
    (hBC : B * C = projPos S) (hCB : C * B = projNeg S) :
    (B + C) ^ 2 = 1 - projZero S := by
  have hCC : C * C = 0 := by
    calc
      C * C = (projNeg S * C * projPos S) *
          (projNeg S * C * projPos S) := by rw [hC]
      _ = projNeg S * C * (projPos S * projNeg S) * C * projPos S := by
        simp only [mul_assoc]
      _ = 0 := by rw [projPos_mul_projNeg_eq_zero hS]; simp
  calc
    (B + C) ^ 2 = projPos S + projNeg S := by
      simp only [pow_two, add_mul, mul_add, extreme_square_zero hS hB,
        hCC, hBC, hCB, zero_add, add_zero]
    _ = 1 - projZero S :=
      (PeirceSpine.one_sub_projZero_eq_projPos_add_projNeg S).symm

end Algebra

section Exponential

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- Commutation with the generator preserves the actual polynomial cut. -/
theorem exponential_commute_projPos {S G : A} (hG : Commute G S) (t : ℝ) :
    Commute (NormedSpace.exp (t • G)) (projPos S) :=
  ((commute_projPos hG).smul_left t).exp_left

/-- A preserved positive sector has no transfer to its complement. -/
theorem exponential_no_leakage {S G : A} (hS : S * S * S = S)
    (hG : Commute G S) (t : ℝ) :
    (1 - projPos S) * NormedSpace.exp (t • G) * projPos S = 0 := by
  rw [mul_assoc, (exponential_commute_projPos hG t).eq, ← mul_assoc]
  simp only [sub_mul, one_mul, projPos_idempotent hS, sub_self, zero_mul]

/-- Supplying the missing phase commutation makes the proposed generator
grade-preserving and simultaneously eliminates leakage through this cut. -/
theorem phase_generated_no_leakage {S J H : A} (hS : S * S * S = S)
    (hSJ : Commute S J) (hSH : Commute S H) (t : ℝ) :
    (1 - projPos S) * NormedSpace.exp (t • (J * H)) * projPos S = 0 :=
  exponential_no_leakage hS (hSJ.mul_right hSH).symm t

end Exponential

section Endomorphism

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The intake's exact dual-inverse relations discharge the middle-kernel
conclusion through Mathlib's native idempotent range/kernel theorem. -/
theorem paired_square_kernel_of_partial_inverses
    {S B C : Module.End ℝ E} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B)
    (hC : projNeg S * C * projPos S = C)
    (hBC : B * C = projPos S) (hCB : C * B = projNeg S) :
    LinearMap.ker ((B + C) ^ 2) = LinearMap.range (projZero S) := by
  rw [paired_square_of_partial_inverses hS hB hC hBC hCB]
  exact (LinearMap.IsIdempotentElem.range_eq_ker_one_sub
    (show IsIdempotentElem (projZero S) from projZero_idempotent hS)).symm

/-- Exact kernel of opposite outer-sector transitions. The premises are the
zero-kernel form of injectivity on each source sector; middle annihilation
alone does not supply them. The real module may be infinite-dimensional. -/
theorem paired_kernel_eq_middle_range
    {S B C : Module.End ℝ E} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B)
    (hC : projNeg S * C * projPos S = C)
    (hBinj : ∀ x : E, projNeg S x = x → B x = 0 → x = 0)
    (hCinj : ∀ x : E, projPos S x = x → C x = 0 → x = 0) :
    LinearMap.ker (B + C) = LinearMap.range (projZero S) := by
  let p := projPos S
  let q := projZero S
  let r := projNeg S
  have hp : p * p = p := projPos_idempotent hS
  have hr : r * r = r := projNeg_idempotent hS
  have hpB : p * B = B := by
    calc
      p * B = p * (p * B * r) := by rw [hB]
      _ = (p * p) * B * r := by simp only [mul_assoc]
      _ = B := by rw [hp, hB]
  have hBr : B * r = B := by
    calc
      B * r = (p * B * r) * r := by rw [hB]
      _ = p * B * (r * r) := by simp only [mul_assoc]
      _ = B := by rw [hr, hB]
  have hCp : C * p = C := by
    calc
      C * p = (r * C * p) * p := by rw [hC]
      _ = r * C * (p * p) := by simp only [mul_assoc]
      _ = C := by rw [hp, hC]
  have hpC : p * C = 0 := by
    calc
      p * C = p * (r * C * p) := by rw [hC]
      _ = (p * r) * C * p := by simp only [mul_assoc]
      _ = 0 := by rw [projPos_mul_projNeg_eq_zero hS]; simp
  have hsumq : (B + C) * q = 0 := by
    rw [add_mul, (extreme_zero_sector hS hB).2,
      (opposite_zero_sector hS hC).2, add_zero]
  ext x
  change (B + C) x = 0 ↔ ∃ y, q y = x
  constructor
  · intro hx
    have hBx : B x = 0 := by
      have h := congrArg (fun y : E => p y) hx
      change (p * (B + C)) x = p 0 at h
      rw [mul_add, hpB, hpC, add_zero, map_zero] at h
      exact h
    have hCx : C x = 0 := by
      change B x + C x = 0 at hx
      simpa only [hBx, zero_add] using hx
    have hrx : r x = 0 := by
      apply hBinj (r x)
      · change (r * r) x = r x
        rw [hr]
      · change (B * r) x = 0
        rw [hBr]
        exact hBx
    have hpx : p x = 0 := by
      apply hCinj (p x)
      · change (p * p) x = p x
        rw [hp]
      · change (C * p) x = 0
        rw [hCp]
        exact hCx
    have hpartition := congrArg (fun f : Module.End ℝ E => f x)
      (proj_sum_eq_id (T := S))
    change p x + q x + r x = x at hpartition
    rw [hpx, hrx, zero_add, add_zero] at hpartition
    exact ⟨x, hpartition⟩
  · rintro ⟨y, rfl⟩
    change ((B + C) * q) y = 0
    rw [hsumq]
    rfl

/-- The square has exactly the same middle kernel. This excludes additional
generalized zero modes using the ordered sector supports and injectivity,
without asserting a norm lower bound or a uniform spectral gap. -/
theorem paired_square_kernel_eq_middle_range
    {S B C : Module.End ℝ E} (hS : S * S * S = S)
    (hB : projPos S * B * projNeg S = B)
    (hC : projNeg S * C * projPos S = C)
    (hBinj : ∀ x : E, projNeg S x = x → B x = 0 → x = 0)
    (hCinj : ∀ x : E, projPos S x = x → C x = 0 → x = 0) :
    LinearMap.ker ((B + C) ^ 2) = LinearMap.range (projZero S) := by
  have hker := paired_kernel_eq_middle_range hS hB hC hBinj hCinj
  have hqleft : projZero S * (B + C) = 0 := by
    rw [mul_add, (extreme_zero_sector hS hB).1,
      (opposite_zero_sector hS hC).1, add_zero]
  ext x
  constructor
  · intro hx
    have hdx : (B + C) x ∈ LinearMap.ker (B + C) := by
      change (B + C) ((B + C) x) = 0
      exact hx
    rw [hker] at hdx
    obtain ⟨y, hy⟩ := hdx
    have hfixed : projZero S ((B + C) x) = (B + C) x := by
      rw [← hy]
      change (projZero S * projZero S) y = projZero S y
      rw [projZero_idempotent hS]
    have hzero : (B + C) x = 0 := by
      rw [← hfixed]
      change (projZero S * (B + C)) x = 0
      rw [hqleft]
      rfl
    rw [← hker]
    exact hzero
  · intro hx
    rw [← hker] at hx
    change (B + C) ((B + C) x) = 0
    rw [show (B + C) x = 0 from hx, map_zero]

end Endomorphism

end InfoGeometry.OperatorAlgebra.TripotentCornerDynamics
