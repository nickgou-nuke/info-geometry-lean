/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentEigenspaces
import Mathlib.LinearAlgebra.Projection

/-!
# Kernels of extreme tripotent operators

The extreme five-grade ranges are the two opposite Peirce corners. Their
nonzero endomorphisms have kernels strictly larger than the zero-mode range.
A normalized pair in the two opposite corners recovers that range as the
intersection of its kernels. These are statements about arbitrary real
vector spaces; no finite-dimensionality or scalar replacement is used.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentExtremeKernels

open InfoGeometry.Physics.Algebra

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- A positive extreme corner annihilates the middle projector on the right. -/
theorem posTwo_mul_projZero_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .posTwo) : N * projZero S = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projPos S * (X * projNeg S)) * projZero S = 0
  simp only [mul_assoc, projNeg_mul_projZero_eq_zero hS, mul_zero]

/-- A positive extreme corner is annihilated by the middle projector on the left. -/
theorem projZero_mul_posTwo_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .posTwo) : projZero S * N = 0 := by
  rcases hN with ⟨X, rfl⟩
  change projZero S * (projPos S * (X * projNeg S)) = 0
  rw [← mul_assoc, projZero_mul_projPos_eq_zero hS, zero_mul]

/-- A positive extreme corner also kills its target spectral range. -/
theorem posTwo_mul_projPos_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .posTwo) : N * projPos S = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projPos S * (X * projNeg S)) * projPos S = 0
  simp only [mul_assoc, projNeg_mul_projPos_eq_zero hS, mul_zero]

/-- Every positive extreme operator has square zero. -/
theorem posTwo_mul_self_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .posTwo) : N * N = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projPos S * (X * projNeg S)) * (projPos S * (X * projNeg S)) = 0
  calc
    _ = projPos S * X * (projNeg S * projPos S) * X * projNeg S := by
      simp only [mul_assoc]
    _ = 0 := by simp only [projNeg_mul_projPos_eq_zero hS, mul_zero, zero_mul]

/-- A negative extreme corner annihilates the middle projector on the right. -/
theorem negTwo_mul_projZero_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .negTwo) : N * projZero S = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projNeg S * (X * projPos S)) * projZero S = 0
  simp only [mul_assoc, projPos_mul_projZero_eq_zero hS, mul_zero]

/-- A negative extreme corner is annihilated by the middle projector on the left. -/
theorem projZero_mul_negTwo_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .negTwo) : projZero S * N = 0 := by
  rcases hN with ⟨X, rfl⟩
  change projZero S * (projNeg S * (X * projPos S)) = 0
  rw [← mul_assoc, projZero_mul_projNeg_eq_zero hS, zero_mul]

/-- A negative extreme corner also kills its target spectral range. -/
theorem negTwo_mul_projNeg_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .negTwo) : N * projNeg S = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projNeg S * (X * projPos S)) * projNeg S = 0
  simp only [mul_assoc, projPos_mul_projNeg_eq_zero hS, mul_zero]

/-- Every negative extreme operator has square zero. -/
theorem negTwo_mul_self_eq_zero {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .negTwo) : N * N = 0 := by
  rcases hN with ⟨X, rfl⟩
  change (projNeg S * (X * projPos S)) * (projNeg S * (X * projPos S)) = 0
  calc
    _ = projNeg S * X * (projPos S * projNeg S) * X * projPos S := by
      simp only [mul_assoc]
    _ = 0 := by simp only [projPos_mul_projNeg_eq_zero hS, mul_zero, zero_mul]

end Algebra

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A nonzero square-zero operator annihilating a projector on both sides
has a kernel strictly larger than that projector's range. -/
theorem range_lt_ker_of_sq_zero {P N : Module.End ℝ V}
    (hP : P * P = P) (hNP : N * P = 0) (hPN : P * N = 0)
    (hNN : N * N = 0) (hN : N ≠ 0) :
    LinearMap.range P < LinearMap.ker N := by
  refine lt_of_le_of_ne (LinearMap.range_le_ker_iff.mpr hNP) ?_
  intro heq
  apply hN
  ext v
  have hv : N v ∈ LinearMap.range P := by
    rw [heq]
    change (N * N) v = 0
    rw [hNN]
    rfl
  obtain ⟨w, hw⟩ := hv
  have hfix : P (N v) = N v := by
    rw [← hw]
    change (P * P) w = P w
    rw [hP]
  have hzero : P (N v) = 0 := by
    change (P * N) v = 0
    rw [hPN]
    rfl
  exact hfix.symm.trans hzero

/-- A positive extreme endomorphism kills the middle and positive ranges. -/
theorem range_zero_sup_pos_le_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .posTwo) :
    LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) ≤ LinearMap.ker N :=
  sup_le
    (LinearMap.range_le_ker_iff.mpr (posTwo_mul_projZero_eq_zero hS hN))
    (LinearMap.range_le_ker_iff.mpr (posTwo_mul_projPos_eq_zero hS hN))

/-- A negative extreme endomorphism kills the middle and negative ranges. -/
theorem range_zero_sup_neg_le_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .negTwo) :
    LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) ≤ LinearMap.ker N :=
  sup_le
    (LinearMap.range_le_ker_iff.mpr (negTwo_mul_projZero_eq_zero hS hN))
    (LinearMap.range_le_ker_iff.mpr (negTwo_mul_projNeg_eq_zero hS hN))

/-- No nonzero positive extreme endomorphism has exactly the zero-mode kernel. -/
theorem range_projZero_lt_ker_posTwo {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .posTwo) (hne : N ≠ 0) :
    LinearMap.range (projZero S) < LinearMap.ker N :=
  range_lt_ker_of_sq_zero (projZero_idempotent hS)
    (posTwo_mul_projZero_eq_zero hS hN) (projZero_mul_posTwo_eq_zero hS hN)
    (posTwo_mul_self_eq_zero hS hN) hne

/-- No nonzero negative extreme endomorphism has exactly the zero-mode kernel. -/
theorem range_projZero_lt_ker_negTwo {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .negTwo) (hne : N ≠ 0) :
    LinearMap.range (projZero S) < LinearMap.ker N :=
  range_lt_ker_of_sq_zero (projZero_idempotent hS)
    (negTwo_mul_projZero_eq_zero hS hN) (projZero_mul_negTwo_eq_zero hS hN)
    (negTwo_mul_self_eq_zero hS hN) hne

/-- A normalized left inverse on the negative range determines the positive
extreme operator's full kernel. -/
theorem ker_posTwo_eq_range_zero_sup_pos {S Nplus Nminus : Module.End ℝ V}
    (hS : S * S * S = S) (hplus : Nplus ∈ fiveGradeRange S .posTwo)
    (hprod : Nminus * Nplus = projNeg S) :
    LinearMap.ker Nplus =
      LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) := by
  apply le_antisymm
  · intro v hv
    have hNv : Nplus v = 0 := hv
    have hneg : projNeg S v = 0 := by
      rw [← hprod]
      change Nminus (Nplus v) = 0
      rw [hNv, map_zero]
    have hrec := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id (T := S))
    change projPos S v + projZero S v + projNeg S v = v at hrec
    rw [hneg, add_zero] at hrec
    have heq : v = projZero S v + projPos S v := by
      simpa only [add_comm] using hrec.symm
    rw [heq]
    exact Submodule.add_mem _
      ((le_sup_left : LinearMap.range (projZero S) ≤
        LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S)) ⟨v, rfl⟩)
      ((le_sup_right : LinearMap.range (projPos S) ≤
        LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S)) ⟨v, rfl⟩)
  · exact range_zero_sup_pos_le_ker hS hplus

/-- A normalized left inverse on the positive range determines the negative
extreme operator's full kernel. -/
theorem ker_negTwo_eq_range_zero_sup_neg {S Nplus Nminus : Module.End ℝ V}
    (hS : S * S * S = S) (hminus : Nminus ∈ fiveGradeRange S .negTwo)
    (hprod : Nplus * Nminus = projPos S) :
    LinearMap.ker Nminus =
      LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) := by
  apply le_antisymm
  · intro v hv
    have hNv : Nminus v = 0 := hv
    have hpos : projPos S v = 0 := by
      rw [← hprod]
      change Nplus (Nminus v) = 0
      rw [hNv, map_zero]
    have hrec := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id (T := S))
    change projPos S v + projZero S v + projNeg S v = v at hrec
    rw [hpos, zero_add] at hrec
    rw [← hrec]
    exact Submodule.add_mem _
      ((le_sup_left : LinearMap.range (projZero S) ≤
        LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S)) ⟨v, rfl⟩)
      ((le_sup_right : LinearMap.range (projNeg S) ≤
        LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S)) ⟨v, rfl⟩)
  · exact range_zero_sup_neg_le_ker hS hminus

/-- Opposite normalized extreme operators isolate the zero-mode range by
intersection of kernels. The normalization is an explicit hypothesis. -/
theorem ker_posTwo_inf_ker_negTwo_eq_range_projZero
    {S Nplus Nminus : Module.End ℝ V} (hS : S * S * S = S)
    (hplus : Nplus ∈ fiveGradeRange S .posTwo)
    (hminus : Nminus ∈ fiveGradeRange S .negTwo)
    (hpm : Nplus * Nminus = projPos S) (hmp : Nminus * Nplus = projNeg S) :
    LinearMap.ker Nplus ⊓ LinearMap.ker Nminus = LinearMap.range (projZero S) := by
  apply le_antisymm
  · intro v hv
    have hp : Nplus v = 0 := hv.1
    have hm : Nminus v = 0 := hv.2
    have hpos : projPos S v = 0 := by
      rw [← hpm]
      change Nplus (Nminus v) = 0
      rw [hm, map_zero]
    have hneg : projNeg S v = 0 := by
      rw [← hmp]
      change Nminus (Nplus v) = 0
      rw [hp, map_zero]
    refine ⟨v, ?_⟩
    have hrec := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id (T := S))
    change projPos S v + projZero S v + projNeg S v = v at hrec
    simpa only [hpos, hneg, zero_add, add_zero] using hrec
  · exact le_inf
      (LinearMap.range_le_ker_iff.mpr (posTwo_mul_projZero_eq_zero hS hplus))
      (LinearMap.range_le_ker_iff.mpr (negTwo_mul_projZero_eq_zero hS hminus))

end Endomorphisms

section Algebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The positive projector fixes every positive extreme operator on the left. -/
theorem projPos_mul_posTwo_eq_self {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .posTwo) : projPos S * N = N := by
  rcases hN with ⟨X, rfl⟩
  change projPos S * (projPos S * (X * projNeg S)) = projPos S * (X * projNeg S)
  rw [← mul_assoc, projPos_idempotent hS]

/-- The negative projector fixes every negative extreme operator on the left. -/
theorem projNeg_mul_negTwo_eq_self {S N : A} (hS : S * S * S = S)
    (hN : N ∈ fiveGradeRange S .negTwo) : projNeg S * N = N := by
  rcases hN with ⟨X, rfl⟩
  change projNeg S * (projNeg S * (X * projPos S)) = projNeg S * (X * projPos S)
  rw [← mul_assoc, projNeg_idempotent hS]

end Algebra

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The zero and positive spectral ranges form a direct sum inside their join. -/
theorem range_projZero_disjoint_range_projPos {S : Module.End ℝ V}
    (hS : S * S * S = S) :
    Disjoint (LinearMap.range (projZero S)) (LinearMap.range (projPos S)) := by
  exact Disjoint.mono_right
    (LinearMap.range_le_ker_iff.mpr (projZero_mul_projPos_eq_zero hS))
    (LinearMap.IsIdempotentElem.isCompl (projZero_idempotent hS)).disjoint

/-- The zero and negative spectral ranges form a direct sum inside their join. -/
theorem range_projZero_disjoint_range_projNeg {S : Module.End ℝ V}
    (hS : S * S * S = S) :
    Disjoint (LinearMap.range (projZero S)) (LinearMap.range (projNeg S)) := by
  exact Disjoint.mono_right
    (LinearMap.range_le_ker_iff.mpr (projZero_mul_projNeg_eq_zero hS))
    (LinearMap.IsIdempotentElem.isCompl (projZero_idempotent hS)).disjoint

/-- A nonzero positive extreme operator forces a proper positive enlargement. -/
theorem range_projZero_lt_sup_range_projPos {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .posTwo) (hne : N ≠ 0) :
    LinearMap.range (projZero S) <
      LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) := by
  apply left_lt_sup.mpr
  intro hle
  have hzero : projPos S = 0 := LinearMap.range_eq_bot.mp
    ((range_projZero_disjoint_range_projPos hS).eq_bot_of_ge hle)
  have htarget := projPos_mul_posTwo_eq_self hS hN
  rw [hzero, zero_mul] at htarget
  exact hne htarget.symm

/-- A nonzero negative extreme operator forces a proper negative enlargement. -/
theorem range_projZero_lt_sup_range_projNeg {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ fiveGradeRange S .negTwo) (hne : N ≠ 0) :
    LinearMap.range (projZero S) <
      LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) := by
  apply left_lt_sup.mpr
  intro hle
  have hzero : projNeg S = 0 := LinearMap.range_eq_bot.mp
    ((range_projZero_disjoint_range_projNeg hS).eq_bot_of_ge hle)
  have htarget := projNeg_mul_negTwo_eq_self hS hN
  rw [hzero, zero_mul] at htarget
  exact hne htarget.symm

end Endomorphisms

end InfoGeometry.Core.TripotentExtremeKernels
