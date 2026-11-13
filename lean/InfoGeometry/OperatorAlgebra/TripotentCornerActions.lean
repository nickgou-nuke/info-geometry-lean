/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading

/-!
# Extreme corners acting on the original module

A nonzero extreme endomorphism has kernel strictly larger than the middle
projector range. A pair with the stated two product identities recovers that
range as the intersection of its kernels. These are statements about the
actual action on an arbitrary real module, not scalar corner surrogates.
The product identities are sufficient hypotheses, not a necessary criterion.
-/

namespace InfoGeometry.OperatorAlgebra.TripotentCornerActions

open InfoGeometry.Physics.Algebra
open InfoGeometry.Core.TripotentAdjoint

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- Positive extreme membership is the corner with negative input and positive output. -/
theorem mem_adGrade_two_iff_corner {S N : A} (hS : S * S * S = S) :
    N ∈ adGrade S 2 ↔ projPos S * (N * projNeg S) = N := by
  change N ∈ adGrade S (fiveGradeValue .posTwo) ↔ _
  rw [adGrade_fiveGradeValue hS]
  exact mem_fiveGradeRange_iff_projector_fixed hS .posTwo

/-- Negative extreme membership is exactly the reversed corner. -/
theorem mem_adGrade_neg_two_iff_corner {S N : A} (hS : S * S * S = S) :
    N ∈ adGrade S (-2) ↔ projNeg S * (N * projPos S) = N := by
  change N ∈ adGrade S (fiveGradeValue .negTwo) ↔ _
  rw [adGrade_fiveGradeValue hS]
  exact mem_fiveGradeRange_iff_projector_fixed hS .negTwo

/-- A corner annihilates every right projector with a different input label. -/
theorem corner_mul_projector_eq_zero {S N : A} (hS : S * S * S = S)
    {a b c : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N)
    (hbc : b ≠ c) : N * peirceProjector S c = 0 := by
  calc
    N * peirceProjector S c =
        (peirceProjector S a * (N * peirceProjector S b)) * peirceProjector S c :=
      congrArg (fun x => x * peirceProjector S c) hN.symm
    _ = peirceProjector S a * (N * (peirceProjector S b * peirceProjector S c)) := by
      simp only [mul_assoc]
    _ = 0 := by rw [peirceProjector_mul_eq_zero_of_ne hS hbc]; simp

/-- A corner is annihilated on the left away from its output label. -/
theorem projector_mul_corner_eq_zero {S N : A} (hS : S * S * S = S)
    {a b c : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N)
    (hca : c ≠ a) : peirceProjector S c * N = 0 := by
  calc
    peirceProjector S c * N =
        peirceProjector S c * (peirceProjector S a * (N * peirceProjector S b)) :=
      congrArg (fun x => peirceProjector S c * x) hN.symm
    _ = (peirceProjector S c * peirceProjector S a) * (N * peirceProjector S b) := by
      simp only [mul_assoc]
    _ = 0 := by rw [peirceProjector_mul_eq_zero_of_ne hS hca]; simp

/-- Every corner is supported on its input projector. -/
theorem corner_mul_input_projector {S N : A} (hS : S * S * S = S)
    {a b : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N) :
    N * peirceProjector S b = N := by
  calc
    N * peirceProjector S b =
        (peirceProjector S a * (N * peirceProjector S b)) * peirceProjector S b :=
      congrArg (fun x => x * peirceProjector S b) hN.symm
    _ = peirceProjector S a * (N * (peirceProjector S b * peirceProjector S b)) := by
      simp only [mul_assoc]
    _ = N := by rw [peirceProjector_mul_self hS]; exact hN

/-- An off-diagonal corner has square zero in the original algebra. -/
theorem corner_square_eq_zero {S N : A} (hS : S * S * S = S)
    {a b : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N)
    (hab : a ≠ b) : N * N = 0 := by
  calc
    N * N = N * (peirceProjector S a * (N * peirceProjector S b)) :=
      congrArg (fun x => N * x) hN.symm
    _ = (N * peirceProjector S a) * (N * peirceProjector S b) := by
      simp only [mul_assoc]
    _ = 0 := by rw [corner_mul_projector_eq_zero hS hN hab.symm]; simp

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Distinct Peirce projector ranges have zero intersection on the module. -/
theorem disjoint_peirce_projector_ranges {S : Module.End ℝ V}
    (hS : S * S * S = S) {a b : PeirceSign} (hab : a ≠ b) :
    Disjoint (LinearMap.range (peirceProjector S a))
      (LinearMap.range (peirceProjector S b)) := by
  rw [Submodule.disjoint_def]
  rintro v ⟨x, hx⟩ ⟨y, hy⟩
  have hfix : peirceProjector S a v = v := by
    rw [← hx]
    exact congrArg (fun T : Module.End ℝ V => T x) (peirceProjector_mul_self hS a)
  have hz : peirceProjector S a v = 0 := by
    rw [← hy]
    exact congrArg (fun T : Module.End ℝ V => T y)
      (peirceProjector_mul_eq_zero_of_ne hS hab)
  exact hfix.symm.trans hz

/-- A nonzero corner with a nonmiddle output makes the sum of the middle
and output ranges strictly larger than the middle range. -/
theorem middle_range_lt_sup_output_range {S N : Module.End ℝ V}
    (hS : S * S * S = S) {a b : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N)
    (ha : a ≠ .zero) (hne : N ≠ 0) :
    LinearMap.range (projZero S) <
      LinearMap.range (projZero S) ⊔ LinearMap.range (peirceProjector S a) := by
  refine lt_iff_le_not_ge.mpr ⟨le_sup_left, ?_⟩
  intro hback
  apply hne
  ext v
  have houtput : N v ∈ LinearMap.range (peirceProjector S a) :=
    ⟨N (peirceProjector S b v), congrArg (fun T : Module.End ℝ V => T v) hN⟩
  have hsum : N v ∈ LinearMap.range (projZero S) ⊔
      LinearMap.range (peirceProjector S a) :=
    (show LinearMap.range (peirceProjector S a) ≤
      LinearMap.range (projZero S) ⊔ LinearMap.range (peirceProjector S a) from
        le_sup_right) houtput
  have hmiddle : N v ∈ LinearMap.range (projZero S) := hback hsum
  exact (Submodule.disjoint_def.mp (disjoint_peirce_projector_ranges hS ha.symm))
    (N v) hmiddle houtput

/-- Every right-annihilated projector range lies in the actual operator kernel. -/
theorem projector_range_le_corner_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) {a b c : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N) (hbc : b ≠ c) :
    LinearMap.range (peirceProjector S c) ≤ LinearMap.ker N := by
  rintro _ ⟨v, rfl⟩
  have h := congrArg (fun T : Module.End ℝ V => T v)
    (corner_mul_projector_eq_zero hS hN hbc)
  exact h

/-- Nonzero off-diagonal corners avoiding the middle sector have kernel
strictly larger than the middle range. Nonzero means nonzero as an operator. -/
theorem middle_range_lt_corner_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) {a b : PeirceSign}
    (hN : peirceProjector S a * (N * peirceProjector S b) = N)
    (ha : a ≠ .zero) (hb : b ≠ .zero) (hab : a ≠ b) (hne : N ≠ 0) :
    LinearMap.range (projZero S) < LinearMap.ker N := by
  refine lt_iff_le_not_ge.mpr
    ⟨projector_range_le_corner_ker hS hN hb, ?_⟩
  intro hback
  apply hne
  ext v
  have hk : N v ∈ LinearMap.ker N :=
    congrArg (fun T : Module.End ℝ V => T v) (corner_square_eq_zero hS hN hab)
  obtain ⟨w, hw⟩ := hback hk
  have hfix : projZero S (N v) = N v := by
    calc
      projZero S (N v) = projZero S (projZero S w) := congrArg (projZero S) hw.symm
      _ = projZero S w :=
        congrArg (fun T : Module.End ℝ V => T w) (projZero_idempotent hS)
      _ = N v := hw
  have hz : projZero S (N v) = 0 :=
    congrArg (fun T : Module.End ℝ V => T v)
      (projector_mul_corner_eq_zero hS hN ha.symm)
  exact hfix.symm.trans hz

/-- The negative extreme kernel contains the middle and negative ranges. -/
theorem range_zero_sup_range_neg_le_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S (-2)) :
    LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) ≤ LinearMap.ker N := by
  have hc := (mem_adGrade_neg_two_iff_corner hS).mp hN
  exact sup_le
    (projector_range_le_corner_ker hS (a := .neg) (b := .pos) (c := .zero) hc (by decide))
    (projector_range_le_corner_ker hS (a := .neg) (b := .pos) (c := .neg) hc (by decide))

/-- The positive extreme kernel contains the middle and positive ranges. -/
theorem range_zero_sup_range_pos_le_ker {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S 2) :
    LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) ≤ LinearMap.ker N := by
  have hc := (mem_adGrade_two_iff_corner hS).mp hN
  exact sup_le
    (projector_range_le_corner_ker hS (a := .pos) (b := .neg) (c := .zero) hc (by decide))
    (projector_range_le_corner_ker hS (a := .pos) (b := .neg) (c := .pos) hc (by decide))

/-- A single nonzero negative extreme cannot recover the middle range as its kernel. -/
theorem range_zero_lt_ker_neg_two {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S (-2)) (hne : N ≠ 0) :
    LinearMap.range (projZero S) < LinearMap.ker N :=
  middle_range_lt_corner_ker hS (a := .neg) (b := .pos)
    ((mem_adGrade_neg_two_iff_corner hS).mp hN)
    (by decide) (by decide) (by decide) hne

/-- The same strict obstruction holds for a nonzero positive extreme. -/
theorem range_zero_lt_ker_two {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S 2) (hne : N ≠ 0) :
    LinearMap.range (projZero S) < LinearMap.ker N :=
  middle_range_lt_corner_ker hS (a := .pos) (b := .neg)
    ((mem_adGrade_two_iff_corner hS).mp hN)
    (by decide) (by decide) (by decide) hne

/-- The full strict negative-kernel chain; the two summand ranges are
disjoint by `disjoint_peirce_projector_ranges`. -/
theorem negative_extreme_kernel_chain {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S (-2)) (hne : N ≠ 0) :
    (LinearMap.range (projZero S) <
      LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S)) ∧
    (LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) ≤ LinearMap.ker N) :=
  ⟨middle_range_lt_sup_output_range hS (a := .neg) (b := .pos)
      ((mem_adGrade_neg_two_iff_corner hS).mp hN)
      (by decide) hne,
    range_zero_sup_range_neg_le_ker hS hN⟩

/-- The corresponding strict positive-kernel chain. -/
theorem positive_extreme_kernel_chain {S N : Module.End ℝ V}
    (hS : S * S * S = S) (hN : N ∈ adGrade S 2) (hne : N ≠ 0) :
    (LinearMap.range (projZero S) <
      LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S)) ∧
    (LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) ≤ LinearMap.ker N) :=
  ⟨middle_range_lt_sup_output_range hS (a := .pos) (b := .neg)
      ((mem_adGrade_two_iff_corner hS).mp hN)
      (by decide) hne,
    range_zero_sup_range_pos_le_ker hS hN⟩

/-- A left inverse on the positive support determines the negative operator's kernel. -/
theorem dual_negative_kernel_eq {S Nplus Nminus : Module.End ℝ V}
    (hS : S * S * S = S) (hm : Nminus ∈ adGrade S (-2))
    (hpm : Nplus * Nminus = projPos S) :
    LinearMap.ker Nminus =
      LinearMap.range (projZero S) ⊔ LinearMap.range (projNeg S) := by
  apply le_antisymm
  · intro v hv
    have hv' : Nminus v = 0 := hv
    have hpv : projPos S v = 0 := by
      rw [← hpm, Module.End.mul_apply, hv', map_zero]
    apply Submodule.mem_sup.mpr
    refine ⟨projZero S v, ⟨v, rfl⟩, projNeg S v, ⟨v, rfl⟩, ?_⟩
    have hsum := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id S)
    simpa only [LinearMap.add_apply, Module.End.one_apply, hpv, zero_add] using hsum
  · exact range_zero_sup_range_neg_le_ker hS hm

/-- A left inverse on the negative support determines the positive operator's kernel. -/
theorem dual_positive_kernel_eq {S Nplus Nminus : Module.End ℝ V}
    (hS : S * S * S = S) (hp : Nplus ∈ adGrade S 2)
    (hmp : Nminus * Nplus = projNeg S) :
    LinearMap.ker Nplus =
      LinearMap.range (projZero S) ⊔ LinearMap.range (projPos S) := by
  apply le_antisymm
  · intro v hv
    have hv' : Nplus v = 0 := hv
    have hmv : projNeg S v = 0 := by
      rw [← hmp, Module.End.mul_apply, hv', map_zero]
    apply Submodule.mem_sup.mpr
    refine ⟨projZero S v, ⟨v, rfl⟩, projPos S v, ⟨v, rfl⟩, ?_⟩
    have hsum := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id S)
    simpa only [LinearMap.add_apply, Module.End.one_apply, hmv, add_zero, add_comm] using hsum
  · exact range_zero_sup_range_pos_le_ker hS hp

/-- Two dual extreme operators with the specified product equations isolate
the middle range. No necessity of those product equations is asserted. -/
theorem dual_extreme_kernel_inf {S Nplus Nminus : Module.End ℝ V}
    (hS : S * S * S = S) (hp : Nplus ∈ adGrade S 2)
    (hm : Nminus ∈ adGrade S (-2))
    (hpm : Nplus * Nminus = projPos S) (hmp : Nminus * Nplus = projNeg S) :
    LinearMap.ker Nplus ⊓ LinearMap.ker Nminus = LinearMap.range (projZero S) := by
  apply le_antisymm
  · intro v hv
    have hvp : Nplus v = 0 := hv.1
    have hvm : Nminus v = 0 := hv.2
    have hpv : projPos S v = 0 := by
      rw [← hpm, Module.End.mul_apply, hvm, map_zero]
    have hmv : projNeg S v = 0 := by
      rw [← hmp, Module.End.mul_apply, hvp, map_zero]
    refine ⟨v, ?_⟩
    have hsum := congrArg (fun T : Module.End ℝ V => T v) (proj_sum_eq_id S)
    simpa only [LinearMap.add_apply, Module.End.one_apply, hpv, hmv,
      zero_add, add_zero] using hsum
  · exact le_inf
      (le_trans le_sup_left (range_zero_sup_range_pos_le_ker hS hp))
      (le_trans le_sup_left (range_zero_sup_range_neg_le_ker hS hm))

end Endomorphisms

end InfoGeometry.OperatorAlgebra.TripotentCornerActions
