/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentIntegerGrading
import InfoGeometry.Core.TripotentSpectralSubmodule
import InfoGeometry.Core.TripotentJordanPair
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Star involutions and tripotent Lie grades

A real-linear ring star reverses the adjoint action. A self-adjoint generator
therefore exchanges opposite grades under star, whereas a skew-adjoint
generator preserves each grade. The skew-adjoint submodule is an ordinary
Lie subalgebra; its odd anticommutators are self-adjoint instead.

These are conditional algebraic statements about a specified star. No positive
C-star structure or existence of a second Krein involution is assumed.
-/

noncomputable section

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- An anti-involution reverses the adjoint action. -/
theorem star_adOp (S X : A) :
    star (adOp S X) = -adOp (star S) (star X) := by
  simp only [adOp, star_sub, star_mul]
  abel

/-- A skew-adjoint grading element makes star commute with its adjoint action. -/
theorem star_adOp_of_star_eq_neg {S : A} (hSstar : star S = -S) (X : A) :
    star (adOp S X) = adOp S (star X) := by
  rw [star_adOp, hSstar]
  unfold adOp
  noncomm_ring

/-- Star reverses integer weights for a self-adjoint generator. -/
theorem star_mem_adGrade_neg_of_selfAdjoint {S X : A} {k : ℤ}
    (hSstar : star S = S) (hX : X ∈ adGrade S k) :
    star X ∈ adGrade S (-k) := by
  have h := congrArg star (mem_adGrade_iff.mp hX)
  simp only [star_adOp, hSstar, star_smul, star_trivial] at h
  rw [mem_adGrade_iff, Int.cast_neg]
  calc
    adOp S (star X) = -(-adOp S (star X)) := by simp
    _ = -((k : ℝ) • star X) := congrArg Neg.neg h
    _ = (-(k : ℝ)) • star X := by simp

/-- Star preserves every integer weight for a skew-adjoint generator. -/
theorem star_mem_adGrade_of_skewAdjoint {S X : A} {k : ℤ}
    (hSstar : star S = -S) (hX : X ∈ adGrade S k) :
    star X ∈ adGrade S k := by
  have h := congrArg star (mem_adGrade_iff.mp hX)
  simpa only [star_adOp_of_star_eq_neg hSstar, star_smul, star_trivial,
    ← mem_adGrade_iff] using h

/-- All nonzero-degree skew-adjoint eigenvectors vanish for a self-adjoint
generator. Tripotence is not needed for this obstruction. -/
theorem eq_zero_of_skewAdjoint_mem_adGrade_of_selfAdjoint {S X : A} {k : ℤ}
    (hSstar : star S = S) (hXstar : star X = -X)
    (hX : X ∈ adGrade S k) (hk : k ≠ 0) : X = 0 := by
  have hminus : X ∈ adGrade S (-k) := by
    simpa only [hXstar, neg_neg] using
      (adGrade S (-k)).neg_mem (star_mem_adGrade_neg_of_selfAdjoint hSstar hX)
  have hzero : ((k : ℝ) - ((-k : ℤ) : ℝ)) • X = 0 := by
    rw [sub_smul, ← mem_adGrade_iff.mp hX, ← mem_adGrade_iff.mp hminus, sub_self]
  have hne : (k : ℝ) ≠ ((-k : ℤ) : ℝ) := by
    intro h
    have hi : k = -k := Int.cast_injective h
    exact hk (by omega)
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

/-- Ordinary commutators of skew-adjoint elements are skew-adjoint. -/
theorem star_commutator_of_skewAdjoint {X Y : A}
    (hX : star X = -X) (hY : star Y = -Y) :
    star (X * Y - Y * X) = -(X * Y - Y * X) := by
  simp only [star_sub, star_mul, hX, hY]
  noncomm_ring

/-- Odd anticommutators are self-adjoint, so ordinary star-skew closure must
not be reused as a superbracket closure theorem. -/
theorem star_anticommutator_of_skewAdjoint {X Y : A}
    (hX : star X = -X) (hY : star Y = -Y) :
    star (X * Y + Y * X) = X * Y + Y * X := by
  simp only [star_add, star_mul, hX, hY]
  noncomm_ring

/-- The native skew-adjoint submodule with its proved ordinary Lie closure. -/
def starSkewLieSubalgebra : LieSubalgebra ℝ A :=
  { skewAdjoint.submodule ℝ A with
    lie_mem' := by
      intro X Y hX hY
      exact star_commutator_of_skewAdjoint hX hY }

/-- The actual extreme skew-adjoint intersections form the existing Jordan
pair structure. Their nontriviality is not assumed or asserted. -/
def skewAdjointExtremeJordanPair (S : A) (hS : S * S * S = S) :
    TKKJordanPairData.JordanPair ℝ :=
  InfoGeometry.Core.TripotentJordanPair.tripotentExtremeJordanPair
    starSkewLieSubalgebra S hS

/-- For a skew element, stability under `ad S` has the exact centralizer
criterion `ad (S + star S) X = 0`. -/
theorem adOp_skewAdjoint_iff {S X : A} (hXstar : star X = -X) :
    star (adOp S X) = -adOp S X ↔ adOp (S + star S) X = 0 := by
  have hstar : star (adOp S X) = adOp (star S) X := by
    rw [star_adOp, hXstar]
    unfold adOp
    noncomm_ring
  have hadd : adOp (S + star S) X = adOp S X + adOp (star S) X := by
    unfold adOp
    noncomm_ring
  rw [hstar, hadd]
  constructor
  · intro h
    rw [h, add_neg_cancel]
  · intro h
    have := congrArg (fun Z : A => -adOp S X + Z) h
    simpa only [← add_assoc, neg_add_cancel, zero_add, add_zero] using this

/-- A skew-adjoint generator preserves the entire native skew-adjoint submodule. -/
theorem ad_mem_skewAdjoint_of_star_eq_neg {S : A} (hSstar : star S = -S)
    {X : A} (hX : X ∈ skewAdjoint.submodule ℝ A) :
    LieAlgebra.ad ℝ A S X ∈ skewAdjoint.submodule ℝ A := by
  change star (adOp S X) = -adOp S X
  have hXstar : star X = -X := hX
  rw [star_adOp_of_star_eq_neg hSstar, hXstar]
  exact map_neg (adLinear S) X

/-- A skew-adjoint tripotent splits the skew-adjoint Lie algebra internally
into its five homogeneous intersections. No corner-invariance is assumed. -/
theorem skewAdjoint_fiveGrade_isInternal {S : A}
    (hS : S * S * S = S) (hSstar : star S = -S) :
    DirectSum.IsInternal (fun k : FiveGrade =>
      (fiveGradeRange S k).comap (skewAdjoint.submodule ℝ A).subtype) :=
  isInternal_fiveGradeRange_comap_of_ad_invariant hS (skewAdjoint.submodule ℝ A)
    (fun _ hX => ad_mem_skewAdjoint_of_star_eq_neg hSstar hX)

/-- Star exchanges the positive and negative spectral projectors. -/
theorem star_projPos_of_star_eq_neg {S : A} (hSstar : star S = -S) :
    star (projPos S) = projNeg S := by
  simp [projPos, projNeg, star_smul, hSstar, sub_eq_add_neg]

theorem star_projNeg_of_star_eq_neg {S : A} (hSstar : star S = -S) :
    star (projNeg S) = projPos S := by
  simp [projPos, projNeg, star_smul, hSstar]

theorem star_projZero_of_star_eq_neg {S : A} (hSstar : star S = -S) :
    star (projZero S) = projZero S := by
  simp [projZero, hSstar]

/-- The middle corner of a skew element is itself skew-adjoint. -/
theorem star_middle_corner_of_skewAdjoint {S X : A}
    (hSstar : star S = -S) (hXstar : star X = -X) :
    star (projZero S * X * projZero S) = -(projZero S * X * projZero S) := by
  simp only [star_mul, star_projZero_of_star_eq_neg hSstar, hXstar]
  noncomm_ring

/-- The paired outer diagonal sector has zero intersection with the middle
corner. Compression by the middle projector detects the latter uniquely. -/
theorem paired_corner_eq_middle_implies_zero {S X Y : A}
    (hS : S * S * S = S) (hSstar : star S = -S)
    (h : projPos S * X * projPos S - star (projPos S * X * projPos S) =
      projZero S * Y * projZero S) :
    projZero S * Y * projZero S = 0 := by
  have hout : projZero S *
      (projPos S * X * projPos S - star (projPos S * X * projPos S)) *
      projZero S = 0 := by
    simp only [star_mul, star_projPos_of_star_eq_neg hSstar,
      mul_sub, sub_mul, ← mul_assoc, projZero_mul_projPos_eq_zero hS,
      projZero_mul_projNeg_eq_zero hS, zero_mul, sub_self]
  have hmid : projZero S * (projZero S * Y * projZero S) * projZero S =
      projZero S * Y * projZero S := by
    calc
      _ = (projZero S * projZero S) * Y * (projZero S * projZero S) := by
        noncomm_ring
      _ = _ := by rw [projZero_idempotent hS]
  have hc := congrArg (fun Z : A => projZero S * Z * projZero S) h
  exact hmid.symm.trans (hc.symm.trans hout)

/-- In degree zero the positive and negative diagonal blocks are paired by
star, with the middle skew block as the remaining component. -/
theorem skew_gradeZero_corner_decomposition {S X : A}
    (hS : S * S * S = S) (hSstar : star S = -S) (hXstar : star X = -X)
    (hX : X ∈ adGrade S 0) :
    X = (projPos S * X * projPos S - star (projPos S * X * projPos S)) +
      projZero S * X * projZero S := by
  have hX' : X ∈ fiveGradeRange S .zero := by
    rw [fiveGradeRange_eq_adGrade hS]
    exact hX
  have hfixed := (mem_fiveGradeRange_iff_projector_fixed hS .zero).mp hX'
  change projPos S * (X * projPos S) + projZero S * (X * projZero S) +
    projNeg S * (X * projNeg S) = X at hfixed
  calc
    X = projPos S * (X * projPos S) + projZero S * (X * projZero S) +
        projNeg S * (X * projNeg S) := hfixed.symm
    _ = _ := by
      simp only [star_mul, star_projPos_of_star_eq_neg hSstar, hXstar]
      noncomm_ring

/-- In degree one the two adjacent blocks are likewise paired by star. -/
theorem skew_gradeOne_corner_decomposition {S X : A}
    (hS : S * S * S = S) (hSstar : star S = -S) (hXstar : star X = -X)
    (hX : X ∈ adGrade S 1) :
    X = projPos S * X * projZero S - star (projPos S * X * projZero S) := by
  have hX' : X ∈ fiveGradeRange S .posOne := by
    rw [fiveGradeRange_eq_adGrade hS]
    exact hX
  have hfixed := (mem_fiveGradeRange_iff_projector_fixed hS .posOne).mp hX'
  change projPos S * (X * projZero S) + projZero S * (X * projNeg S) = X at hfixed
  calc
    X = projPos S * (X * projZero S) + projZero S * (X * projNeg S) := hfixed.symm
    _ = _ := by
      simp only [star_mul, star_projPos_of_star_eq_neg hSstar,
        star_projZero_of_star_eq_neg hSstar, hXstar]
      noncomm_ring

end InfoGeometry.Core.TripotentAdjoint
