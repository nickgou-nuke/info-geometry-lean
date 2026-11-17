/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftMajorana
import InfoGeometry.Clifford.LorentzianBivectorSignatureBridge

/-!
# Prescribed mode flips on the native Zorn module

The three positive-square operators and their three negative-square partners
already belong to `ZornLeftMajorana`. For each fixed mode, left composition
with the prescribed negative partner times the positive generator is the
unique operator sending that positive generator to its negative partner.
On the real eight-dimensional Zorn module these three mode flips are distinct,
so one operator cannot perform all three prescribed flips.

This does not rule out a common involution producing a different family of
negative-square composites. The native left diagonal grading does exactly
that: it anticommutes with every positive generator, and its product with
each such generator squares to the negative identity. The no-common-flip
theorem says that this new family cannot equal the prescribed negative
left-multiplication family in all three modes.

All products in the conclusions are ordered composition in `Module.End`.
No multiplicative embedding of the nonassociative Zorn product, uniqueness
of a basis-independent fourth structure, or physical covariance is asserted.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

noncomputable section

variable {R : Type*} [CommRing R]

/-- A fixed prescribed mode determines its left-composition flip uniquely. -/
theorem leftMajorana_mode_flip_iff (i : Fin 3)
    (T : Module.End R (ZornVectorMatrix R)) :
    T * leftMajoranaPlus (ZornVec3.basis (R := R) i) =
        leftMajoranaMinus (ZornVec3.basis i) ↔
      T = leftMajoranaMinus (ZornVec3.basis (R := R) i) *
        leftMajoranaPlus (ZornVec3.basis i) := by
  constructor
  · intro h
    have hright := congrArg
      (fun S : Module.End R (ZornVectorMatrix R) =>
        S * leftMajoranaPlus (ZornVec3.basis (R := R) i)) h
    simpa only [_root_.mul_assoc, leftMajoranaPlus_basis_square,
      _root_.mul_one] using hright
  · rintro rfl
    exact leftMajorana_mode_flip_plus i

/-- Different real modes have different flip operators. Evaluating at the
upper basis vector of the first mode gives opposite nonzero coordinates. -/
theorem leftMajorana_mode_flips_ne {i j : Fin 3} (hij : i ≠ j) :
    leftMajoranaMinus (ZornVec3.basis (R := ℝ) i) *
        leftMajoranaPlus (ZornVec3.basis i) ≠
      leftMajoranaMinus (ZornVec3.basis (R := ℝ) j) *
        leftMajoranaPlus (ZornVec3.basis j) := by
  intro h
  simp only [leftMajorana_mode_product] at h
  have heval := congrArg
    (fun T : Module.End ℝ (ZornVectorMatrix ℝ) => T (U i)) h
  change
    (L_map (R := ℝ) (U i) * L_map (V i) -
        L_map (V i) * L_map (U i) : Module.End ℝ (ZornVectorMatrix ℝ)) (U i) =
      (L_map (R := ℝ) (U j) * L_map (V j) -
        L_map (V j) * L_map (U j) : Module.End ℝ (ZornVectorMatrix ℝ)) (U i) at heval
  rw [left_mode_commutator_apply (R := ℝ) i (U i),
    left_mode_commutator_apply (R := ℝ) j (U i)] at heval
  have hcoord := congrArg (fun X : ZornVectorMatrix ℝ => X.v i) heval
  norm_num [U, ZornVec3.basis, hij] at hcoord

/-- No single real endomorphism sends all three prescribed positive native
generators to their prescribed negative partners by left composition. -/
theorem no_common_leftMajorana_mode_flip :
    ¬ ∃ T : Module.End ℝ (ZornVectorMatrix ℝ),
      ∀ i : Fin 3,
        T * leftMajoranaPlus (ZornVec3.basis (R := ℝ) i) =
          leftMajoranaMinus (ZornVec3.basis i) := by
  rintro ⟨T, hT⟩
  have hzero := (leftMajorana_mode_flip_iff 0 T).mp (hT 0)
  have hone := (leftMajorana_mode_flip_iff 1 T).mp (hT 1)
  exact leftMajorana_mode_flips_ne (i := 0) (j := 1) (by decide)
    (hzero.symm.trans hone)

/-- The diagonal grading nevertheless produces a negative-square composite
from every positive generator. This is multiplication of operators, not
similarity or an identification with the prescribed negative generator. -/
theorem left_diagonal_difference_mul_majoranaPlus_square (i : Fin 3) :
    (L_map (R := R) (diagonal (R := R) 1 (-1)) *
        leftMajoranaPlus (ZornVec3.basis (R := R) i)) *
      (L_map (R := R) (diagonal (R := R) 1 (-1)) *
        leftMajoranaPlus (ZornVec3.basis (R := R) i)) = -1 := by
  exact InfoGeometry.Clifford.LorentzianBivectorSignatureBridge.positive_bivector_sq_neg_one
    left_diagonal_difference_involution
    (leftMajoranaPlus_basis_square i)
    (left_diagonal_difference_anticommutes_offDiagonal
      (ZornVec3.basis (R := R) i) (ZornVec3.basis i))

end

end InfoGeometry.Algebra.ZornVectorMatrix
