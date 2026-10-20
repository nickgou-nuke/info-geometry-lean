/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationLinearityWave16
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationAdditivityWave17
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentationScalarLeftWave19
import InfoGeometry.Clifford.ClNNFockChiralProjectorClosure

noncomputable section

namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordSuperGradeColimit

/-- A grade-zero algebra element preserves the positive chiral projector on the
actual algebraic Fock direct limit. -/
theorem splitCliffordFockAction_grade_zero_projectorPlus
    (aInf : SplitCliffordInfinity) (ψInf : FockInfinity)
    (ha : splitCliffordInfinityInvolute aInf = aInf) :
    fockInfinityProjectorPlus
        (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction aInf (fockInfinityProjectorPlus ψInf) := by
  rw [fockInfinityProjectorPlus, fockInfinityProjectorPlus]
  rw [splitCliffordFockAction_grade_equivariant, ha]
  rw [splitCliffordFockAction_smul_right, splitCliffordFockAction_add_right]

/-- A grade-zero algebra element preserves the negative chiral projector on the
actual algebraic Fock direct limit. -/
theorem splitCliffordFockAction_grade_zero_projectorMinus
    (aInf : SplitCliffordInfinity) (ψInf : FockInfinity)
    (ha : splitCliffordInfinityInvolute aInf = aInf) :
    fockInfinityProjectorMinus
        (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction aInf (fockInfinityProjectorMinus ψInf) := by
  rw [fockInfinityProjectorMinus, fockInfinityProjectorMinus]
  rw [splitCliffordFockAction_grade_equivariant, ha]
  have h_sub (x y : FockInfinity) :
      splitCliffordFockAction aInf (x - y) =
        splitCliffordFockAction aInf x - splitCliffordFockAction aInf y := by
    rw [sub_eq_add_neg, splitCliffordFockAction_add_right]
    have h_neg : splitCliffordFockAction aInf (-y) =
        -splitCliffordFockAction aInf y := by
      calc
        splitCliffordFockAction aInf (-y) =
            splitCliffordFockAction aInf ((-1 : ℝ) • y) := by
              rw [neg_one_smul]
        _ = (-1 : ℝ) • splitCliffordFockAction aInf y :=
          splitCliffordFockAction_smul_right (-1) aInf y
        _ = -splitCliffordFockAction aInf y := by rw [neg_one_smul]
    rw [h_neg]
    rw [sub_eq_add_neg]
  rw [splitCliffordFockAction_smul_right, h_sub]

/-- A grade-one algebra element exchanges the two chiral projectors on the
actual algebraic Fock direct limit. -/
theorem splitCliffordFockAction_grade_one_projectorPlus
    (aInf : SplitCliffordInfinity) (ψInf : FockInfinity)
    (ha : splitCliffordInfinityInvolute aInf = -aInf) :
    fockInfinityProjectorPlus
        (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction aInf (fockInfinityProjectorMinus ψInf) := by
  rw [fockInfinityProjectorPlus, fockInfinityProjectorMinus]
  rw [splitCliffordFockAction_grade_equivariant, ha]
  rw [← neg_one_smul ℝ aInf, splitCliffordFockAction_smul_left]
  rw [neg_one_smul]
  have h_sub (x y : FockInfinity) :
      splitCliffordFockAction aInf (x - y) =
        splitCliffordFockAction aInf x - splitCliffordFockAction aInf y := by
    rw [sub_eq_add_neg, splitCliffordFockAction_add_right]
    have h_neg : splitCliffordFockAction aInf (-y) =
        -splitCliffordFockAction aInf y := by
      calc
        splitCliffordFockAction aInf (-y) =
            splitCliffordFockAction aInf ((-1 : ℝ) • y) := by
              rw [neg_one_smul]
        _ = (-1 : ℝ) • splitCliffordFockAction aInf y :=
          splitCliffordFockAction_smul_right (-1) aInf y
        _ = -splitCliffordFockAction aInf y := by rw [neg_one_smul]
    rw [h_neg]
    rw [sub_eq_add_neg]
  rw [splitCliffordFockAction_smul_right, h_sub]
  module

/-- A grade-one algebra element exchanges the two chiral projectors on the
actual algebraic Fock direct limit. -/
theorem splitCliffordFockAction_grade_one_projectorMinus
    (aInf : SplitCliffordInfinity) (ψInf : FockInfinity)
    (ha : splitCliffordInfinityInvolute aInf = -aInf) :
    fockInfinityProjectorMinus
        (splitCliffordFockAction aInf ψInf) =
      splitCliffordFockAction aInf (fockInfinityProjectorPlus ψInf) := by
  rw [fockInfinityProjectorMinus, fockInfinityProjectorPlus]
  rw [splitCliffordFockAction_grade_equivariant, ha]
  rw [← neg_one_smul ℝ aInf, splitCliffordFockAction_smul_left]
  rw [neg_one_smul]
  rw [splitCliffordFockAction_smul_right, splitCliffordFockAction_add_right]
  module

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
