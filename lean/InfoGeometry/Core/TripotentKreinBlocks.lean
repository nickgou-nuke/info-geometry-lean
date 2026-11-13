/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.TripotentInvolution
import InfoGeometry.Core.TripotentEigenspaces

/-!
# Krein adjoints of the existing tripotent blocks

For a self-adjoint fundamental symmetry `η`, a Krein-skew grading element
exchanges its positive and negative Peirce projectors under the owned
`Krein.sharp`, while fixing the middle projector. A corner `(a, b)` is sent to
the corner obtained by exchanging the two labels and reversing both signs.

The final readbacks are identities for actual elements in the existing integer
grades. A Krein-skew element of degree zero is `C - sharp C + M`, where `C`
and `M` are its existing positive and middle diagonal projections. A Krein-skew
element of degree one is `B - sharp B`, where `B` is its existing positive-to-
middle corner. These identities neither assert nonzero components nor classify
the middle corner as a particular gauge algebra.
-/

namespace InfoGeometry.Core.TripotentAdjoint

open InfoGeometry.Physics.Algebra
open InfoGeometry.Canonical.SpinorialCore

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

private theorem swap_peirce_zero :
    Equiv.swap PeirceSign.pos PeirceSign.neg PeirceSign.zero = .zero :=
  Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

/-- Krein skewness exchanges the positive polynomial projector with the negative one. -/
theorem sharp_projPos {η S : A} (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) :
    Krein.sharp η (projPos S) = projNeg S := by
  change Krein.sharp η ((1 / 2 : ℝ) • (S * S + S)) =
    (1 / 2 : ℝ) • (S * S - S)
  calc
    Krein.sharp η ((1 / 2 : ℝ) • (S * S + S)) =
        (1 / 2 : ℝ) • Krein.sharp η (S * S + S) := by
      simp only [Krein.sharp, star_smul, star_trivial,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    _ = (1 / 2 : ℝ) • (S * S - S) := by
      simp only [Krein.sharp_add, Krein.sharp_mul η S S hη,
        hS, neg_mul_neg, sub_eq_add_neg]

/-- Involutivity gives the reverse projector exchange. -/
theorem sharp_projNeg {η S : A} (hηstar : star η = η) (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) :
    Krein.sharp η (projNeg S) = projPos S := by
  have h := congrArg (Krein.sharp η) (sharp_projPos hη hS)
  simpa only [Krein.sharp_involutive η hηstar hη (projPos S)] using h.symm

/-- The middle polynomial projector is fixed by the Krein adjoint. -/
theorem sharp_projZero {η S : A} (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) :
    Krein.sharp η (projZero S) = projZero S := by
  change Krein.sharp η (1 - S * S) = 1 - S * S
  simp only [Krein.sharp_sub, Krein.sharp_one η hη,
    Krein.sharp_mul η S S hη, hS, neg_mul_neg]

/-- Sign reversal uses the native transposition of the existing Peirce labels. -/
theorem sharp_peirceProjector {η S : A} (hηstar : star η = η)
    (hη : η * η = 1) (hS : Krein.sharp η S = -S) (a : PeirceSign) :
    Krein.sharp η (peirceProjector S a) =
      peirceProjector S (Equiv.swap PeirceSign.pos PeirceSign.neg a) := by
  cases a with
  | pos =>
      simpa only [peirceProjector, Equiv.swap_apply_left] using sharp_projPos hη hS
  | zero =>
      simpa only [peirceProjector, swap_peirce_zero] using sharp_projZero hη hS
  | neg =>
      simpa only [peirceProjector, Equiv.swap_apply_right] using
        sharp_projNeg hηstar hη hS

/-- The Krein adjoint reverses the product order and exchanges the two extreme labels. -/
theorem sharp_jointPeirceProjector {η S : A} (hηstar : star η = η)
    (hη : η * η = 1) (hS : Krein.sharp η S = -S)
    (a b : PeirceSign) (X : A) :
    Krein.sharp η (jointPeirceProjector S a b X) =
      jointPeirceProjector S
        (Equiv.swap PeirceSign.pos PeirceSign.neg b)
        (Equiv.swap PeirceSign.pos PeirceSign.neg a) (Krein.sharp η X) := by
  simp only [jointPeirceProjector_apply]
  rw [Krein.sharp_mul η (peirceProjector S a) (X * peirceProjector S b) hη,
    Krein.sharp_mul η X (peirceProjector S b) hη,
    sharp_peirceProjector hηstar hη hS b,
    sharp_peirceProjector hηstar hη hS a]
  exact mul_assoc _ _ _

/-- For a Krein-skew element, opposite reflected corners are negatives of its adjoint corners. -/
theorem sharp_jointPeirceProjector_of_skew {η S X : A}
    (hηstar : star η = η) (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) (hX : Krein.sharp η X = -X)
    (a b : PeirceSign) :
    Krein.sharp η (jointPeirceProjector S a b X) =
      -jointPeirceProjector S
        (Equiv.swap PeirceSign.pos PeirceSign.neg b)
        (Equiv.swap PeirceSign.pos PeirceSign.neg a) X := by
  rw [sharp_jointPeirceProjector hηstar hη hS, hX, map_neg]

/-- The actual middle corner of a Krein-skew element is itself Krein-skew. -/
theorem sharp_middle_corner_of_skew {η S X : A}
    (hηstar : star η = η) (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) (hX : Krein.sharp η X = -X) :
    Krein.sharp η (jointPeirceProjector S .zero .zero X) =
      -jointPeirceProjector S .zero .zero X := by
  simpa only [swap_peirce_zero] using
    sharp_jointPeirceProjector_of_skew hηstar hη hS hX .zero .zero

/-- Degree-zero skew elements are reconstructed from their actual positive diagonal
and middle diagonal corners: `X = C - sharp C + M`. -/
theorem sharpSkew_grade_zero_readback {η S X : A}
    (hηstar : star η = η) (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) (hT : S * S * S = S)
    (hX : Krein.sharp η X = -X) (hx : X ∈ adGrade S 0) :
    X = jointPeirceProjector S .pos .pos X -
        Krein.sharp η (jointPeirceProjector S .pos .pos X) +
        jointPeirceProjector S .zero .zero X := by
  have hx' : X ∈ fiveGradeRange S .zero := by
    simpa only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hT,
      fiveGradeValue] using hx
  have hrec := (mem_fiveGradeRange_iff_projector_fixed hT .zero).mp hx'
  change jointPeirceProjector S .pos .pos X +
      jointPeirceProjector S .zero .zero X +
      jointPeirceProjector S .neg .neg X = X at hrec
  have hcorner : Krein.sharp η (jointPeirceProjector S .pos .pos X) =
      -jointPeirceProjector S .neg .neg X := by
    simpa only [Equiv.swap_apply_left] using
      sharp_jointPeirceProjector_of_skew hηstar hη hS hX .pos .pos
  calc
    X = jointPeirceProjector S .pos .pos X +
        jointPeirceProjector S .zero .zero X +
        jointPeirceProjector S .neg .neg X := hrec.symm
    _ = jointPeirceProjector S .pos .pos X -
        Krein.sharp η (jointPeirceProjector S .pos .pos X) +
        jointPeirceProjector S .zero .zero X := by
      rw [hcorner, sub_neg_eq_add]
      abel

/-- Degree-one skew elements are reconstructed from their actual `(+,0)` corner:
`X = B - sharp B`. -/
theorem sharpSkew_grade_one_readback {η S X : A}
    (hηstar : star η = η) (hη : η * η = 1)
    (hS : Krein.sharp η S = -S) (hT : S * S * S = S)
    (hX : Krein.sharp η X = -X) (hx : X ∈ adGrade S 1) :
    X = jointPeirceProjector S .pos .zero X -
      Krein.sharp η (jointPeirceProjector S .pos .zero X) := by
  have hx' : X ∈ fiveGradeRange S .posOne := by
    simpa only [adGrade_eq_eigenspace, fiveGradeRange_eq_eigenspace hT,
      fiveGradeValue] using hx
  have hrec := (mem_fiveGradeRange_iff_projector_fixed hT .posOne).mp hx'
  change jointPeirceProjector S .pos .zero X +
      jointPeirceProjector S .zero .neg X = X at hrec
  have hcorner : Krein.sharp η (jointPeirceProjector S .pos .zero X) =
      -jointPeirceProjector S .zero .neg X := by
    simpa only [swap_peirce_zero, Equiv.swap_apply_left] using
      sharp_jointPeirceProjector_of_skew hηstar hη hS hX .pos .zero
  calc
    X = jointPeirceProjector S .pos .zero X +
        jointPeirceProjector S .zero .neg X := hrec.symm
    _ = jointPeirceProjector S .pos .zero X -
        Krein.sharp η (jointPeirceProjector S .pos .zero X) := by
      rw [hcorner, sub_neg_eq_add]

end InfoGeometry.Core.TripotentAdjoint
