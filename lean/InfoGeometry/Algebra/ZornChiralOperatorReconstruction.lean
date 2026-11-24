/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornLeftMajorana
import InfoGeometry.Algebra.ZornLeftCAR

/-!
# Real chiral reconstruction in the existing Zorn operator algebra

The carrier, multiplication, and six Majorana operators are the existing
`ZornVectorMatrix ℝ`, `mul`, and `leftMajoranaPlus` / `leftMajoranaMinus`.
The seventh positive-square direction is the existing diagonal difference.
The full seven-dimensional Clifford lift and its noninjectivity belong to
`Lie.SplitOctonionCliffordAction` and `Lie.SplitOctonionCliffordNoninjective`.

For the supplied convention, `qHyper i = V i - U i` and
`qCut7 = E22 - E11`; consequently their left actions are the negatives of
`leftMajoranaMinus` and the diagonal-difference action used below.
The exact associator witness is `-2 qCut7`, not `2 qCut7`.

Source: the two Zorn drafts supplied on 2026-11-24. This file contains only
the operator identities missing from the inspected owners, without defining
a second octonion carrier or a second Clifford representation.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornLeftCAR

/-- The two existing left-regular APIs act identically on the same real carrier. -/
theorem leftMultiplication_eq_L_map (X : ZornVectorMatrix ℝ) :
    leftMultiplication X = L_map (R := ℝ) X := by
  apply LinearMap.ext
  intro Y
  rfl

end InfoGeometry.Algebra.ZornLeftCAR

namespace InfoGeometry.Algebra.ZornVectorMatrix

section Ring

variable {R : Type*} [CommRing R]

/-- The two actual Peirce left projectors resolve the identity. -/
theorem left_E11_add_left_E22 :
    L_map (R := R) (E11 : ZornVectorMatrix R) + L_map (R := R) E22 = 1 := by
  apply LinearMap.ext
  intro X
  change add (mul E11 X) (mul E22 X) = X
  ext i <;> simp [mul, E11, E22, add, ZornVec3.dot, ZornVec3.cross]

/-- Their difference is the seventh positive-square operator. -/
theorem left_E11_sub_left_E22 :
    L_map (R := R) (E11 : ZornVectorMatrix R) - L_map (R := R) E22 =
      L_map (R := R) (diagonal 1 (-1)) := by
  apply LinearMap.ext
  intro X
  change sub (mul E11 X) (mul E22 X) = mul (diagonal 1 (-1)) X
  ext i <;> simp [mul, E11, E22, diagonal, sub, add, neg,
    ZornVec3.dot, ZornVec3.cross]

end Ring

/-- Reconstruction of the positive chiral operator over the real scalars. -/
theorem left_E11_reconstruction :
    L_map (R := ℝ) (E11 : ZornVectorMatrix ℝ) =
      (1 / 2 : ℝ) • (1 + L_map (R := ℝ) (diagonal 1 (-1))) := by
  apply LinearMap.ext
  intro X
  change mul E11 X = smul (1 / 2 : ℝ) (add X (mul (diagonal 1 (-1)) X))
  ext i <;> simp [mul, E11, diagonal, smul, add, ZornVec3.dot, ZornVec3.cross] <;> ring

/-- Reconstruction of the negative chiral operator over the real scalars. -/
theorem left_E22_reconstruction :
    L_map (R := ℝ) (E22 : ZornVectorMatrix ℝ) =
      (1 / 2 : ℝ) • (1 - L_map (R := ℝ) (diagonal 1 (-1))) := by
  apply LinearMap.ext
  intro X
  change mul E22 X = smul (1 / 2 : ℝ) (sub X (mul (diagonal 1 (-1)) X))
  ext i <;> simp [mul, E22, diagonal, smul, sub, add, neg,
    ZornVec3.dot, ZornVec3.cross] <;> ring

/-- Recover the upper nilpotent action from the existing two Majorana actions. -/
theorem left_U_reconstruction (i : Fin 3) :
    L_map (R := ℝ) (U (R := ℝ) i) =
      (1 / 2 : ℝ) • (leftMajoranaPlus (ZornVec3.basis i) +
        leftMajoranaMinus (ZornVec3.basis i)) := by
  rw [leftMajoranaPlus_basis, leftMajoranaMinus_basis]
  module

/-- Recover the lower nilpotent action from the same two Majorana actions. -/
theorem left_V_reconstruction (i : Fin 3) :
    L_map (R := ℝ) (V (R := ℝ) i) =
      (1 / 2 : ℝ) • (leftMajoranaPlus (ZornVec3.basis i) -
        leftMajoranaMinus (ZornVec3.basis i)) := by
  rw [leftMajoranaPlus_basis, leftMajoranaMinus_basis]
  module

/-- The ordered source generators `(q₁,q₂,q₃,q₄,q₅,q₆,q₇)` have volume `-I`.
This is an identity of associative operators, not an octonion reassociation. -/
theorem leftMajorana_source_ordered_volume :
    (-leftMajoranaMinus (ZornVec3.basis (R := ℝ) 0)) *
      (-leftMajoranaMinus (ZornVec3.basis 1)) *
      (-leftMajoranaMinus (ZornVec3.basis 2)) *
      leftMajoranaPlus (ZornVec3.basis 0) *
      leftMajoranaPlus (ZornVec3.basis 1) *
      leftMajoranaPlus (ZornVec3.basis 2) *
      (-L_map (R := ℝ) (diagonal 1 (-1))) = -1 := by
  apply LinearMap.ext
  intro X
  ext i <;> (try fin_cases i) <;>
    simp [Module.End.mul_apply, leftMajoranaMinus, leftMajoranaPlus,
      L_map, mul, offDiagonal, diagonal, ZornVec3.basis, ZornVec3.dot,
      ZornVec3.cross, neg]

/-- Evaluation of the actual operator-composition defect on the third split
direction gives `2 (E11-E22)`, equivalently `-2 qCut7` in the supplied convention. -/
theorem leftMajoranaPlus_associator_witness :
    ((leftMajoranaPlus (ZornVec3.basis (R := ℝ) 0) *
        leftMajoranaPlus (ZornVec3.basis 1) -
      L_map (R := ℝ)
        (mul (offDiagonal (ZornVec3.basis 0) (ZornVec3.basis 0))
          (offDiagonal (ZornVec3.basis 1) (ZornVec3.basis 1)))) :
        Module.End ℝ (ZornVectorMatrix ℝ))
      (offDiagonal (ZornVec3.basis 2) (ZornVec3.basis 2)) =
        (2 : ℝ) • diagonal (R := ℝ) 1 (-1) := by
  change sub
      (mul (offDiagonal (ZornVec3.basis 0) (ZornVec3.basis 0))
        (mul (offDiagonal (ZornVec3.basis 1) (ZornVec3.basis 1))
          (offDiagonal (ZornVec3.basis 2) (ZornVec3.basis 2))))
      (mul (mul (offDiagonal (ZornVec3.basis 0) (ZornVec3.basis 0))
          (offDiagonal (ZornVec3.basis 1) (ZornVec3.basis 1)))
        (offDiagonal (ZornVec3.basis 2) (ZornVec3.basis 2))) =
      smul (2 : ℝ) (diagonal 1 (-1))
  ext i <;> (try fin_cases i) <;>
    norm_num [mul, offDiagonal, diagonal, sub, add, neg, smul,
      ZornVec3.basis, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- The exact witness rules out multiplicativity on these positive-square
generators, even though their operators satisfy the Clifford relations. -/
theorem leftMajoranaPlus_not_multiplicative :
    leftMajoranaPlus (ZornVec3.basis (R := ℝ) 0) *
        leftMajoranaPlus (ZornVec3.basis 1) ≠
      L_map (R := ℝ)
        (mul (offDiagonal (ZornVec3.basis 0) (ZornVec3.basis 0))
          (offDiagonal (ZornVec3.basis 1) (ZornVec3.basis 1))) := by
  intro h
  have hw := leftMajoranaPlus_associator_witness
  rw [h, _root_.sub_self] at hw
  have ha := congrArg ZornVectorMatrix.a hw
  norm_num [diagonal, smul, zero] at ha

end InfoGeometry.Algebra.ZornVectorMatrix
