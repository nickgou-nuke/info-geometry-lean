/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Canonical.ZornMultiplicationOperators
import InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
import InfoGeometry.Algebra.ZornDerivationBridge

/-!
# Left multiplication on the canonical split-octonion carrier

This owner records the first-quantized linear lift without treating the
nonassociative product as an associative operator representation.  The
composition defect is retained explicitly as the ordinary associator.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal
open InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity

abbrev Carrier := InfoGeometry.OperatorAlgebra.SplitOctonionPseudoReal.CanonicalZorn
abbrev State := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-- The associator defect of two left-multiplication operators. -/
def leftMulCompDefect (Z W : Carrier) : Module.End ℝ State :=
  (leftMulLinearGeneral Z).comp (leftMulLinearGeneral W) -
    leftMulLinearGeneral (Z * W)

/-- On a canonical Zorn vector, the composition defect is the coordinate
image of the negative associator with the indicated parenthesization. -/
theorem leftMulCompDefect_apply_coord (Z W X : Carrier) :
    leftMulCompDefect Z W (coordLE X) =
      -coordLE ((Z * W) * X - Z * (W * X)) := by
  change coordLE (Z * (coordLE.symm (coordLE (W * (coordLE.symm (coordLE X)))))) -
    coordLE ((Z * W) * (coordLE.symm (coordLE X))) = _
  simp only [coordLE.symm_apply_apply, map_sub]
  abel

/-- Right alternativity, transported from the native Zorn vector algebra,
polarizes to antisymmetry of the canonical associator in its last two slots. -/
private theorem canonical_associator_swap23 (X Y Z : Carrier) :
    (X * Y) * Z - X * (Y * Z) = -((X * Z) * Y - X * (Z * Y)) := by
  open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge in
  apply eq_neg_of_add_eq_zero_left
  apply canonicalVectorEquiv.injective
  simp only [canonicalVectorEquiv_add, canonicalVectorEquiv_sub,
    canonicalVectorEquiv_mul, canonicalVectorEquiv_zero]
  have h := InfoGeometry.Algebra.alternative_associator_swap23
    InfoGeometry.Algebra.zorn_right_alternative
    (canonicalVectorEquiv X) (canonicalVectorEquiv Y) (canonicalVectorEquiv Z)
  simp only [associator_apply] at h
  change ((canonicalVectorEquiv X * canonicalVectorEquiv Y) * canonicalVectorEquiv Z -
    canonicalVectorEquiv X * (canonicalVectorEquiv Y * canonicalVectorEquiv Z)) +
    ((canonicalVectorEquiv X * canonicalVectorEquiv Z) * canonicalVectorEquiv Y -
      canonicalVectorEquiv X * (canonicalVectorEquiv Z * canonicalVectorEquiv Y)) = 0
  rw [h, neg_add_cancel]

/-- The left-regular composition defect is the commutator `[R_Y,L_X]`
on the actual eight-dimensional operator carrier. The right action is the
existing canonical Zorn right multiplication transported by `coordLE`. -/
theorem leftMulCompDefect_eq_right_left_commutator (X Y : Carrier) :
    leftMulCompDefect X Y =
      (((coordLE : Carrier →ₗ[ℝ] State).comp
          ((InfoGeometry.Canonical.ZornMatrix.rightMulLinear Y).comp
            (coordLE.symm : State →ₗ[ℝ] Carrier))).comp
          (leftMulLinearGeneral X)) -
        ((leftMulLinearGeneral X).comp
          ((coordLE : Carrier →ₗ[ℝ] State).comp
            ((InfoGeometry.Canonical.ZornMatrix.rightMulLinear Y).comp
              (coordLE.symm : State →ₗ[ℝ] Carrier)))) := by
  apply LinearMap.ext
  intro v
  change coordLE (X * (Y * coordLE.symm v)) - coordLE ((X * Y) * coordLE.symm v) =
    coordLE ((X * coordLE.symm v) * Y) - coordLE (X * (coordLE.symm v * Y))
  have h := canonical_associator_swap23 X Y (coordLE.symm v)
  have hh := congrArg coordLE h
  simp only [map_sub, map_neg] at hh
  linear_combination (norm := abel) -hh

/-- Left multiplication is additive in the Zorn element, despite the
nonassociativity of Zorn multiplication. -/
theorem leftMulLinearGeneral_sub (Z W : Carrier) :
    leftMulLinearGeneral (Z - W) = leftMulLinearGeneral Z - leftMulLinearGeneral W := by
  apply LinearMap.ext
  intro v
  change coordLE ((Z - W) * coordLE.symm v) =
    coordLE (Z * coordLE.symm v) - coordLE (W * coordLE.symm v)
  have hneg : (-W) * coordLE.symm v = -(W * coordLE.symm v) := by
    simpa using (InfoGeometry.Canonical.ZornClifford.smul_mul' (-1 : ℝ) W (coordLE.symm v))
  rw [sub_eq_add_neg, InfoGeometry.Canonical.ZornClifford.add_mul', hneg, map_add, map_neg]
  rfl

/-- The failure of the left-operator commutator to match the difference of
left multiplications of the two ordered Zorn products is exactly the
antisymmetrized composition defect. No associativity of the Zorn product is
used. -/
theorem leftMul_commutator_defect (Z W : Carrier) :
    ((leftMulLinearGeneral Z).comp (leftMulLinearGeneral W) -
        (leftMulLinearGeneral W).comp (leftMulLinearGeneral Z)) -
      (leftMulLinearGeneral (Z * W) - leftMulLinearGeneral (W * Z)) =
    leftMulCompDefect Z W - leftMulCompDefect W Z := by
  unfold leftMulCompDefect
  abel

/-- The commutator of left operators differs from left multiplication by the
actual Zorn commutator by the antisymmetrized associator defect. -/
theorem leftMul_zorn_commutator_defect (Z W : Carrier) :
    ((leftMulLinearGeneral Z).comp (leftMulLinearGeneral W) -
      (leftMulLinearGeneral W).comp (leftMulLinearGeneral Z)) -
        leftMulLinearGeneral (Z * W - W * Z) =
      leftMulCompDefect Z W - leftMulCompDefect W Z := by
  rw [leftMulLinearGeneral_sub]
  exact leftMul_commutator_defect Z W

theorem leftMulCompDefect_eq_zero_iff (Z W : Carrier) :
    leftMulCompDefect Z W = 0 ↔
      ∀ X : Carrier, Z * (W * X) = (Z * W) * X := by
  constructor
  · intro h X
    have hv := congrArg (fun f : Module.End ℝ State => f (coordLE X)) h
    simp only [leftMulCompDefect, LinearMap.sub_apply, LinearMap.comp_apply,
      leftMulLinearGeneral,
      InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic.zMulLinear] at hv
    exact coordLE.injective (sub_eq_zero.mp hv)
  · intro h
    apply LinearMap.ext
    intro v
    change coordLE (Z * (W * coordLE.symm v)) -
      coordLE ((Z * W) * coordLE.symm v) = 0
    rw [h]
    simp

/-- The explicit nonzero split-octonion associator remains a nonzero
composition defect on the canonical finite operator carrier. -/
theorem leftMulCompDefect_ex_ne_zero :
    leftMulCompDefect ex_X.1 ex_Y.1 ≠ 0 := by
  intro h
  have hv := congrArg (fun f : Module.End ℝ State => f (coordLE ex_Z.1)) h
  simp only [leftMulCompDefect, LinearMap.sub_apply, LinearMap.comp_apply,
    leftMulLinearGeneral,
    InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic.zMulLinear] at hv
  have hAssocEq : ex_X.1 * (ex_Y.1 * ex_Z.1) =
      (ex_X.1 * ex_Y.1) * ex_Z.1 :=
    coordLE.injective (sub_eq_zero.mp hv)
  have hAssoc : ex_associator = 0 := by
    unfold ex_associator
    rw [← hAssocEq]
    exact sub_self _
  exact ex_associator_ne_zero hAssoc

/-- The commutator defect is genuinely nonzero for the existing explicit
imaginary split-octonion elements, not merely an abstract possibility. -/
theorem leftMul_commutator_defect_ex_ne_zero :
    leftMulCompDefect ex_X.1 ex_Y.1 - leftMulCompDefect ex_Y.1 ex_X.1 ≠ 0 := by
  intro h
  have hv := congrArg (fun f : Module.End ℝ State => f (coordLE ex_Z.1) 0) h
  simp only [LinearMap.sub_apply, LinearMap.zero_apply, leftMulCompDefect_apply_coord] at hv
  simp [coordLE, ex_X, ex_Y, ex_Z, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] at hv

/-- The existing imaginary split-octonion generators induce genuinely
noncommuting left-multiplication operators on the eight-dimensional state. -/
theorem leftMul_operators_ex_noncommute :
    (leftMulLinearGeneral ex_X.1).comp (leftMulLinearGeneral ex_Y.1) ≠
      (leftMulLinearGeneral ex_Y.1).comp (leftMulLinearGeneral ex_X.1) := by
  intro h
  have hv := congrArg (fun f : Module.End ℝ State => f (coordLE ex_Z.1) 0) h
  simp only [LinearMap.comp_apply, leftMulLinearGeneral,
    InfoGeometry.OperatorAlgebra.SplitOctonionLoxodromic.zMulLinear] at hv
  simp [coordLE, ex_X, ex_Y, ex_Z, InfoGeometry.Canonical.ZornMatrix.mul,
    InfoGeometry.Canonical.ZornMatrix.dot, InfoGeometry.Canonical.ZornMatrix.cross] at hv
  norm_num at hv

/-- The same noncommutation holds in the actual real 8×8 matrix realization. -/
theorem leftMulMatrix_ex_noncommute :
    leftMulMatrixGeneral ex_X.1 * leftMulMatrixGeneral ex_Y.1 ≠
      leftMulMatrixGeneral ex_Y.1 * leftMulMatrixGeneral ex_X.1 := by
  intro h
  have hm := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => Matrix.toLin' M) h
  apply leftMul_operators_ex_noncommute
  simpa [leftMulMatrixGeneral, Matrix.toLin'_mul] using hm

/-- The same obstruction is visible as an inequality of concrete real 8×8
matrices: their operator commutator is not the lift of the Zorn commutator. -/
theorem leftMulMatrix_commutator_obstruction :
    leftMulMatrixGeneral ex_X.1 * leftMulMatrixGeneral ex_Y.1 -
      leftMulMatrixGeneral ex_Y.1 * leftMulMatrixGeneral ex_X.1 ≠
    leftMulMatrixGeneral (ex_X.1 * ex_Y.1) - leftMulMatrixGeneral (ex_Y.1 * ex_X.1) := by
  intro h
  have hm := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℝ => Matrix.toLin' M) h
  apply leftMul_commutator_defect_ex_ne_zero
  rw [← leftMul_commutator_defect]
  simpa [leftMulMatrixGeneral, Matrix.toLin'_mul] using sub_eq_zero.mpr hm

end InfoGeometry.OperatorAlgebra.SplitOctonionLeftMultiplicationBridge
