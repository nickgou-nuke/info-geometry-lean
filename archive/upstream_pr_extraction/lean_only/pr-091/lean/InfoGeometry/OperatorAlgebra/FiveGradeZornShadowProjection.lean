import Mathlib
import InfoGeometry.Algebra.ChiralOperatorSymbolProjection
import InfoGeometry.Algebra.ChiralSymbolProjectionMirror
import InfoGeometry.Algebra.ZornMatrix

/-!
# Five-grade operator words and their Zorn shadow

The operator envelope remains associative.  A Zorn carrier is used only as a
symbol/readout target, through an explicit inclusion and readout pair.  The
projected product is therefore allowed to be nonassociative, and its
associator is the readout of the discarded operator defect.
-/

namespace InfoGeometry.OperatorAlgebra.FiveGradeZornShadowProjection

open InfoGeometry.Algebra

variable {R Z E : Type*}
  [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

/-- Native Zorn vector-matrix carrier, exposed as a possible shadow target. -/
abbrev ZornShadowCarrier (R : Type*) [CommRing R] :=
  ZornMatrix R

def visibleProjection (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) : E →ₗ[R] E :=
  symbolProjection inclusion readout

def operatorDefect (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (X : E) : E :=
  symbolDefect inclusion readout X

def shadowMul (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y : Z) : Z :=
  projectedOperatorMul inclusion readout x y

theorem shadowMul_add_left
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) :
    shadowMul inclusion readout (x + y) z =
      shadowMul inclusion readout x z + shadowMul inclusion readout y z := by
  simp [shadowMul, projectedOperatorMul, map_add, add_mul]

theorem shadowMul_add_right
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) :
    shadowMul inclusion readout x (y + z) =
      shadowMul inclusion readout x y + shadowMul inclusion readout x z := by
  simp [shadowMul, projectedOperatorMul, map_add, mul_add]

theorem shadowMul_neg_left
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y : Z) :
    shadowMul inclusion readout (-x) y =
      -shadowMul inclusion readout x y := by
  simp [shadowMul, projectedOperatorMul, map_neg, neg_mul]

theorem shadowMul_neg_right
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y : Z) :
    shadowMul inclusion readout x (-y) =
      -shadowMul inclusion readout x y := by
  simp [shadowMul, projectedOperatorMul, map_neg, mul_neg]

def shadowAssociator (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  shadowMul inclusion readout (shadowMul inclusion readout x y) z -
    shadowMul inclusion readout x (shadowMul inclusion readout y z)

def shadowCommutator (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y : Z) : Z :=
  shadowMul inclusion readout x y - shadowMul inclusion readout y x

def shadowJacobiator (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  shadowCommutator inclusion readout (shadowCommutator inclusion readout x y) z +
    shadowCommutator inclusion readout (shadowCommutator inclusion readout y z) x +
      shadowCommutator inclusion readout (shadowCommutator inclusion readout z x) y

def shadowRightNestedJacobiator
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  shadowCommutator inclusion readout x (shadowCommutator inclusion readout y z) +
    shadowCommutator inclusion readout y (shadowCommutator inclusion readout z x) +
      shadowCommutator inclusion readout z (shadowCommutator inclusion readout x y)

theorem shadow_akivis_identity
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y z : Z) :
    shadowJacobiator inclusion readout x y z =
      (shadowAssociator inclusion readout x y z +
          shadowAssociator inclusion readout y z x +
          shadowAssociator inclusion readout z x y) -
        (shadowAssociator inclusion readout y x z +
          shadowAssociator inclusion readout z y x +
          shadowAssociator inclusion readout x z y) := by
  unfold shadowJacobiator shadowCommutator shadowAssociator
  simp only [sub_eq_add_neg, shadowMul_add_left, shadowMul_add_right,
    shadowMul_neg_left, shadowMul_neg_right]
  abel_nf

theorem shadowRightNestedJacobiator_eq_neg
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y z : Z) :
    shadowRightNestedJacobiator inclusion readout x y z =
      -shadowJacobiator inclusion readout x y z := by
  unfold shadowRightNestedJacobiator shadowJacobiator shadowCommutator
  simp only [sub_eq_add_neg, shadowMul_add_left, shadowMul_add_right,
    shadowMul_neg_left, shadowMul_neg_right]
  abel_nf

theorem visibleProjection_add_operatorDefect
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (X : E) :
    visibleProjection inclusion readout X + operatorDefect inclusion readout X = X := by
  exact symbolProjection_add_defect inclusion readout X

theorem shadowAssociator_eq_readout_of_defect
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y z : Z) :
    shadowAssociator inclusion readout x y z =
      readout (
        inclusion x * operatorDefect inclusion readout (inclusion y * inclusion z) -
          operatorDefect inclusion readout (inclusion x * inclusion y) * inclusion z) := by
  exact projectedOperatorAssociator_eq_defect
    inclusion readout x y z

theorem shadowAssociator_eq_zero_of_defect_expression_eq_zero
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y z : Z)
    (hdef : inclusion x * operatorDefect inclusion readout (inclusion y * inclusion z) -
        operatorDefect inclusion readout (inclusion x * inclusion y) * inclusion z = 0) :
    shadowAssociator inclusion readout x y z = 0 := by
  rw [shadowAssociator_eq_readout_of_defect inclusion readout x y z, hdef]
  exact map_zero readout

theorem defect_expression_eq_zero_of_shadowAssociator_eq_zero
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (hinj : Function.Injective readout) (x y z : Z)
    (hzero : shadowAssociator inclusion readout x y z = 0) :
    inclusion x * operatorDefect inclusion readout (inclusion y * inclusion z) -
        operatorDefect inclusion readout (inclusion x * inclusion y) * inclusion z = 0 := by
  apply hinj
  calc
    readout (inclusion x * operatorDefect inclusion readout (inclusion y * inclusion z) -
        operatorDefect inclusion readout (inclusion x * inclusion y) * inclusion z) =
      shadowAssociator inclusion readout x y z :=
        (shadowAssociator_eq_readout_of_defect inclusion readout x y z).symm
    _ = 0 := hzero
    _ = readout 0 := (map_zero readout).symm

theorem shadowMul_agrees_with_operator_readout
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z) (x y : Z) :
    shadowMul inclusion readout x y = readout (inclusion x * inclusion y) :=
  rfl

/-! ## The real integer-to-cyclotomic fold -/

def gradeResidue (k : ℤ) : ZMod 3 := k

theorem grade_two_folds_to_neg_one :
    gradeResidue 2 = gradeResidue (-1) := by
  decide

theorem grade_neg_two_folds_to_one :
    gradeResidue (-2) = gradeResidue 1 := by
  decide

theorem grade_residue_add (r s : ℤ) :
    gradeResidue (r + s) = gradeResidue r + gradeResidue s := by
  exact Int.cast_add r s

/-! ## Equivariant mirror transport -/

theorem mirror_preserves_shadowMul
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (M : SymbolProjectionMirrorData inclusion readout) (x y : Z) :
    M.mirrorSymbol (shadowMul inclusion readout x y) =
      shadowMul inclusion readout (M.mirrorSymbol x) (M.mirrorSymbol y) := by
  exact mirror_projectedOperatorMul M x y

theorem mirror_preserves_visibleProjection
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (M : SymbolProjectionMirrorData inclusion readout) (X : E) :
    M.mirrorOperator (visibleProjection inclusion readout X) =
      visibleProjection inclusion readout (M.mirrorOperator X) := by
  exact mirror_symbolProjection M X

theorem mirror_preserves_operatorDefect
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (M : SymbolProjectionMirrorData inclusion readout) (X : E) :
    M.mirrorOperator (operatorDefect inclusion readout X) =
      operatorDefect inclusion readout (M.mirrorOperator X) := by
  exact mirror_symbolDefect M X

end InfoGeometry.OperatorAlgebra.FiveGradeZornShadowProjection
