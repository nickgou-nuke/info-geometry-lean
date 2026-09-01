import Mathlib
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Zorn associator as an operator-composition defect

True split-octonion Zorn multiplication is nonassociative, so it is not placed
inside ordinary Mathlib matrix multiplication.

The canonical Zorn owner already provides the correct bridge: every Zorn cell
`X` acts by the left-regular linear endomorphism `L_X`, and

`L_X (L_Y Z) - L_{XY} Z = -[X,Y,Z]`.

Thus the nonassociative information survives exactly as the defect of the
associative operator composition law.  On triples with vanishing associator,
the left-regular action becomes multiplicative at that vector.
-/

namespace InfoGeometry.Physics.NuclearZornAssociatorOperatorBridge

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

abbrev Zorn := SplitOct
abbrev ZornEnd := Module.End ℤ SplitOct

/-- Left-regular Zorn multiplication as an associative linear-operator
carrier. -/
def leftOp (X : Zorn) : ZornEnd :=
  leftRegularLinear X

@[simp] theorem leftOp_apply (X Y : Zorn) :
    leftOp X Y = mulZ X Y := by
  rfl

/-- Exact composition defect: the discrepancy between composing left-regular
operators and left-multiplying by the Zorn product is the negative associator. -/
theorem leftOp_composition_defect_apply (X Y Z : Zorn) :
    ((leftOp X * leftOp Y - leftOp (mulZ X Y)) Z) =
      negZ (associator X Y Z) := by
  change subZ (leftRegular X (leftRegular Y Z))
      (leftRegular (mulZ X Y) Z) = negZ (associator X Y Z)
  exact leftRegular_mul_defect X Y Z

/-- If the associator vanishes on a triple, left-regular operator composition
agrees with multiplication by the Zorn product on that vector. -/
theorem leftOp_mul_apply_eq_of_associator_zero
    (X Y Z : Zorn) (hAssoc : associator X Y Z = 0) :
    (leftOp X * leftOp Y) Z = leftOp (mulZ X Y) Z := by
  have h := leftOp_composition_defect_apply X Y Z
  rw [hAssoc] at h
  change (leftOp X * leftOp Y) Z - leftOp (mulZ X Y) Z = 0 at h
  exact sub_eq_zero.mp h

/-- Conversely, exact multiplicativity of the left-regular action on a vector
forces the corresponding associator to vanish. -/
theorem associator_zero_of_leftOp_mul_apply_eq
    (X Y Z : Zorn)
    (hMul : (leftOp X * leftOp Y) Z = leftOp (mulZ X Y) Z) :
    associator X Y Z = 0 := by
  have h := leftOp_composition_defect_apply X Y Z
  have hzero :
      (leftOp X * leftOp Y - leftOp (mulZ X Y)) Z = 0 := by
    change (leftOp X * leftOp Y) Z - leftOp (mulZ X Y) Z = 0
    exact sub_eq_zero.mpr hMul
  rw [hzero] at h
  have hneg : negZ (associator X Y Z) = 0 := h.symm
  have hneg' : -(associator X Y Z) = 0 := by
    change negZ (associator X Y Z) = 0
    exact hneg
  exact neg_eq_zero.mp hneg'

/-- The nonassociative and operator formulations agree exactly on whether the
local composition defect vanishes. -/
theorem leftOp_multiplicative_at_iff_associator_zero
    (X Y Z : Zorn) :
    (leftOp X * leftOp Y) Z = leftOp (mulZ X Y) Z ↔
      associator X Y Z = 0 := by
  constructor
  · exact associator_zero_of_leftOp_mul_apply_eq X Y Z
  · exact leftOp_mul_apply_eq_of_associator_zero X Y Z

end InfoGeometry.Physics.NuclearZornAssociatorOperatorBridge
