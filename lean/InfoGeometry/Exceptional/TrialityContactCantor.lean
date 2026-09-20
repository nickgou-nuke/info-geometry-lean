import Mathlib.Algebra.Lie.Subalgebra
import InfoGeometry.Algebra.CyclicOrderThree

/-!
# Order-three linear actions: fixed points and coboundaries

The dependencies are an order-three action, its orbit sum, the normalized
Reynolds projection, and the kernel/range criterion for cancellation.
This is a general action theorem, not an identification of a fixed algebra
with G₂. A cyclic orbit sum need not vanish; coboundaries do have zero sum.
-/

noncomputable section

namespace InfoGeometry.Exceptional.TrialityContactCantor

open InfoGeometry.Algebra.CyclicOrderThree

section LieAction

variable {Scalar LieCarrier : Type*} [CommRing Scalar]
variable [LieRing LieCarrier] [LieAlgebra Scalar LieCarrier]

def fixedLieSubalgebra (rotation : LieCarrier ≃ₗ⁅Scalar⁆ LieCarrier) :
    LieSubalgebra Scalar LieCarrier where
  carrier := {operator | rotation operator = operator}
  zero_mem' := map_zero rotation
  add_mem' := by
    intro first second hfirst hsecond
    change rotation first = first at hfirst
    change rotation second = second at hsecond
    change rotation (first + second) = first + second
    rw [map_add, hfirst, hsecond]
  smul_mem' := by
    intro scalar operator hoperator
    change rotation operator = operator at hoperator
    change rotation (scalar • operator) = scalar • operator
    rw [map_smul, hoperator]
  lie_mem' := by
    intro first second hfirst hsecond
    change rotation ⁅first, second⁆ = ⁅first, second⁆
    rw [rotation.map_lie, hfirst, hsecond]

end LieAction

section Projection

variable {Scalar LieCarrier : Type*} [Field Scalar] [CharZero Scalar]
variable [LieRing LieCarrier] [LieAlgebra Scalar LieCarrier]
variable (rotation : LieCarrier ≃ₗ⁅Scalar⁆ LieCarrier)

omit [CharZero Scalar] in
theorem fixedLieSubalgebra_eq_ker_boundary :
    (fixedLieSubalgebra rotation).toSubmodule =
      LinearMap.ker (boundary rotation.toLinearEquiv.toLinearMap) := by
  ext operator
  change rotation operator = operator ↔ operator - rotation operator = 0
  rw [sub_eq_zero, eq_comm]

theorem range_reynolds_eq_fixedLieSubalgebra
    (hcycle : ∀ operator, rotation (rotation (rotation operator)) = operator) :
    LinearMap.range (reynolds rotation.toLinearEquiv.toLinearMap) =
      (fixedLieSubalgebra rotation).toSubmodule := by
  rw [fixedLieSubalgebra_eq_ker_boundary]
  exact range_reynolds _ hcycle

end Projection

end InfoGeometry.Exceptional.TrialityContactCantor
