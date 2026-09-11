import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.NuclearBathSubalgebra

variable {Operator : Type*}
variable [Ring Operator] [Algebra ℝ Operator]

/-!
# Associative bath commutants

This is the associative counterpart of the Lie-level bath predicate.  The
carrier is a native `Subalgebra`; no second operator algebra is introduced.
-/

/-- Associative observables commuting with every element of the bath. -/
def CommutesWithBath (bath : Set Operator) (X : Operator) : Prop :=
  ∀ ⦃B : Operator⦄, B ∈ bath → X * B = B * X

/-- The associative bath commutant as a Mathlib subalgebra. -/
def BathCommutant (bath : Set Operator) : Subalgebra ℝ Operator where
  carrier := {X | CommutesWithBath bath X}
  mul_mem' := by
    intro X Y hX hY B hB
    rw [mul_assoc, hY hB, ← mul_assoc, hX hB, mul_assoc]
  one_mem' := by
    intro B hB
    simp
  add_mem' := by
    intro X Y hX hY B hB
    rw [add_mul, mul_add, hX hB, hY hB]
  zero_mem' := by
    intro B hB
    simp
  algebraMap_mem' := by
    intro r B hB
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      mul_smul_comm, mul_one]

@[simp] theorem mem_bathCommutant_iff
    (bath : Set Operator) (X : Operator) :
    X ∈ BathCommutant bath ↔ CommutesWithBath bath X :=
  Iff.rfl

theorem bathCommutant_mul_mem
    (bath : Set Operator) {X Y : Operator}
    (hX : X ∈ BathCommutant bath)
    (hY : Y ∈ BathCommutant bath) :
    X * Y ∈ BathCommutant bath :=
  (BathCommutant bath).mul_mem hX hY

theorem bathCommutant_add_mem
    (bath : Set Operator) {X Y : Operator}
    (hX : X ∈ BathCommutant bath)
    (hY : Y ∈ BathCommutant bath) :
    X + Y ∈ BathCommutant bath :=
  (BathCommutant bath).add_mem hX hY

/-- The associative commutator of two bath-commuting observables is again
bath-commuting. -/
theorem bathCommutant_commutator_mem
    (bath : Set Operator) {X Y : Operator}
    (hX : X ∈ BathCommutant bath)
    (hY : Y ∈ BathCommutant bath) :
    X * Y - Y * X ∈ BathCommutant bath := by
  intro B hB
  have hXY : (X * Y) * B = B * (X * Y) :=
    (BathCommutant bath).mul_mem hX hY hB
  have hYX : (Y * X) * B = B * (Y * X) :=
    (BathCommutant bath).mul_mem hY hX hB
  rw [sub_mul, mul_sub, hXY, hYX]

end InfoGeometry.Canonical.NuclearBathSubalgebra
