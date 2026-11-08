import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect

/-!
# The unit level set of the Peirce defect

Dependency: the universal defect product and `Phi² = V` give an explicit
unit; the quadratic relation gives the power recurrence. All products remain
in the ambient associative ring. No field extension is asserted.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B)

/-- On the unit defect level set, the two defect values are inverse units. -/
def defectLevelUnit (hV : idempotencyDefect (genV P A C) = 1) : Bˣ where
  val := idempotencyDefect (-genPhi P A C)
  inv := idempotencyDefect (genPhi P A C)
  val_inv := (genPhi_defect_product hP A C).1.trans hV
  inv_val := (genPhi_defect_product hP A C).2.trans hV

@[simp] theorem defectLevelUnit_val (hV : idempotencyDefect (genV P A C) = 1) :
    (defectLevelUnit hP A C hV : B) = genV P A C + genPhi P A C :=
  (genPhi_defect_pair hP A C).2

@[simp] theorem defectLevelUnit_inv (hV : idempotencyDefect (genV P A C) = 1) :
    ((defectLevelUnit hP A C hV)⁻¹ : Bˣ).val = genV P A C - genPhi P A C :=
  (genPhi_defect_pair hP A C).1

/-- This recurrence requires only the level-set equation, not idempotence of P. -/
theorem defect_level_power_recurrence
    (hV : idempotencyDefect (genV P A C) = 1) (n : ℕ) :
    genV P A C ^ (n + 2) = genV P A C ^ (n + 1) + genV P A C ^ n := by
  have h : genV P A C * genV P A C = genV P A C + 1 := by
    have hh := sub_eq_iff_eq_add.mp hV
    exact hh.trans (add_comm _ _)
  simpa using quadratic_power_recurrence (genV P A C) 1 h n

/-- The second defect iterate is zero on the unit level set. -/
theorem defect_level_second_iterate
    (hV : idempotencyDefect (genV P A C) = 1) :
    idempotencyDefect (idempotencyDefect (genV P A C)) = 0 := by
  rw [hV]
  simp [idempotencyDefect]

end InfoGeometry.OperatorAlgebra.PeirceSpine
