/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PeircePolynomialColimit
import InfoGeometry.Examples.RealMatrixModeWitness

/-!
# Dense operator obstructions to unrestricted nilpotent Taylor truncation

The existing stage-two matrices have no zero entries. Their exact products
give a nonzero cubic remainder, and faithfulness retains that obstruction
in the actual tensor direct limit. The second obstruction concerns the
formal scalar derivative at a Peirce idempotent. These are counterexamples
to overstrong formulas, not replacements for the generic operator results.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Examples.PeircePolynomialWitness

open InfoGeometry.Examples.RealMatrixModeWitness
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.PolynomialCalculus

/-- The existing dense square-zero matrix has a nonzero cubic remainder
at its adjoint base: the separated word is exactly the original matrix. -/
theorem dense_cubic_remainder_ne_zero :
    (star x + x) ^ 3 - (star x) ^ 3 -
      ((star x) ^ 2 * x + star x * x * star x + x * (star x) ^ 2) ≠ 0 := by
  rw [cube_add_sqZero_remainder (star x) x x_square_zero,
    x_mul_star_x, p_mul_x]
  intro hx
  exact x_entry_ne_zero default default
    (congrArg (fun M : Stage 2 => M default default) hx)

/-- The obstruction remains nonzero after faithful passage to the actual
algebraic direct limit. -/
theorem limit_dense_cubic_remainder_ne_zero :
    (star (ofStage 2 x) + ofStage 2 x) ^ 3 - (star (ofStage 2 x)) ^ 3 -
      ((star (ofStage 2 x)) ^ 2 * ofStage 2 x +
        star (ofStage 2 x) * ofStage 2 x * star (ofStage 2 x) +
        ofStage 2 x * (star (ofStage 2 x)) ^ 2) ≠ 0 := by
  rw [cube_add_sqZero_remainder _ _ limit_x_square_zero, ← ofStage_star,
    ← map_mul, x_mul_star_x, ← map_mul, p_mul_x]
  intro hx
  have hx0 : x = 0 :=
    (InfoGeometry.Clifford.Cl11StarAlgebraColimit.ofStage_eq_zero_iff 2 x).mp hx
  exact x_entry_ne_zero default default
    (congrArg (fun M : Stage 2 => M default default) hx0)

/-- At the dense idempotent base the square-polynomial increment is the
corner itself, whereas multiplying by the scalar formal derivative doubles it. -/
theorem dense_square_formal_derivative_failure :
    (p + x) ^ 2 ≠ p ^ 2 + (2 * p) * x := by
  have hcorner : conePlus p x = x := component10_x
  have hnonzero : conePlus p x ≠ 0 := by
    rw [hcorner]
    intro hx
    exact x_entry_ne_zero default default
      (congrArg (fun M : Stage 2 => M default default) hx)
  simpa only [hcorner] using
    square_add_conePlus_ne_formal_derivative p_isIdempotentElem.eq x hnonzero

end InfoGeometry.Examples.PeircePolynomialWitness

end
