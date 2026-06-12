import Mathlib
import InfoGeometry.Topology.AharonovBohmVortices
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Braid parafermion finite closure

This module ties the finite braid/vortex surface together without promoting the
interpretive physics to kernel claims.

It proves three closed algebraic facts:

* a `2 x 2` block embeds multiplicatively into a `3 x 3` projective carrier;
* the explicit `3 x 3` braid generators satisfy the Artin relation;
* an exact `ZMod 3` additive winding phase closes after three windings.

#### BUCKET 1: CLOSED FINITE THEOREMS

`blockEmbed2x2_mul`, `z3Unit_three_windings`, `z3Unit_nonzero`, and
`finite_braid_parafermion_closure`.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

`finite_braid_vortex_closure`.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here proves Lorentz covariance, `SU(2)`/`SU(3)` representation
theory, physical parafermion statistics, color confinement, or an LLM thermal
model.  Those require additional explicit representations and analytic
premises.
-/

noncomputable section

namespace InfoGeometry.Topology.BraidParafermionClosure

open Matrix
open InfoGeometry.Topology.Parafermion

/-- `2 x 2` complex matrices. -/
abbrev Mat2C := Matrix (Fin 2) (Fin 2) ℂ

/-- `3 x 3` complex matrices. -/
abbrev Mat3C := Matrix (Fin 3) (Fin 3) ℂ

/--
Embed a `2 x 2` block into the upper-left corner of a `3 x 3` projective
carrier, with the third coordinate fixed.
-/
def blockEmbed2x2 (A : Mat2C) : Mat3C :=
  ![![A 0 0, A 0 1, 0],
    ![A 1 0, A 1 1, 0],
    ![0,     0,     1]]

/-- The `2 x 2 -> 3 x 3` block embedding preserves multiplication. -/
theorem blockEmbed2x2_mul (A B : Mat2C) :
    blockEmbed2x2 (A * B) = blockEmbed2x2 A * blockEmbed2x2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockEmbed2x2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

/-- The exact additive `Z/3Z` unit phase. -/
def z3Unit : ZMod 3 := 1

/-- Three unit windings close in `Z/3Z`. -/
theorem z3Unit_three_windings :
    z3Unit + z3Unit + z3Unit = 0 := by
  native_decide

/-- The unit winding is nonzero in `Z/3Z`. -/
theorem z3Unit_nonzero :
    z3Unit ≠ 0 := by
  native_decide

/--
Closed finite braid/phase packet.

This combines the explicit Artin matrix relation with exact `Z/3Z` phase
closure.  It does not assert a physical realization.
-/
theorem finite_braid_parafermion_closure (t : ℂ) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t ∧
      z3Unit + z3Unit + z3Unit = 0 ∧
        z3Unit ≠ 0 := by
  exact ⟨su3_parafermion_braiding t, z3Unit_three_windings, z3Unit_nonzero⟩

/--
Conditional closure packet with a supplied complex third-root vortex witness.
-/
theorem finite_braid_vortex_closure (t : ℂ) (v : AharonovBohmVortex) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t ∧
      vortexOperator v * vortexOperator v * vortexOperator v = 1 := by
  exact ⟨su3_parafermion_braiding t, vortexOperator_cube_eq_one v⟩

end InfoGeometry.Topology.BraidParafermionClosure

end noncomputable section
