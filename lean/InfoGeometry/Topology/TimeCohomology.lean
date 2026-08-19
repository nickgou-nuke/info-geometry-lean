import Mathlib.Tactic

open scoped ComplexConjugate

namespace InfoGeometry.Motives

/-!
# TimeCohomology

This file keeps only a very small theorem-honest core:

- a concrete 2×2 causal matrix model,
- a null-cone predicate via determinant zero,
- a finite algebraic record carrying a winding-number readout,
- the exact equality between that readout and its stored integer label.

It does not prove that physical time is de Rham cohomology, nor that the
Klein-quadric complement has already been computed globally.

## Core Definitions
1. `KleinQuadric`: the determinant-zero causal cone.
2. `MonodromyWinding`: a package containing a chosen winding-number readout.
3. `time_readout`: the associated integer label.
-/

variable {R : Type*} [CommRing R]

/-- 
The simple 2×2 causal matrix model.
-/
def CausalMatrix (t x y z : R) : Matrix (Fin 2) (Fin 2) R :=
  ![![t + z, x - y],
    ![x + y, t - z]]

/-- 
The determinant readout for the simple causal matrix model.
-/
def CausalDeterminant (t x y z : R) : R :=
  (CausalMatrix t x y z).det

/-- The causal determinant is the split quadratic form
`t² - x² - z² + y²`. -/
theorem causalDeterminant_formula (t x y z : R) :
    CausalDeterminant t x y z = t ^ 2 - x ^ 2 - z ^ 2 + y ^ 2 := by
  simp [CausalDeterminant, CausalMatrix, Matrix.det_fin_two]
  ring

/-- 
The determinant-zero locus in the simple causal matrix model.
-/
def KleinQuadric (t x y z : R) : Prop :=
  CausalDeterminant t x y z = 0

/-- The finite Klein-quadric predicate is exactly the split quadratic equation. -/
theorem kleinQuadric_iff (t x y z : R) :
    KleinQuadric t x y z ↔ t ^ 2 - x ^ 2 - z ^ 2 + y ^ 2 = 0 := by
  unfold KleinQuadric
  rw [causalDeterminant_formula]

/-- Positivity of the causal determinant is positivity of the split quadratic
form in the finite matrix model. -/
theorem causalDeterminant_pos_iff
    {t x y z : ℝ} :
    0 < CausalDeterminant t x y z ↔
      0 < t ^ 2 - x ^ 2 - z ^ 2 + y ^ 2 := by
  rw [causalDeterminant_formula]

/-- 
A logarithmic barrier potential on the open determinant-positive region.

This is only a definition here; no derivative or cohomology theorem is proved in
this file.
-/
noncomputable def LogBarrierPotential (X : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  - Real.log (X.det)

/-- 
Finite algebraic carrier for a winding-number readout.

No analytic de Rham form, holonomy theorem, or modular-flow identification is
constructed in this file.
-/
class MonodromyWinding where
  /-- The base manifold (Minkowski space) excluding the Klein quadric singularity. -/
  base_space : Type*
  /-- The chosen winding-number readout. -/
  winding_number : ℤ

/-- 
The integer time readout associated with a chosen winding-number packet.
-/
def time_readout (M : MonodromyWinding) : ℤ :=
  M.winding_number

/-- The time readout is exactly the winding number stored by the carrier. -/
theorem time_is_cohomology_of_winding (M : MonodromyWinding) :
  time_readout M = M.winding_number := by
  rfl

end InfoGeometry.Motives
