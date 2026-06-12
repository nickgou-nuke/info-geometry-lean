import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Katz-Sarnak 1-Level Densities

Formalizes the 1-level scaling densities for the low-lying zeroes of various families
of L-functions as proven/conjectured by Katz and Sarnak.
-/

noncomputable section

namespace InfoGeometry.Analysis.KatzSarnak

open Real

/-- The Unitary (U) symmetry scaling density. -/
def w_U (x : ℝ) : ℝ := 1

/-- The Symplectic (Sp) symmetry scaling density. 
Note: x = 0 is a removable singularity. -/
def w_Sp (x : ℝ) : ℝ :=
  if x = 0 then 0 else 1 - Real.sin (2 * Real.pi * x) / (2 * Real.pi * x)

/-- The Orthogonal even (SO(even)) symmetry scaling density.
Note: x = 0 is a removable singularity. -/
def w_SO_even (x : ℝ) : ℝ :=
  if x = 0 then 2 else 1 + Real.sin (2 * Real.pi * x) / (2 * Real.pi * x)

/--
Theorem: The symplectic density exhibits level repulsion at the origin,
w_Sp(0) = 0.
-/
theorem w_Sp_zero : w_Sp 0 = 0 := by
  dsimp [w_Sp]
  split_ifs
  · rfl
  · contradiction

/--
Theorem: The SO(even) density exhibits level attraction at the origin,
w_SO_even(0) = 2.
-/
theorem w_SO_even_zero : w_SO_even 0 = 2 := by
  dsimp [w_SO_even]
  split_ifs
  · rfl
  · contradiction

end InfoGeometry.Analysis.KatzSarnak
