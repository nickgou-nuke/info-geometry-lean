import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
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
def w_U (_x : ℝ) : ℝ := 1

/-- The unitary density is constantly `1`. -/
theorem w_U_eq_one (_x : ℝ) : w_U _x = 1 := by
  rfl

/-- The unitary density at the origin is `1`. -/
theorem w_U_zero : w_U 0 = 1 := by
  rfl

/-- The unitary density is nonnegative everywhere. -/
theorem w_U_nonneg (x : ℝ) : 0 ≤ w_U x := by
  simp [w_U]

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

/-- The symplectic and even-orthogonal densities sum to `2`. -/
theorem w_Sp_add_w_SO_even (x : ℝ) :
    w_Sp x + w_SO_even x = 2 := by
  by_cases hx : x = 0
  · simp [w_Sp, w_SO_even, hx]
  · simp [w_Sp, w_SO_even, hx]
    ring

/-- The even-orthogonal density is the complement of the symplectic one. -/
theorem w_SO_even_eq_two_sub_w_Sp (x : ℝ) :
    w_SO_even x = 2 - w_Sp x := by
  have h := w_Sp_add_w_SO_even x
  linarith

/-- The symplectic density is the complement of the even-orthogonal one. -/
theorem w_Sp_eq_two_sub_w_SO_even (x : ℝ) :
    w_Sp x = 2 - w_SO_even x := by
  have h := w_Sp_add_w_SO_even x
  linarith

end InfoGeometry.Analysis.KatzSarnak
