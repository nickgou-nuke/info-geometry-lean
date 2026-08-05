import Mathlib.Tactic

/-!
# Cole-Fury 32-dimensional ideal quadrant laws

This module is the Lean twin of `tools/sympy/cole_fury_ideals.py`.
It formalizes exact `32 × 32` integer block matrices for the `16+16` spinor
quadrant decomposition used by the finite Pin(5,5) glide/projective-center lane.

#### BUCKET 1: CLOSED FINITE THEOREMS
The concrete matrices below prove:

* upper-left and lower-right diagonal quadrant projectors are idempotent;
* the upper-right horizon `horizonUp` and lower-left horizon `horizonDown` are nilpotent;
* `horizonUp * horizonDown = upperLeft` and `horizonDown * horizonUp = lowerRight`;
* the commutator `[horizonDown, horizonUp]` closes to `diag(-I₁₆,+I₁₆)`;
* the diagonal grading core squares to identity and acts on the horizons by
  weights `-2` and `+2`.

#### BUCKET 3: OPEN CLOSURE DEBT
This is a finite quadrant-block law surface.  It does not prove a physical
Cole-Fury/electron-positron classification theorem or a Cuntz quasilattice
boundary theorem.
-/

namespace InfoGeometry.OperatorAlgebra.ColeFury

open Matrix

abbrev Spin32Matrix := Matrix (Fin 32) (Fin 32) ℤ

/-- Upper-left `16 × 16` diagonal block. -/
def upperLeft : Spin32Matrix :=
  fun i j => if i.val < 16 ∧ j = i then 1 else 0

/-- Lower-right `16 × 16` diagonal block. -/
def lowerRight : Spin32Matrix :=
  fun i j => if 16 ≤ i.val ∧ j = i then 1 else 0

/-- Upper-right nilpotent horizon block. -/
def horizonUp : Spin32Matrix :=
  fun i j => if i.val < 16 ∧ j.val = i.val + 16 then 1 else 0

/-- Lower-left conjugate nilpotent horizon block. -/
def horizonDown : Spin32Matrix :=
  fun i j => if 16 ≤ i.val ∧ j.val + 16 = i.val then 1 else 0

/-- Diagonal grading core obtained as `[g₋₁,g₊₁] = horizonDown*horizonUp - horizonUp*horizonDown`. -/
def g0Core : Spin32Matrix := horizonDown * horizonUp - horizonUp * horizonDown

/-- Explicit diagonal `diag(-I₁₆,+I₁₆)` target for the commutator closure. -/
def expectedG0Core : Spin32Matrix := -upperLeft + lowerRight

/-- Upper-left quadrant is an idempotent projector. -/
theorem upperLeft_idempotent : upperLeft * upperLeft = upperLeft := by
  unfold upperLeft
  native_decide

/-- Lower-right quadrant is an idempotent projector. -/
theorem lowerRight_idempotent : lowerRight * lowerRight = lowerRight := by
  unfold lowerRight
  native_decide

/-- Diagonal quadrants are orthogonal in this block decomposition. -/
theorem upperLeft_lowerRight_zero : upperLeft * lowerRight = 0 := by
  unfold upperLeft lowerRight
  native_decide

/-- Diagonal quadrants are orthogonal in the reverse order. -/
theorem lowerRight_upperLeft_zero : lowerRight * upperLeft = 0 := by
  unfold upperLeft lowerRight
  native_decide

/-- The two diagonal quadrants partition the full spinor identity. -/
theorem diagonal_quadrants_sum : upperLeft + lowerRight = 1 := by
  unfold upperLeft lowerRight
  native_decide

/-- The upper-right horizon block is nilpotent. -/
theorem horizonUp_nilpotent : horizonUp * horizonUp = 0 := by
  unfold horizonUp
  native_decide

/-- The lower-left horizon block is nilpotent. -/
theorem horizonDown_nilpotent : horizonDown * horizonDown = 0 := by
  unfold horizonDown
  native_decide

/-- Upper-right followed by lower-left closes to the upper-left diagonal block. -/
theorem horizonUp_horizonDown : horizonUp * horizonDown = upperLeft := by
  unfold horizonUp horizonDown upperLeft
  native_decide

/-- Lower-left followed by upper-right closes to the lower-right diagonal block. -/
theorem horizonDown_horizonUp : horizonDown * horizonUp = lowerRight := by
  unfold horizonUp horizonDown lowerRight
  native_decide

/-- Anticommutator of the two horizon blocks is the full identity. -/
theorem horizon_anticomm_identity : horizonUp * horizonDown + horizonDown * horizonUp = 1 := by
  rw [horizonUp_horizonDown, horizonDown_horizonUp, diagonal_quadrants_sum]

/-- The horizon commutator closes into the diagonal grading core. -/
theorem horizon_commutator_expected :
    horizonDown * horizonUp - horizonUp * horizonDown = expectedG0Core :=
  by
    unfold horizonUp horizonDown expectedG0Core upperLeft lowerRight
    native_decide

/-- The named grading core equals the explicit diagonal target. -/
theorem g0Core_eq_expected : g0Core = expectedG0Core := by
  unfold g0Core
  exact horizon_commutator_expected

/-- The diagonal grading core is an involution. -/
theorem g0Core_sq : g0Core * g0Core = 1 := by
  unfold g0Core horizonUp horizonDown
  native_decide

/-- The diagonal grading core acts on the upper-right horizon with weight `-2`. -/
theorem g0Core_horizonUp_weight : g0Core * horizonUp - horizonUp * g0Core = (-2 : ℤ) • horizonUp := by
  unfold g0Core horizonUp horizonDown
  native_decide

/-- The diagonal grading core acts on the lower-left horizon with weight `+2`. -/
theorem g0Core_horizonDown_weight : g0Core * horizonDown - horizonDown * g0Core = (2 : ℤ) • horizonDown := by
  unfold g0Core horizonUp horizonDown
  native_decide

end InfoGeometry.OperatorAlgebra.ColeFury
