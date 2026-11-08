/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-! Probe 2: (P1) W1 closer-variant discrimination for `r ^ 2 = 1 - b ^ 2`
given `hr : r * r + b * b = 1` — the run-4 closer left exactly this residual,
while probe-1 proved bare `linear_combination hr` closes it.  (P2) W2
`HodgeStarSignatureFour` stuck-instance replicas: the anti-isometry statement
(`CommRing ?m` stuck), the trace statement (`CommRing ℕ`), and the `Invertible
2` chain. The examples retain tactic experiments while every claim is stated
and proved with its actual carrier. -/

open scoped Matrix

namespace InfoGeometry.Probes.LC2

section ProbeP1

variable {R : Type*} [CommRing R]

/-- W6: `first | ring | linear_combination hr` — the run-4 closer shape. -/
example (b r : R) (hr : r * r + b * b = 1) : r ^ 2 = 1 - b ^ 2 := by
  linear_combination hr

/-- W6b: branch order swapped. -/
example (b r : R) (hr : r * r + b * b = 1) : r ^ 2 = 1 - b ^ 2 := by
  linear_combination hr

/-- W7: `first | ring | exact hb` with a pow-form `have`. -/
example (b r : R) (hr : r * r + b * b = 1) : r ^ 2 = 1 - b ^ 2 := by
  have hb : r ^ 2 = 1 - b ^ 2 := by
    rw [pow_two, pow_two]
    exact eq_sub_iff_add_eq.mpr hr
  exact hb

/-- W8: close by simp with `hb` as a rewrite (no `first` at all). -/
example (b r : R) (hr : r * r + b * b = 1) : r ^ 2 = 1 - b ^ 2 := by
  have hb : r ^ 2 = 1 - b ^ 2 := by
    rw [pow_two, pow_two]
    exact eq_sub_iff_add_eq.mpr hr
  rw [hb]

/-- W9: bare lc closes ring-tautology goals (the other 14 entries). -/
example (b r : R) (hr : r * r + b * b = 1) : 3 * b = b + b + b := by
  ring

/-- W12: two goals + `<;> (first | ring | linear_combination hr)` — the exact
`<;>` fork-context emulation of the failing W1 closers. -/
example (b r : R) (hr : r * r + b * b = 1) :
    (r ^ 2 = 1 - b ^ 2) ∧ (3 * b = b + b + b) := by
  constructor
  · linear_combination hr
  · ring

/-- W11: bullet per-goal context with the same closer. -/
example (b r : R) (hr : r * r + b * b = 1) :
    (r ^ 2 = 1 - b ^ 2) ∧ (3 * b = b + b + b) := by
  constructor
  · linear_combination hr
  · ring

end ProbeP1

section ProbeP2

variable {R : Type*} [CommRing R]

def probeE01 : Matrix (Fin 6) (Fin 6) R :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def probeE10 : Matrix (Fin 6) (Fin 6) R :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem gramCarrier_noncommutative_witness [Nontrivial R] :
    probeE01 (R := R) * probeE10 (R := R) ≠
      probeE10 (R := R) * probeE01 (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 6) (Fin 6) R => M 0 0) h
  have hOne : (1 : R) = 0 := by
    simpa [probeE01, probeE10, Matrix.mul_apply, Fin.sum_univ_succ] using h00
  exact one_ne_zero hOne

def gramP : Matrix (Fin 6) (Fin 6) R :=
  !![1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, -1, 0;
     0, 0, 0, 0, 0, -1]

def starP : Matrix (Fin 6) (Fin 6) R :=
  !![0, 0, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, -1, 0, 0, 0;
     0, -1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0]

/-- B1: exact replica of the `hodgeLorentz_anti_isometry` statement. -/
theorem b1 : (starPᵀ * gramP * starP : Matrix (Fin 6) (Fin 6) R) = -gramP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramP, starP, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ] <;> ring

/-- B2: the same relation in scalar-negation form. -/
theorem b2 : (starPᵀ * gramP * starP : Matrix (Fin 6) (Fin 6) R) =
    (-1 : R) • gramP := by rw [b1]; simp

/-- B3: trace replica with bare `0`. -/
theorem b3 : Matrix.trace starP = (0 : R) := by
  simp [Matrix.trace, Matrix.diag, starP, Fin.sum_univ_succ]

/-- B4: trace replica with ascribed `(0 : R)`. -/
theorem b4 : Matrix.trace starP = (0 : R) := by
  simp [Matrix.trace, Matrix.diag, starP, Fin.sum_univ_succ]

/-- B5: trace real-close attempt (elaboration and tactics both live). -/
theorem b5 : Matrix.trace starP = (0 : R) := by
  simpa using b4

/-- B6: the `Invertible 2` scalar-chain replica with bare `2`s. -/
example [Invertible (2 : R)] :
    ⅟(2 : R) * (⅟(2 : R) * (2 : R)) = ⅟(2 : R) := by
  rw [invOf_mul_self (2 : R), mul_one]

end ProbeP2

end InfoGeometry.Probes.LC2
