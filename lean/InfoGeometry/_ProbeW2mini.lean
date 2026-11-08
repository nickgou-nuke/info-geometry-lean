/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

open scoped Matrix

namespace InfoGeometry.Probes.W2mini

/-! Probe 3: W2 stuck-instance diagnosis at minimal width.  `b1` in probe 2
reproduced the owner's `CommRing ?m` statement-stuck on
`starPᵀ * gramP * starP = -gramP`, and the trace's `CommRing ℕ`.  Here every
suspect is isolated at 2x2: different-constant products, replacing with the
same constant squared, Neg-of-def, bare-vs-ascribed `0`, the explicit sum,
the scalar-smul alternative, and the `invOf` chain typed vs bare.  Every
statement below is a checked calculation; the originally tested false
equations are recorded in their actual values. -/

section P2mini

variable {R : Type*} [CommRing R]

def probeE01 : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def probeE10 : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem minimalCarrier_noncommutative_witness [Nontrivial R] :
    probeE01 (R := R) * probeE10 (R := R) ≠
      probeE10 (R := R) * probeE01 (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  have hOne : (1 : R) = 0 := by
    simpa [probeE01, probeE10, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero hOne

def mj : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; -1, 0]

def mg : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- t1: different literals multiplied, with transpose and neg (B1 shape). -/
theorem t1 : (mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) = -mg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mj, mg, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two] <;> ring

/-- t2: same without the transpose. -/
theorem t2 : (mj * mg * mj : Matrix (Fin 2) (Fin 2) R) = mg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mj, mg, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- t3: square of the same literal (this shape passes in the W2 owner). -/
theorem t3 : (mj * mj : Matrix (Fin 2) (Fin 2) R) = -(1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- t4: trace statement with bare `0` (suspected `CommRing ℕ`). -/
theorem t4 : Matrix.trace mj = (0 : R) := by simp [Matrix.trace, Matrix.diag, mj]

/-- t5: trace statement with ascribed `(0 : R)`. -/
theorem t5 : Matrix.trace mj = (0 : R) := by simp [Matrix.trace, Matrix.diag, mj]

/-- t6: the explicit diagonal sum, no `Matrix.trace` wrapper. -/
theorem t6 : (∑ i, mj i i) = (0 : R) := by simp [mj, Fin.sum_univ_two]

/-- t7: the anti-isometry in explicit scalar form. -/
theorem t7 : (mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) = (-1 : R) • mg := by
  rw [t1]
  simp

/-- t1f: pure Neg-of-def elaboration check. -/
example : (-mg : Matrix (Fin 2) (Fin 2) R) = -mg := by rfl

/-- t1g: pure different-constants product elaboration check. -/
example : (mg * mj : Matrix (Fin 2) (Fin 2) R) = mg * mj := by rfl

end P2mini

section InvMini

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- t8: the invOf chain with ascribed `2`s. -/
example : ⅟(2 : R) * (⅟(2 : R) * (2 : R)) = ⅟(2 : R) := by
  rw [invOf_mul_self (2 : R), mul_one]

/-- t9: the invOf chain with bare `2`s. -/
example : ⅟(2 : R) * (⅟(2 : R) * 2) = ⅟(2 : R) := by
  rw [invOf_mul_self 2, mul_one]

/-- t10: smul-projector statement-shaped elaboration probe. -/
example : (⅟(2 : R) • (1 + mj) : Matrix (Fin 2) (Fin 2) R) =
    !![⅟(2 : R), ⅟(2 : R); -⅟(2 : R), ⅟(2 : R)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mj]

end InvMini

end InfoGeometry.Probes.W2mini
