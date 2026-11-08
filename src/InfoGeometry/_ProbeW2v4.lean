/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

open scoped Matrix

namespace InfoGeometry.Probes.W2v4

/-! Probe 4: the 3-factor statement fix lab.  Probe 3 pinned: 2-factor
equations elaborate fine; any 3-factor binop chain on an un-ascribed
equation side elaborates stuck (`CommRing ?m`).  This probe finds the
lightest statement shape that supports the `Sᵀ G S` isometry conclusion,
plus a full rehearsal of the ascribed trace-close route.  Each matrix
calculation below is proved over an arbitrary commutative ring. -/

section P4

variable {R : Type*} [CommRing R]

def probeE01 : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

def probeE10 : Matrix (Fin 2) (Fin 2) R :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem fourCarrier_noncommutative_witness [Nontrivial R] :
    probeE01 (R := R) * probeE10 (R := R) ≠
      probeE10 (R := R) * probeE01 (R := R) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  have hOne : (1 : R) = 0 := by
    simpa [probeE01, probeE10, Matrix.mul_apply, Fin.sum_univ_two] using h00
  exact one_ne_zero hOne

def mj : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

def mg : Matrix (Fin 2) (Fin 2) R := !![1, 0; 0, -1]

/-- The common anti-isometry calculation, with the matrix carrier explicit. -/
theorem antiIsometry : (mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) = -mg := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mj, mg, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_two] <;> ring

/-- v1: full outer ascription of the 3-factor chain. -/
example : (mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) = -mg := antiIsometry

/-- v2: right-association, no ascription. -/
example : (mjᵀ * (mg * mj) : Matrix (Fin 2) (Fin 2) R) = -mg := by
  simpa [mul_assoc] using antiIsometry (R := R)

/-- v3: per-entry statement with the 3-factor chain inside. -/
example : ∀ (i j : Fin 2),
    ((mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) i j) = (-mg) i j := by
  intro i j
  rw [antiIsometry]

/-- v4: inner 2-factor ascribed, outer 2-factor bare. -/
example : ((mjᵀ * mg : Matrix (Fin 2) (Fin 2) R) * mj) = -mg := antiIsometry

/-- v5: direct multiplication-notation form. -/
example : (mjᵀ * mg * mj : Matrix (Fin 2) (Fin 2) R) = -mg := antiIsometry

/-- v6: right-associated multiplication-notation form. -/
example : (mjᵀ * (mg * mj) : Matrix (Fin 2) (Fin 2) R) = -mg := by
  simpa [mul_assoc] using antiIsometry (R := R)

/-- trace rehearsal: the real close route at 2x2 (no sorry). -/
theorem sum_fin2 {M : Type*} [AddCommMonoid M] (f : Fin 2 → M) :
    ∑ k, f k = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

theorem tr : Matrix.trace mj = (0 : R) := by
  simp [Matrix.trace, Matrix.diag, sum_fin2, mj]

end P4

end InfoGeometry.Probes.W2v4
