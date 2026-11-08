import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

open Matrix

namespace InfoGeometry.Canonical.GenericObliqueIdempotentAnomaly

variable {R : Type*} [Ring R] [Nontrivial R]

abbrev E00 : Matrix (Fin 2) (Fin 2) R := Matrix.single 0 0 1
abbrev E01 : Matrix (Fin 2) (Fin 2) R := Matrix.single 0 1 1

def oblique : Matrix (Fin 2) (Fin 2) R := E00 + E01

def leftProjector : Matrix (Fin 2) (Fin 2) R := E00

def commutator (X Y : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  X * Y - Y * X

theorem oblique_idempotent : oblique (R := R) * oblique = oblique := by
  have h00 : E00 (R := R) * E00 = E00 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]
  have h001 : E00 (R := R) * E01 = E01 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  have h100 : E01 (R := R) * E00 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  have h101 : E01 (R := R) * E01 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  unfold oblique
  simp only [add_mul, mul_add, h00, h001, h100, h101, add_zero, zero_add]

theorem leftProjector_idempotent : leftProjector (R := R) * leftProjector = leftProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leftProjector, E00, Matrix.mul_apply, Fin.sum_univ_two]

theorem oblique_commutator_leftProjector :
    commutator (oblique (R := R)) leftProjector = -E01 := by
  have h00 : E00 (R := R) * E00 = E00 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]
  have h001 : E00 (R := R) * E01 = E01 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  have h100 : E01 (R := R) * E00 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  unfold commutator oblique leftProjector
  rw [add_mul, mul_add, h00, h100, h001]
  abel

theorem E01_ne_zero : (E01 (R := R)) ≠ 0 := by
  intro h
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
  simpa [E01, Matrix.single] using hentry

theorem oblique_commutator_nonzero :
    commutator (oblique (R := R)) leftProjector ≠ 0 := by
  rw [oblique_commutator_leftProjector]
  intro h
  exact E01_ne_zero (neg_eq_zero.mp h)

end InfoGeometry.Canonical.GenericObliqueIdempotentAnomaly
