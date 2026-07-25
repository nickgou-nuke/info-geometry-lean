import Mathlib.Tactic

/-!
# Supercharges square

Minimal formalization of the spatial `N=1`/`osp(1|2)` atom:

* an odd supercharge `Q` satisfies `Q² = H`;
* equivalently `{Q,Q}=2H`;
* chiral parity `(-1)^F` anticommutes with `Q`;
* the collapsed boundary supercharge is nilpotent, `q²=0`.
-/

noncomputable section

namespace SuperchargeSquare

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Bulk/spatial supercharge atom. -/
def Q : M2C := !![0, 1; 1, 0]

/-- Hamiltonian/translation atom. -/
def H : M2C := 1

/-- Chiral parity `(-1)^F`. -/
def parityF : M2C := !![1, 0; 0, -1]

/-- Boundary nilpotent supercharge. -/
def qNil : M2C := !![0, 1; 0, 0]

/-- The supercharge squares to the Hamiltonian/translation atom. -/
theorem Q_sq : Q * Q = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Q, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- The super-anticommutator `{Q,Q}=2H`. -/
theorem Q_anticommutator : Q * Q + Q * Q = (2 : ℂ) • H := by
  rw [Q_sq]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [H] <;> norm_num

/-- Chiral parity squares to identity. -/
theorem parityF_sq : parityF * parityF = H := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [parityF, H, Matrix.mul_apply, Fin.sum_univ_two]

/-- Chiral parity anticommutes with the odd supercharge. -/
theorem parity_anticommutes_Q : parityF * Q + Q * parityF = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [parityF, Q, Matrix.mul_apply, Fin.sum_univ_two]

/-- The collapsed boundary supercharge is square-zero. -/
theorem qNil_sq_zero : qNil * qNil = 0 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [qNil, Matrix.mul_apply, Fin.sum_univ_two]

/-- Boundary nilpotent anticommutator vanishes. -/
theorem qNil_anticommutator_zero : qNil * qNil + qNil * qNil = 0 := by
  rw [qNil_sq_zero]
  simp

/-- Main synthesis theorem. -/
theorem supercharge_square_synthesis :
    Q * Q = H ∧
    Q * Q + Q * Q = (2 : ℂ) • H ∧
    parityF * parityF = H ∧
    parityF * Q + Q * parityF = 0 ∧
    qNil * qNil = 0 ∧
    qNil * qNil + qNil * qNil = 0 := by
  exact ⟨Q_sq, Q_anticommutator, parityF_sq, parity_anticommutes_Q,
    qNil_sq_zero, qNil_anticommutator_zero⟩

#check Q_sq
#check Q_anticommutator
#check parity_anticommutes_Q
#check qNil_sq_zero
#check supercharge_square_synthesis

end SuperchargeSquare
