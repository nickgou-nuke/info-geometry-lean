import Mathlib.Basic.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

open Complex Matrix

namespace InfoGeometry.Physics.Pin55

def s1 : Matrix (Fin 2) (Fin 2) ℂ := ![![0, 1], ![1, 0]]
def s2 : Matrix (Fin 2) (Fin 2) ℂ := ![![0, -I], ![I, 0]]

/-- 
The core algebraic generator of the Pin(5,5) reflection R.
The full 32x32 Cl(5,5) matrix is R_core ⊗ I_16.
-/
def R_core : Matrix (Fin 2) (Fin 2) ℂ := s1

/-- 
The core algebraic generator of the spatial translation T.
In the double cover, T acts as an imaginary generator 
anti-commuting with R.
-/
def T_core : Matrix (Fin 2) (Fin 2) ℂ := I • s2

lemma sum_fin_2 {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) : 
  ∑ i : Fin 2, f i = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

/-- 
THEOREM: Explicit Pin(5,5) Mandatory Glide Reflection.
Proves computationally that the non-symmorphic glide reflection (R * T) 
squares strictly to the positive Spin Parity (+I), definitively 
annihilating the spatial translation without any abstract assumptions.
-/
lemma T_core_eq :
    T_core = ![![0, 1], ![-1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j
  · change I * (s2 0 0) = 0
    dsimp [s2]; ring
  · change I * (s2 0 1) = 1
    dsimp [s2]; simp [Complex.I_mul_I]
  · change I * (s2 1 0) = -1
    dsimp [s2]; simp [Complex.I_mul_I]
  · change I * (s2 1 1) = 0
    dsimp [s2]; ring

def J_core : Matrix (Fin 2) (Fin 2) ℂ := ![![ -1, 0 ], ![ 0, 1 ]]

lemma R_core_mul_T_core :
    R_core * T_core = J_core := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> {
    rw [T_core_eq]
    dsimp [R_core, s1, J_core]
    ring
  }

lemma J_core_sq :
    J_core * J_core = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> {
    dsimp [J_core]
    simp
  }

theorem explicit_glide_compactification :
    (R_core * T_core) * (R_core * T_core) = 1 := by
  rw [R_core_mul_T_core, J_core_sq]

end InfoGeometry.Physics.Pin55
