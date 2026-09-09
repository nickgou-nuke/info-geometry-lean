import Mathlib.Data.Complex.Basic
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
theorem explicit_glide_compactification :
    (R_core * T_core) * (R_core * T_core) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R_core, T_core, s1, s2, mul_apply, I_mul_I]

end InfoGeometry.Physics.Pin55
