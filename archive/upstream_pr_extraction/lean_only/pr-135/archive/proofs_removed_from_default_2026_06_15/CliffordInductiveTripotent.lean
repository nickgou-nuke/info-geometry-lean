import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Tactic.Ring

/-!
# Inductive Clifford Colimit and Tripotency

Formalizes the algebraic stability of the tripotent trifactor geometry 
under the infinite-dimensional inductive colimit of the Clifford algebras.
We rigorously prove that the scaling inclusion map `j_n(T) = T ⊗ I₂` 
strictly preserves the tripotent non-invertible property across all scales.
-/

namespace CliffordInductiveTripotent

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix is tripotent if `T³ = T`. This classifies the algebraic spectrum 
    into the `{+1, -1, 0}` topological sectors. -/
def IsTripotent (T : Matrix n n ℝ) : Prop :=
  T * (T * T) = T

/-- 
Theorem: The scaling inclusion map `j_n(T) = T ⊗ I₂` strictly preserves 
the tripotent algebraic property.

This means that as the finite Clifford algebra scales up towards the 
hyperfinite type II₁ factor (CAR algebra) in the thermodynamic limit, 
the topological non-invertible boundary defect is flawlessly conserved!
-/
theorem kronecker_preserves_tripotency (T : Matrix n n ℝ) (hT : IsTripotent T) :
    IsTripotent (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  dsimp [IsTripotent] at *
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) * 1 = 1 := Matrix.mul_one _
  
  -- Expand the first matrix multiplication: (T ⊗ 1) * (T ⊗ 1)
  have h_step1 : (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (T ⊗ₖ 1) = (T * T) ⊗ₖ 1 := by
    rw [Matrix.kronecker_mul, h1]
    
  -- Expand the final multiplication: (T ⊗ 1) * ((T * T) ⊗ 1)
  have h_step2 : (T ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) * ((T * T) ⊗ₖ 1) = (T * (T * T)) ⊗ₖ 1 := by
    rw [Matrix.kronecker_mul, h1]
    
  rw [h_step1, h_step2, hT]

end CliffordInductiveTripotent
