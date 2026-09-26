import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
import InfoGeometryCore.Basic

open InfoGeometryCore

/-!
# CL(1,1) Matrix Relations and Basis in M₂(ℝ)

This module formalizes the real 2×2 matrix representation of the Clifford algebra CL(1,1).
It establishes:
1. The generator relations for `sigma1` and `epsilon` with respect to identity matrix `I2`.
2. That the basis matrices `{I2, sigma1, epsilon, sigma3}` span `Matrix (Fin 2) (Fin 2) ℝ`.
3. The conjunction of these two properties in `bott_trifactor_capstone`.
-/

noncomputable section

namespace BottPeriodicityReconciliation

/-! ### 1. CL(1,1) Generators and Basis in M₂(ℝ) -/

/-- First real Pauli matrix `!![0, 1; 1, 0]`. -/
def sigma1R : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- Third real Pauli matrix `!![1, 0; 0, -1]`. -/
def sigma3R : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- Identity matrix in `Matrix (Fin 2) (Fin 2) ℝ`. -/
def I2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]

/-- Alias for `sigma1R`. -/
abbrev sigma1 := sigma1R

/-- Split Clifford generator matrix `!![0, 1; -1, 0]`. -/
def epsilon : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- Alias for `sigma3R`. -/
abbrev sigma3 := sigma3R

/--
Generator relations for CL(1,1) in M₂(ℝ):
`sigma1 * sigma1 = I2`, `epsilon * epsilon = -I2`, and `sigma1 * epsilon + epsilon * sigma1 = 0`.
-/
theorem cl11_generator_relations :
    sigma1 * sigma1 = I2 ∧
    epsilon * epsilon = -I2 ∧
    sigma1 * epsilon + epsilon * sigma1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sigma1R, epsilon, I2, Matrix.mul_apply, Fin.sum_univ_two]

/--
The four matrices `I2`, `sigma1`, `epsilon`, and `sigma3` span `Matrix (Fin 2) (Fin 2) ℝ`.
For any matrix `A`, `A = a • I2 + b • sigma1 + c • epsilon + d • sigma3` where:
- `a = (A 0 0 + A 1 1) / 2`
- `b = (A 0 1 + A 1 0) / 2`
- `c = (A 0 1 - A 1 0) / 2`
- `d = (A 0 0 - A 1 1) / 2`
-/
theorem cl11_basis_spans_M2 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (a b c d : ℝ),
      A = a • I2 + b • sigma1 + c • epsilon + d • sigma3 := by
  use (A 0 0 + A 1 1) / 2, (A 0 1 + A 1 0) / 2, (A 0 1 - A 1 0) / 2, (A 0 0 - A 1 1) / 2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [I2, sigma1R, epsilon, sigma3R, Matrix.add_apply]
    ring

/-! ### 2. Capstone Conjunction -/

/--
Capstone theorem combining the CL(1,1) generator relations and the spanning
property of `{I2, sigma1, epsilon, sigma3}` in `Matrix (Fin 2) (Fin 2) ℝ`.
-/
theorem bott_trifactor_capstone :
    (-- CL(1,1) generators: e₁²=I, e₂²=-I, {e₁,e₂}=0
     sigma1 * sigma1 = I2 ∧ epsilon * epsilon = -I2 ∧
     sigma1 * epsilon + epsilon * sigma1 = 0) ∧
    (-- CL(1,1) ≅ M₂(ℝ): the Pauli basis spans all 2×2 real matrices
     ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
       ∃ (a b c d : ℝ),
         A = a • I2 + b • sigma1 + c • epsilon + d • sigma3) :=
  ⟨cl11_generator_relations, cl11_basis_spans_M2⟩

end BottPeriodicityReconciliation



#print axioms BottPeriodicityReconciliation.sigma1R
#print axioms BottPeriodicityReconciliation.sigma3R
#print axioms BottPeriodicityReconciliation.I2
#print axioms BottPeriodicityReconciliation.epsilon
#print axioms BottPeriodicityReconciliation.cl11_generator_relations
#print axioms BottPeriodicityReconciliation.cl11_basis_spans_M2
#print axioms BottPeriodicityReconciliation.bott_trifactor_capstone
