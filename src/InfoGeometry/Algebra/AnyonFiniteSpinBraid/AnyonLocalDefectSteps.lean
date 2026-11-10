import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite Spin Ladder and One-Mode CAR

Proves nilpotency, the canonical anticommutation relation, and number-operator
relations for the actual `2 × 2` complex spin ladder matrices.

#### BUCKET 1: CLOSED FINITE OPERATOR THEOREMS
The canonical raising/lowering pair is square-zero, satisfies the one-mode
CAR, and induces complementary algebraic occupation idempotents.

#### BUCKET 2: CONDITIONAL THEOREMS
None; all declarations here concern the explicitly defined matrices.

#### BUCKET 3: OPEN CLOSURE DEBT
No claim is made about an infinite-mode CAR representation or anyon braid
classification.
-/

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

open Matrix
open InfoGeometry.Algebra.FiniteSpin

/-- Concrete nilpotency of the finite spin raising operator. -/
theorem J_plus_nilpotent : J_plus * J_plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_plus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Concrete nilpotency of the finite spin lowering operator. -/
theorem J_minus_nilpotent : J_minus * J_minus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The canonical creation and annihilation operators satisfy the one-mode CAR. -/
theorem J_ladder_car :
    J_plus * J_minus + J_minus * J_plus = (1 : Mat2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The occupation operator is the projection onto the first spin state. -/
def occupation : Mat2C := J_plus * J_minus

/-- The occupation operator is idempotent. -/
theorem occupation_idempotent : occupation * occupation = occupation := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two ladder products are complementary algebraic idempotents: each is
idempotent, their cross-products vanish, and their sum is the identity. -/
theorem occupation_peirce_decomposition :
    occupation * occupation = occupation ∧
    (J_minus * J_plus) * (J_minus * J_plus) = J_minus * J_plus ∧
    occupation * (J_minus * J_plus) = 0 ∧
    (J_minus * J_plus) * occupation = 0 ∧
    occupation + J_minus * J_plus = (1 : Mat2C) := by
  refine ⟨occupation_idempotent, ?_, ?_, ?_, J_ladder_car⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Occupation raises the creation operator with weight one. -/
theorem occupation_comm_create :
    occupation * J_plus - J_plus * occupation = J_plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Occupation lowers the annihilation operator with weight minus one. -/
theorem occupation_comm_annihilate :
    occupation * J_minus - J_minus * occupation = -J_minus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [occupation, J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
