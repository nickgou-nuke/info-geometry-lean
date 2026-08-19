import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Algebra.AnyonFiniteSpinBraid

open Matrix
open InfoGeometry.Algebra.FiniteSpin

/-- The local finite spin ladder pair used as creation/annihilation data. -/
structure LocalDefectStepOperators where
  create : Mat2C
  annihilate : Mat2C

def LocalDefectStepOperatorsLaws (steps : LocalDefectStepOperators) : Prop :=
  steps.create * steps.create = 0 ∧
  steps.annihilate * steps.annihilate = 0

namespace LocalDefectStepOperators

variable (steps : LocalDefectStepOperators)
variable (hsteps : LocalDefectStepOperatorsLaws steps)

/-- The creation mechanism is nilpotent in the finite two-state block. -/
theorem creation_nilpotent (hsteps : LocalDefectStepOperatorsLaws steps) :
    steps.create * steps.create = 0 :=
  hsteps.1

/-- The annihilation mechanism is nilpotent in the finite two-state block. -/
theorem annihilation_nilpotent (hsteps : LocalDefectStepOperatorsLaws steps) :
    steps.annihilate * steps.annihilate = 0 :=
  hsteps.2

end LocalDefectStepOperators

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

/-- Canonical finite spin defect steps: `J₊` creates and `J₋` annihilates. -/
def canonicalDefectSteps : LocalDefectStepOperators where
  create := J_plus
  annihilate := J_minus

theorem canonicalDefectSteps_laws :
    LocalDefectStepOperatorsLaws canonicalDefectSteps := by
  exact ⟨J_plus_nilpotent, J_minus_nilpotent⟩

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
