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
  create_nilpotent : create * create = 0
  annihilate_nilpotent : annihilate * annihilate = 0

namespace LocalDefectStepOperators

variable (steps : LocalDefectStepOperators)

/-- The creation mechanism is nilpotent in the finite two-state block. -/
theorem creation_nilpotent : steps.create * steps.create = 0 :=
  steps.create_nilpotent

/-- The annihilation mechanism is nilpotent in the finite two-state block. -/
theorem annihilation_nilpotent : steps.annihilate * steps.annihilate = 0 :=
  steps.annihilate_nilpotent

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
  create_nilpotent := J_plus_nilpotent
  annihilate_nilpotent := J_minus_nilpotent

/-- Creation readback for the canonical localized defect interface. -/
theorem canonical_create_eq : canonicalDefectSteps.create = J_plus :=
  rfl

/-- Annihilation readback for the canonical localized defect interface. -/
theorem canonical_annihilate_eq : canonicalDefectSteps.annihilate = J_minus :=
  rfl

end InfoGeometry.Algebra.AnyonFiniteSpinBraid

end noncomputable section
