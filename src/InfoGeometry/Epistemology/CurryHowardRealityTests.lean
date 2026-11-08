import InfoGeometry.Epistemology.CurryHowardReality
import InfoGeometry.Epistemology.CurryHowardRealityDependency

namespace InfoGeometry.Epistemology.CurryHowardRealityTests

open CurryHowardReality

noncomputable section

def unitEnvironment : Environment := ⟨1, zero_lt_one⟩

example : balance unitEnvironment = 1 / 2 := by
  norm_num [balance, unitEnvironment]

example : response unitEnvironment (balance unitEnvironment) = 1 / 4 := by
  rw [response_at_balance]
  norm_num [unitEnvironment]

example : ¬ IsMaximizer unitEnvironment 0 := by
  rw [isMaximizer_iff]
  norm_num [balance, unitEnvironment]

example (environment : Environment) : Nonempty (CertifiedOptimum environment) :=
  ⟨certifiedOptimum environment⟩

example (environment : Environment) (first second : CertifiedOptimum environment) :
    first = second := Subsingleton.elim first second

example : (0 : ℝ) ≠ 1 ∧ normalization unitEnvironment 0 = normalization unitEnvironment 1 :=
  ⟨zero_ne_one, rfl⟩

example : relaxation unitEnvironment (1 / 2) 0 = 1 / 4 := by
  norm_num [relaxation, balance, unitEnvironment]

example : response unitEnvironment 0 < response unitEnvironment (relaxation unitEnvironment (1 / 2) 0) := by
  norm_num [response, relaxation, balance, unitEnvironment]

example : response unitEnvironment (relaxation unitEnvironment 3 0) < response unitEnvironment 0 := by
  norm_num [response, relaxation, balance, unitEnvironment]

#print axioms response_completed_square
#print axioms capacity_isGreatest
#print axioms response_eq_capacity_iff
#print axioms isMaximizer_iff
#print axioms normalization_idempotent
#print axioms equal_outputs_do_not_identify_inputs
#print axioms relaxation_gap
#print axioms relaxation_improves_response
#print axioms CurryHowardRealityDependency.normalization_and_dynamics_incomparable

end

end InfoGeometry.Epistemology.CurryHowardRealityTests
