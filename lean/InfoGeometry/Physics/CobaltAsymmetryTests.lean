import InfoGeometry.Physics.CobaltAsymmetry
import InfoGeometry.Physics.CobaltAsymmetryDependency

namespace InfoGeometry.Physics.CobaltAsymmetryTests

open CobaltAsymmetry

example : betaAngularIntensity 1 0 = 0 := by
  norm_num [betaAngularIntensity]

example : betaAngularIntensity 1 Real.pi = 2 := by
  norm_num [betaAngularIntensity]

example : ¬ IsReflectionInvariant (betaAngularIntensity 1) := by
  rw [beta_reflection_invariant_iff]
  norm_num

example : IsReflectionInvariant (betaAngularIntensity 0) :=
  (beta_reflection_invariant_iff 0).mpr rfl

example : gammaAngularModel 1 (1 / 2) (Real.pi / 2) = 1 / 2 := by
  rw [gamma_equator_value]
  norm_num

example : IsAnisotropic (gammaAngularModel 1 (1 / 2)) ∧
    IsReflectionInvariant (gammaAngularModel 1 (1 / 2)) :=
  ⟨gamma_anisotropic _ _ (by norm_num), gamma_reflection_invariant _ _⟩

example : gammaAngularModel 1 2 (Real.pi / 2) < 0 := by
  rw [gamma_equator_value]
  norm_num

#print axioms betaAngularIntensity_nonneg
#print axioms beta_reflection_invariant_iff
#print axioms beta_anisotropic
#print axioms gamma_global_bounds
#print axioms gamma_minimal_at_equator
#print axioms gamma_anisotropic
#print axioms anisotropy_does_not_imply_reflection_violation
#print axioms CobaltAsymmetryDependency.beta_and_gamma_branches_incomparable

end InfoGeometry.Physics.CobaltAsymmetryTests
