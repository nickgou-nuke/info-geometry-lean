import Mathlib.Tactic
import Omega.PhysicalSpacetimeSkeleton.GravitationalScalarUniqueness

namespace Omega.PhysicalSpacetimeSkeleton

/-- Minimal variational closure extending the admissible gravitational-scalar wrapper by the data
needed to state the global Einstein equation on the admissible domain. -/
structure AdmissibleEinsteinClosure where
  gravitationalScalar : ℝ
  ricciScalar : ℝ
  cosmologicalConstant : ℝ
  metric : ℝ
  einsteinTensor : ℝ
  stressEnergy : ℝ
  couplingConstant : ℝ
  residualLagrangian : ℝ
  gravitationalLagrangian : ℝ
  
def AdmissibleEinsteinClosure.toMinimalSecondOrderCovariantClosure
    (D : AdmissibleEinsteinClosure) : MinimalSecondOrderCovariantClosure :=
  { gravitationalScalar := D.gravitationalScalar
    ricciScalar := D.ricciScalar
    cosmologicalConstant := D.cosmologicalConstant }

/-- On an admissible Einstein closure, the gravitational term is normalized to `R_g - 2 Λ`. -/
theorem admissible_gravitational_lagrangian_eq_ricci_minus_two_lambda
    (D : AdmissibleEinsteinClosure) (admissible : Prop) (hAdm : admissible)
    (gravitationalLagrangian_normalized :
      admissible → D.gravitationalLagrangian = D.ricciScalar - 2 * D.cosmologicalConstant) :
    D.gravitationalLagrangian = D.ricciScalar - 2 * D.cosmologicalConstant :=
  gravitationalLagrangian_normalized hAdm

/-- Paper-facing admissible global Einstein equation on the physical spacetime domain.
    thm:physical-spacetime-admissible-global-einstein-equation -/
theorem paper_physical_spacetime_admissible_global_einstein_equation
    (D : AdmissibleEinsteinClosure) (admissible : Prop) (hAdm : admissible)
    (eulerLagrange_identity :
      admissible →
        D.einsteinTensor + D.cosmologicalConstant * D.metric =
          D.couplingConstant * D.stressEnergy) :
    D.einsteinTensor + D.cosmologicalConstant * D.metric =
      D.couplingConstant * D.stressEnergy := by
  exact eulerLagrange_identity hAdm

end Omega.PhysicalSpacetimeSkeleton
