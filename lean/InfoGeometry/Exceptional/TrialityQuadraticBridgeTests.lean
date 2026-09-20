import InfoGeometry.Algebra.SplitOctonionTriality
import InfoGeometry.Algebra.TrialityEigenspaceBracket
import InfoGeometry.Canonical.TypedTrialityTrilinear
import InfoGeometry.Exceptional.SplitOctonionContactCantor
import InfoGeometry.Synthesis.QuadraticContactDerivatives

namespace InfoGeometry.Exceptional.TrialityQuadraticBridgeTests

open InfoGeometry.Algebra.CyclicOrderThree
open InfoGeometry.Synthesis
open InfoGeometry.Synthesis.QuadraticContactDerivatives

example : orbitSum (LinearMap.id : Module.End ℝ ℝ) 1 = 3 := by
  norm_num [orbitSum_apply]

example : reynolds (LinearMap.id : Module.End ℝ ℝ) = LinearMap.id := by
  apply LinearMap.ext
  intro value
  exact reynolds_of_fixed _ value rfl

example : action 1 (1 / 2) 0 = 0 :=
  (action_zero_iff 1 (1 / 2) 0 (by norm_num)).mpr ⟨by norm_num, rfl⟩

example : 0 < action 1 0 0 :=
  action_strict_minimum 1 0 0 (by norm_num) (by norm_num)

example : action 0 5 0 = 1 / 4 := by
  norm_num [action, ImpedanceMatchingDuality.criticalValue_formula,
    ImpedanceMatchingDuality.capacity_vertex]

example : HasDerivAt (ImpedanceMatchingDuality.fisher_capacity 2) 0 (1 / 4) := by
  convert capacity_hasDerivAt 2 (1 / 4) using 1 <;> norm_num

example : deriv (deriv ImpedanceMatchingDuality.criticalValue) 0 = 2 :=
  criticalValue_second_deriv 0

example {Carrier : Type*} [Ring Carrier] [StarRing Carrier]
    (family : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 3) Carrier) :
    SplitOctonionContactCantor.defect_operator family 1 = 0 :=
  SplitOctonionContactCantor.defect_one family

#print axioms InfoGeometry.Algebra.CyclicOrderThree.orbitSum_eq_zero_iff_boundary
#print axioms InfoGeometry.Algebra.SplitOctonionTriality.cycle_cancellation_iff_boundary
#print axioms InfoGeometry.Algebra.TrialityG2.cubic_eigenspace_bracket_fixed
#print axioms CanonicalZornCompositionTriality.trialityTrilinear_cubic_phase
#print axioms SplitOctonionContactCantor.defect_vanishes_iff_commutes
#print axioms capacity_hasDerivAt
#print axioms action_second_variation_positive

end InfoGeometry.Exceptional.TrialityQuadraticBridgeTests
