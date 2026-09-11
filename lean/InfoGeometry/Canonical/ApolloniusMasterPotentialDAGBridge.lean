import InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-! A small bridge from the affine DAG to the existing information-potential
and Lyapunov owners.  The two analytic carriers remain separate. -/
namespace InfoGeometry.Canonical.ApolloniusMasterPotentialDAGBridge

open InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
open InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

theorem masterPotential_stage_reachable :
    Reachable .affineCoordinate .informationPotential :=
  affine_reaches_informationPotential

theorem masterPotential_helmholtz_packet (sigma t : ℝ) :
    rotationalField sigma t = quarterTurn (dilationField sigma t) := by
  rfl

theorem masterPotential_lyapunov_packet (κ x : ℝ)
    (hκ : 0 < κ) (hx : 0 < x) :
    Reachable .affineCoordinate .selfConcordantLyapunov ∧
    lyapunovLieDerivative κ x = -κ * (x - 1) ^ 2 ∧
    lyapunovLieDerivative κ x ≤ 0 := by
  refine ⟨affine_reaches_selfConcordantLyapunov, ?_, ?_⟩
  · exact lyapunovLieDerivative_eq κ x (ne_of_gt hx)
  · exact lyapunovLieDerivative_nonpos κ x (le_of_lt hκ) (ne_of_gt hx)

end InfoGeometry.Canonical.ApolloniusMasterPotentialDAGBridge
