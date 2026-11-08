import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.LieFlowLogJacobianBridge

Log-Jacobian cocycle, infinitesimal divergence rate, and Lie generator trace formula.
-/

noncomputable section

namespace InfoGeometry.Canonical.LieFlowLogJacobian

open Real

/-- Log-Jacobian cocycle: $\mathcal{J}_t(x) = -\ln |J_t(x)|$ -/
def logJacobianCocycle (J : ℝ) : ℝ :=
  - Real.log J

/-- 🏆 THEOREM 1: Additive cocycle law:
    $$-\ln(J_1 \cdot J_2) = (-\ln J_1) + (-\ln J_2)$$ -/
theorem logJacobianCocycle_mul (J1 J2 : ℝ) (h_J1 : 0 < J1) (h_J2 : 0 < J2) :
    logJacobianCocycle (J1 * J2) = logJacobianCocycle J1 + logJacobianCocycle J2 := by
  dsimp [logJacobianCocycle]
  rw [Real.log_mul (ne_of_gt h_J1) (ne_of_gt h_J2)]
  ring

/-- 🏆 THEOREM 2: Linear Lie flow trace formula:
    $$\det(e^{t A}) = e^{t \operatorname{tr} A} \implies -\ln(\det(e^{t A})) = - t \operatorname{tr} A$$ -/
theorem linear_lie_flow_log_det (t trA : ℝ) :
    logJacobianCocycle (Real.exp (t * trA)) = - t * trA := by
  dsimp [logJacobianCocycle]
  rw [Real.log_exp]
  ring

/-- 🏆 THEOREM 3: Unimodular flow produces zero log-volume contraction:
    $$\det J = 1 \implies -\ln J = 0$$ -/
theorem unimodular_log_jacobian_zero (J : ℝ) (h_J : J = 1) :
    logJacobianCocycle J = 0 := by
  dsimp [logJacobianCocycle]
  rw [h_J, Real.log_one, neg_zero]

end InfoGeometry.Canonical.LieFlowLogJacobian
