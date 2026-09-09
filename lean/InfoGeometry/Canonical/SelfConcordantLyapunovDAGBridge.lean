import InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-!
The information-potential stage of the canonical DAG is backed by the
existing scalar self-concordant Lyapunov owner.  This file is only the bridge;
it introduces no second potential or reachability relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge

open InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

theorem affine_reaches_selfConcordant_informationPotential :
    Reachable .affineCoordinate .informationPotential :=
  affine_reaches_informationPotential

theorem reachable_informationPotential_has_global_lyapunov
    (kappa x : ℝ) (hkappa : 0 < kappa) (hx : 0 < x) :
    Reachable .affineCoordinate .informationPotential ∧
    (0 ≤ lyapunovPotential x) ∧
    (lyapunovPotential x = 0 ↔ x = 1) ∧
    (lyapunovLieDerivative kappa x ≤ 0) ∧
    (naturalGradientField kappa x = 0 ↔ x = 1) ∧
    (x ≠ 1 → lyapunovLieDerivative kappa x < 0) := by
  have hL := global_selfConcordant_lyapunov kappa x hkappa hx
  rcases hL with ⟨hpot, hzero, hmetric, hderiv, hstrict⟩
  refine ⟨affine_reaches_informationPotential, hpot, hzero, hderiv,
    naturalGradientField_zero_iff kappa x hkappa hx, ?_⟩
  intro hne
  exact lyapunovLieDerivative_neg kappa x hkappa (ne_of_gt hx) hne

end InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge
