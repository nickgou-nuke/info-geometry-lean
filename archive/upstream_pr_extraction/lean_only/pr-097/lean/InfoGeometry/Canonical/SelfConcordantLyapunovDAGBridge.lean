import InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-!
# Self-concordant Lyapunov closure in the Apollonius lambda DAG

This bridge records that the information-potential node already reachable in
the theorem DAG has a concrete globally strict Lyapunov realization on the
positive scalar chart.
-/

noncomputable section

namespace InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge

open InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-- The information-potential stage is reachable from the affine seed. -/
theorem affine_reaches_selfConcordant_informationPotential :
    Reachable .affineCoordinate .informationPotential :=
  affine_reaches_informationPotential

/-- The reached information-potential stage admits the global strict
self-concordant Lyapunov theorem on `x > 0`. -/
theorem reachable_informationPotential_has_global_lyapunov
    (kappa x : ℝ) (hkappa : 0 < kappa) (hx : 0 < x) :
    Reachable .affineCoordinate .informationPotential ∧
    (0 ≤ lyapunovPotential x) ∧
    (lyapunovPotential x = 0 ↔ x = 1) ∧
    (lyapunovLieDerivative kappa x ≤ 0) ∧
    (naturalGradientField kappa x = 0 ↔ x = 1) ∧
    (x ≠ 1 → lyapunovLieDerivative kappa x < 0) := by
  have hL := global_selfConcordant_lyapunov kappa x hkappa hx
  exact ⟨affine_reaches_informationPotential,
    hL.1,
    hL.2.1,
    hL.2.2.2.2.2.1,
    hL.2.2.2.2.2.2.1,
    hL.2.2.2.2.2.2.2⟩

end InfoGeometry.Canonical.SelfConcordantLyapunovDAGBridge

end noncomputable section
