import InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
import InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
import InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-!
# Master-potential bridge into the Apollonius lambda DAG

This owner records that the already-reachable information-potential stage now
carries two theorem-owned structures:

* the corrected two-dimensional Cauchy--Riemann/Helmholtz packet;
* the global self-concordant Lyapunov/natural-gradient packet.

No spectral or zero-set interpretation is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.ApolloniusMasterPotentialDAGBridge

open InfoGeometry.Canonical.ApolloniusLambdaDAGClosure
open InfoGeometry.Canonical.ApolloniusMasterPotentialHelmholtz
open InfoGeometry.Canonical.SelfConcordantLogGeneratingLyapunov

/-- The affine seed reaches the information-potential stage. -/
theorem masterPotential_stage_reachable :
    Reachable .affineCoordinate .informationPotential :=
  affine_reaches_informationPotential

/-- The reachable information-potential stage carries the corrected Helmholtz packet. -/
theorem reachable_masterPotential_helmholtz
    (sigma t gamma : ℝ)
    (hscale : conformalScaleSq sigma t ≠ 0) :
    Reachable .affineCoordinate .informationPotential ∧
    metricGradientPhi sigma t =
      InfoGeometry.Arithmetic.RiemannApolloniusVectorFields.dilationCoordinateField sigma t ∧
    InfoGeometry.Arithmetic.RiemannApolloniusVectorFields.rotationalField sigma t =
      J (metricGradientPhi sigma t) := by
  refine ⟨masterPotential_stage_reachable, ?_, ?_⟩
  · exact metricGradientPhi_eq_dilation sigma t hscale
  · exact rotational_eq_J_metricGradientPhi sigma t hscale

/-- The same reachable information-potential branch also carries the global
strict self-concordant Lyapunov theorem. -/
theorem reachable_masterPotential_lyapunov
    (kappa x : ℝ) (hkappa : 0 < kappa) (hx : 0 < x) :
    Reachable .affineCoordinate .selfConcordantLyapunov ∧
    lyapunovLieDerivative kappa x = -kappa * (x - 1) ^ 2 ∧
    lyapunovLieDerivative kappa x ≤ 0 ∧
    (x ≠ 1 → lyapunovLieDerivative kappa x < 0) := by
  refine ⟨affine_reaches_selfConcordantLyapunov, ?_, ?_, ?_⟩
  · exact lyapunovLieDerivative_eq kappa x hx
  · exact lyapunovLieDerivative_nonpos (le_of_lt hkappa) hx
  · intro hx1
    exact lyapunovLieDerivative_neg hkappa hx hx1

/-- Combined theorem-safe potential-theory closure. -/
theorem masterPotential_global_closure
    (sigma t gamma kappa x : ℝ)
    (hscale : conformalScaleSq sigma t ≠ 0)
    (hkappa : 0 < kappa) (hx : 0 < x) :
    Reachable .affineCoordinate .informationPotential ∧
    Reachable .affineCoordinate .selfConcordantLyapunov ∧
    metricGradientPhi sigma t =
      InfoGeometry.Arithmetic.RiemannApolloniusVectorFields.dilationCoordinateField sigma t ∧
    InfoGeometry.Arithmetic.RiemannApolloniusVectorFields.rotationalField sigma t =
      J (metricGradientPhi sigma t) ∧
    lyapunovLieDerivative kappa x = -kappa * (x - 1) ^ 2 ∧
    lyapunovLieDerivative kappa x ≤ 0 := by
  exact ⟨masterPotential_stage_reachable,
    affine_reaches_selfConcordantLyapunov,
    metricGradientPhi_eq_dilation sigma t hscale,
    rotational_eq_J_metricGradientPhi sigma t hscale,
    lyapunovLieDerivative_eq kappa x hx,
    lyapunovLieDerivative_nonpos (le_of_lt hkappa) hx⟩

end InfoGeometry.Canonical.ApolloniusMasterPotentialDAGBridge

end noncomputable section
