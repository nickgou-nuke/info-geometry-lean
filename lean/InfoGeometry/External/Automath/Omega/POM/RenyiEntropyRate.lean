import InfoGeometry.External.Automath.Omega.POM.DiagonalHighMoments
import InfoGeometry.External.Automath.Omega.POM.RenyiEndpoint

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the Rényi entropy-rate spectrum theorem in
    `2026_projection_ontological_mathematics_core_tams`.
    thm:renyi-entropy-rate -/
theorem paper_projection_renyi_entropy_rate
    (momentIdentity fixedQEntropyRate renyiEndpointLaw diagonalEntropyLimit : Prop)
    (hMomentIdentity : momentIdentity)
    (hFixedQ : momentIdentity → fixedQEntropyRate)
    (hEndpoint : fixedQEntropyRate → renyiEndpointLaw)
    (hDiagonal : fixedQEntropyRate → diagonalEntropyLimit) :
    fixedQEntropyRate ∧ renyiEndpointLaw ∧ diagonalEntropyLimit := by
  have hFixedQRate : fixedQEntropyRate := hFixedQ hMomentIdentity
  exact ⟨hFixedQRate, hEndpoint hFixedQRate, hDiagonal hFixedQRate⟩

end Omega.POM
