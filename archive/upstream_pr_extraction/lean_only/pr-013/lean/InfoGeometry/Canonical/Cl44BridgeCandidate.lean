import InfoGeometry.Canonical.OperatorProjectorMismatch
import InfoGeometry.Canonical.DilationKKTBridge
import InfoGeometry.Canonical.ChiralKMSOwner
import InfoGeometry.Canonical.WeylSupertraceOwner
import InfoGeometry.Canonical.ConformalProjectorAgreement
import InfoGeometry.Canonical.EntanglementResidualOwner

/-!
# Cl(4,4) bridge candidate

`Cl(4,4)` is recorded as a candidate bridge/readout, not a closure theorem and
not the conformal group itself.  The group-level readout must be supplied as a
separate `spin44OrSO44ReadoutWitness`; standard 3+1 conformal gravity would need
an additional signature-translation witness.
-/

namespace InfoGeometry.Canonical.Cl44BridgeCandidate

set_option linter.dupNamespace false in
/-- Candidate bridge: green only when every witness field is supplied. -/
@[rep_depth transport]
structure Cl44BridgeCandidate where
  operatorSystem : Type
  drazinMPAgreementWitness : Prop
  dilationWitness : Prop
  chiralKMSWitness : Prop
  weylSupertraceWitness : Prop
  conformalEquivarianceWitness : Prop
  metricTransportWitness : Prop
  realCliffordRepresentationWitness : Prop
  splitSignatureWitness : Prop
  spin44OrSO44ReadoutWitness : Prop
  nullConePreservationWitness : Prop
  quantizationWitness : Prop
  metricTransportCertified : metricTransportWitness
  realCliffordRepresentationCertified : realCliffordRepresentationWitness
  nullConePreservationCertified : nullConePreservationWitness
  quantizationCertified : quantizationWitness

/-- A tear point is the explicit failure/lack of one candidate witness. -/
@[rep_depth transport]
structure Cl44BridgeTearPoint where
  failedWitnessName : String
  failureCertificate : Prop

/-- A supplied candidate exposes all obligations; it does not prove conformal gravity. -/
theorem candidate_requires_metric_and_clifford_witnesses
    (C : Cl44BridgeCandidate) :
    C.metricTransportWitness ∧ C.realCliffordRepresentationWitness ∧
      C.nullConePreservationWitness ∧ C.quantizationWitness := by
  exact ⟨C.metricTransportCertified, C.realCliffordRepresentationCertified,
    C.nullConePreservationCertified, C.quantizationCertified⟩

end InfoGeometry.Canonical.Cl44BridgeCandidate
