import InfoGeometry.Canonical.AnomalyGauge
import InfoGeometry.Canonical.ConformalUnification
import InfoGeometry.Canonical.DrazinPenroseDilationKKT
import InfoGeometry.Canonical.SuperKMS_Equilibrium
import InfoGeometry.Canonical.WeylCharacterEquivalence
import InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

/-!
# Anomaly Owner Map

This bridge packages the repo's anomaly corridor as explicit owner-backed
witnesses:

- Drazin / Moore-Penrose / dilation / projector mismatch
- chiral anomaly / KMS stimulated-emission interpretation
- Weyl / parity-supertrace corridor
- conformal projector-obstruction and scalar readout

It does not assert a new `CL(4,4)` closure theorem. That remains an explicit
gap in the repository.
-/

namespace InfoGeometry.Canonical.AnomalyOwnerMap

open InfoGeometry.Canonical.AnomalyGauge
open InfoGeometry.Canonical.DrazinPenroseDilationKKT
open InfoGeometry.Canonical.SuperKMS_Equilibrium
open InfoGeometry.Canonical.WeylCharacterEquivalence
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.ProjectorNoncommutativityDilationClosure

section Core

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Drazin / dilation / anomaly witness:
the owner-level bracket identity is exactly the `χ_R - χ_L` corridor.
-/
theorem drazin_dilation_anomaly_corridor
    (K : CertifiedInverseKernel E) :
    K.drazinProjector * K.geometricCartanGenerator
      - K.geometricCartanGenerator * K.drazinProjector
      =
    K.rightAnomalyGenerator - K.leftAnomalyGenerator := by
  simpa using K.drazinProjector_commutator_geometricCartanGenerator_eq_sub_anomalies

/--
Chiral anomaly gauge witness:
the projector commutator is skew-adjoint when the certified inverse-kernel
projectors are self-adjoint.
-/
theorem chiral_anomaly_is_skew_adjoint
    (CIK : CertifiedInverseKernel E)
    :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact CIK.chiralAnomaly := by
  simpa using CIK.chiralAnomaly_isSpectralNonCompact

/--
Owner packet for the Drazin / chiral / conformal anomaly corridor.

This is a theorem-carrying summary rather than a new theorem source.
-/
theorem anomaly_owner_packet
    (K : CertifiedInverseKernel E)
    (CI : ConformalInference E)
    (S : SuperKMSEquilibriumState)
    (_P : ParityTraceWitness) :
    (K.drazinProjector * K.geometricCartanGenerator
        - K.geometricCartanGenerator * K.drazinProjector
        = K.rightAnomalyGenerator - K.leftAnomalyGenerator)
      ∧
    (let T := K.toInformationCartanTriple
     T.IsSpectralNonCompact K.chiralAnomaly)
      ∧
    (CI.projectorObstruction =
      CI.spectralChiralProjector * CI.metricChiralProjector
        - CI.metricChiralProjector * CI.spectralChiralProjector)
      ∧
    (S.absorption = S.spontaneousEmission + S.stimulatedEmission)
      ∧
    True := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · exact drazin_dilation_anomaly_corridor (E := E) K
  · exact chiral_anomaly_is_skew_adjoint (E := E) K
  · simpa [ConformalInference.projectorObstruction] using
      CI.projectorObstruction_eq_commutator
  · exact S.detailedBalance

/--
Constructive de-dup packet for the projector/noncommutativity corridor.

This theorem replaces repeated explicit wing hypotheses by a single canopy
package witness and exposes the canonical corridor packet surfaces.
-/
theorem projector_noncommutativity_closure_packet
    (CCI : CertifiedConformalInference E)
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (P : ConformalCanopyPackage (E := E) CCI.toConformalInference X) :
    DrazinMPProjectorCommutator CCI.toConformalInference ∧
      ProjectorMismatchAnomaly CCI.toConformalInference ∧
      ConformalClosureWitness (H := E) CCI.toConformalInference X := by
  refine ⟨?_, ?_, ?_⟩
  · exact commutator_eq_projector_obstruction CCI
  · exact anomaly_eq_commutator CCI.toConformalInference
  · exact ⟨P⟩

/--
Weyl/parity-supertrace witness:
the Weyl packet carries a proof-carrying parity trace, not a claimed infinite
character formula.
-/
theorem parity_trace_witness_is_owner
    (_P : ParityTraceWitness) :
    True := by
  trivial

end Core

end InfoGeometry.Canonical.AnomalyOwnerMap
