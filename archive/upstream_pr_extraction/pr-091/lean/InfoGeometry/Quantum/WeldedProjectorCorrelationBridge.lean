import InfoGeometry.Quantum.HestenesKahler
import InfoGeometry.Canonical.CorrelationSymmetrization

open scoped InnerProductSpace

/-!
# InfoGeometry.Quantum.WeldedProjectorCorrelationBridge

Bridge between the welded projector-obstruction phase readout on doubled space
and the owned `K = Jε`-shifted channel-correlation surface.

This file stays narrow on purpose. It does not rename the welded phase readout
as a topological effect. It only identifies the existing operatorial readout
with the already-owned two-state and same-state correlation surfaces at the
correct untwisted perturbation channel.
-/

namespace InfoGeometry.Quantum

open InfoGeometry.Krein
open InfoGeometry.Canonical.ModularTwoStateCorrelation
open InfoGeometry.Canonical.CorrelationSymmetrization
open InfoGeometry.Canonical.ConformalUnification
open InfoGeometry.Canonical.RelationalInformationCore
open InfoGeometry.Canonical.RelativeModularPotential
open InfoGeometry.Quantum.GeometricQuantumTensor

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Untwisted perturbation channel whose `K = Jε` twist recovers the lifted
projector-obstruction operator.
-/
noncomputable def liftedProjectorObstructionCorrelationSeed
    (SCI : StarCertifiedConformalInference E) : EndH :=
  -InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (E := E)
    SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator

@[simp] theorem channelPhaseAxis_liftedProjectorObstructionCorrelationSeed
    (SCI : StarCertifiedConformalInference E) :
    InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (E := E)
      (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
      =
    SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
  calc
    InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (E := E)
        (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
        =
      -((InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (E := E)).comp
        (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis (E := E))
          SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator) := by
            simp [liftedProjectorObstructionCorrelationSeed, LinearMap.comp_apply]
    _ =
      -((-(LinearMap.id : EndH →ₗ[ℝ] EndH))
        SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator) := by
          rw [InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis_sq (E := E)]
    _ = SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator := by
          simp

/--
Under projector agreement, the welded projector-obstruction phase readout is
exactly the `K`-shifted two-state channel correlation surface evaluated on the
untwisted projector-obstruction seed and the identity channel.
-/
theorem weldedProjectorObstructionStatePhaseReadout_eq_phaseShiftedTwoStateChannelCorrelation
    (SCI : StarCertifiedConformalInference E) (ψ u v : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ u v
      =
    phaseShiftedTwoStateChannelCorrelation (E := E) u v
      (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
      (ContinuousLinearMap.id ℝ H₂) := by
  rw [weldedProjectorObstructionStatePhaseReadout_eq_projectorObstructionMetric_of_projectorAgreement
    (E := E) SCI ψ hProj]
  rw [phaseShiftedTwoStateChannelCorrelation]
  rw [channelPhaseAxis_liftedProjectorObstructionCorrelationSeed (E := E) SCI]
  simp [metricOfOperator_apply, twoStateChannelCorrelation_apply]

/--
Same-state specialization of the welded projector-obstruction phase readout as
the owned `K`-shifted channel-correlation surface.
-/
theorem weldedProjectorObstructionStatePhaseReadout_self_eq_phaseShiftedTwoStateChannelCorrelation
    (SCI : StarCertifiedConformalInference E) (ψ comparison : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ comparison comparison
      =
    phaseShiftedTwoStateChannelCorrelation (E := E) comparison comparison
      (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
      (ContinuousLinearMap.id ℝ H₂) :=
  weldedProjectorObstructionStatePhaseReadout_eq_phaseShiftedTwoStateChannelCorrelation
    (E := E) SCI ψ comparison comparison hProj

/--
Same-state specialization of the welded projector-obstruction phase readout as
the primitive comparison-state `K`-phase form on perturbation channels.
-/
theorem weldedProjectorObstructionStatePhaseReadout_self_eq_comparisonStateGeneratorPhase
    (SCI : StarCertifiedConformalInference E) (ψ comparison : H₂)
    (hProj :
      InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.rightProjector SCI.A SCI.A_MP =
        InfoGeometry.Canonical.MoorePenrose.IsMoorePenroseInverse.leftProjector SCI.A SCI.A_MP) :
    weldedProjectorObstructionStatePhaseReadout (E := E) SCI ψ comparison comparison
      =
    InfoGeometry.Canonical.RelativeModularPotential.comparisonStateGeneratorPhase
      (E := E) comparison
      (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
      (ContinuousLinearMap.id ℝ H₂) := by
  rw [comparisonStateGeneratorPhase_eq_phaseShiftedTwoStateChannelCorrelation_self
    (E := E) comparison
    (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
    (ContinuousLinearMap.id ℝ H₂)]
  exact weldedProjectorObstructionStatePhaseReadout_self_eq_phaseShiftedTwoStateChannelCorrelation
    (E := E) SCI ψ comparison hProj

/--
Infinitesimal transport law for the projector-obstruction phase seed:
the derivative of the transported `K = Jε`-shifted comparison correlation at
`t = 0` lands on the general comparison metric readout of the lifted
projector-obstruction operator.
-/
theorem deriv_comparisonTransportPhaseShiftedChannelCorrelation_liftedProjectorObstructionCorrelationSeed_at_zero_eq_comparisonMetricReadout
    (R : InfoGeometry.Canonical.RelationalInformationCore.RelationalInformationDatum (E := E))
    (SCI : StarCertifiedConformalInference E) :
    deriv
      (fun t =>
        InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportPhaseShiftedChannelCorrelation
          R
          (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
          (ContinuousLinearMap.id ℝ H₂) t)
      0
      =
    (InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout R
      (ContinuousLinearMap.id ℝ H₂))
      R.comparisonState
      (SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator
        R.comparisonState) := by
  let X : PerturbationChannel E :=
    liftedProjectorObstructionCorrelationSeed (E := E) SCI
  let Y : PerturbationChannel E := ContinuousLinearMap.id ℝ H₂
  have hbase :
      deriv
        (fun t =>
          InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportPhaseShiftedChannelCorrelation
            R X Y t)
        0
        =
      (InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout R Y)
        R.comparisonState
        ((InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis
            (E := E) X) R.comparisonState) :=
    InfoGeometry.Canonical.ModularTwoStateCorrelation.deriv_comparisonTransportPhaseShiftedChannelCorrelation_at_zero_eq_comparisonMetricReadout
      R X Y
  have hseedEval :
      (InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis
          (E := E) X) R.comparisonState
        =
      SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator
        R.comparisonState := by
    simpa [X] using
      congrArg
        (fun A : EndH => A R.comparisonState)
        (channelPhaseAxis_liftedProjectorObstructionCorrelationSeed (E := E) SCI)
  calc
    deriv
      (fun t =>
        InfoGeometry.Canonical.ModularTwoStateCorrelation.comparisonTransportPhaseShiftedChannelCorrelation
          R
          (liftedProjectorObstructionCorrelationSeed (E := E) SCI)
          (ContinuousLinearMap.id ℝ H₂) t)
      0
      =
    (InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout R
      (ContinuousLinearMap.id ℝ H₂))
      R.comparisonState
      ((InfoGeometry.Canonical.RelationalInformationCore.channelPhaseAxis
          (E := E) (liftedProjectorObstructionCorrelationSeed (E := E) SCI))
        R.comparisonState) := by
        simpa [X, Y] using hbase
    _ =
    (InfoGeometry.Canonical.RelationalInformationCore.comparisonMetricReadout R
      (ContinuousLinearMap.id ℝ H₂))
      R.comparisonState
      (SCI.toCertifiedConformalInference.liftedProjectorObstructionOperator
        R.comparisonState) := by
        rw [hseedEval]

end InfoGeometry.Quantum
