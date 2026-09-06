import InfoGeometry.Canonical.InverseKernelCartanCore
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

/-!
# Inverse Kernel Normal Form

This file begins the normal-form layer for the inverse-kernel spine. The first
step is the commuting-projector corridor: vanishing left/right anomaly is
exactly projector commutation, and those commuting hypotheses place the
corresponding operators in the spectral compact sector and freeze them under the
spectral grading flow.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E
noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
noncomputable local instance : NormedAlgebra ℚ EndH :=
  NormedAlgebra.restrictScalars ℚ ℝ EndH
local instance : IsTopologicalRing EndH := inferInstance
local instance : SMulCommClass ℝ EndH EndH := inferInstance
local instance : IsScalarTower ℝ EndH EndH := inferInstance

namespace InverseKernel

variable (IK : InverseKernel E)

/-- Spectral/metric commutation for the Drazin and Moore-Penrose domain projectors. -/
def SpectralMetricCommute : Prop :=
  IK.spectralProjector * IK.metricProjector = IK.metricProjector * IK.spectralProjector

/-- Spectral/range commutation for the Drazin and Moore-Penrose range projectors. -/
def SpectralRangeCommute : Prop :=
  IK.spectralProjector * IK.mpRangeProjector = IK.mpRangeProjector * IK.spectralProjector

/-- Vanishing left anomaly is exactly spectral/metric projector commutation. -/
theorem chiralAnomaly_eq_zero_iff_spectralMetricCommute :
    IK.chiralAnomaly = 0 ↔ IK.SpectralMetricCommute := by
  unfold InverseKernel.chiralAnomaly InverseKernel.SpectralMetricCommute
  exact sub_eq_zero

/-- Vanishing right anomaly is exactly spectral/range projector commutation. -/
theorem rightChiralAnomaly_eq_zero_iff_spectralRangeCommute :
    IK.rightChiralAnomaly = 0 ↔ IK.SpectralRangeCommute := by
  unfold InverseKernel.rightChiralAnomaly InverseKernel.SpectralRangeCommute
  exact sub_eq_zero

/-- Constructive forward direction for the left anomaly corridor. -/
theorem spectralMetricCommute_of_chiralAnomaly_eq_zero
    (hχ : IK.chiralAnomaly = 0) :
    IK.SpectralMetricCommute :=
  (IK.chiralAnomaly_eq_zero_iff_spectralMetricCommute).1 hχ

/-- Constructive reverse direction for the left anomaly corridor. -/
theorem chiralAnomaly_eq_zero_of_spectralMetricCommute
    (hComm : IK.SpectralMetricCommute) :
    IK.chiralAnomaly = 0 :=
  (IK.chiralAnomaly_eq_zero_iff_spectralMetricCommute).2 hComm

/-- Constructive forward direction for the right anomaly corridor. -/
theorem spectralRangeCommute_of_rightChiralAnomaly_eq_zero
    (hχ : IK.rightChiralAnomaly = 0) :
    IK.SpectralRangeCommute :=
  (IK.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute).1 hχ

/-- Constructive reverse direction for the right anomaly corridor. -/
theorem rightChiralAnomaly_eq_zero_of_spectralRangeCommute
    (hComm : IK.SpectralRangeCommute) :
    IK.rightChiralAnomaly = 0 :=
  (IK.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute).2 hComm

end InverseKernel

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Certified spectral/metric commutation condition. -/
def SpectralMetricCommute : Prop :=
  CIK.toInverseKernel'.SpectralMetricCommute

/-- Certified spectral/range commutation condition. -/
def SpectralRangeCommute : Prop :=
  CIK.toInverseKernel'.SpectralRangeCommute

/-- Certified vanishing left anomaly is exactly spectral/metric projector commutation. -/
theorem chiralAnomaly_eq_zero_iff_spectralMetricCommute :
    CIK.chiralAnomaly = 0 ↔ CIK.SpectralMetricCommute := by
  simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.chiralAnomaly_eq_zero_iff_spectralMetricCommute

/-- Certified vanishing right anomaly is exactly spectral/range projector commutation. -/
theorem rightChiralAnomaly_eq_zero_iff_spectralRangeCommute :
    CIK.rightChiralAnomaly = 0 ↔ CIK.SpectralRangeCommute := by
  simpa [CertifiedInverseKernel.SpectralRangeCommute, CertifiedInverseKernel.rightChiralAnomaly,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute

/-- Constructive forward direction for the certified left anomaly corridor. -/
theorem spectralMetricCommute_of_chiralAnomaly_eq_zero
    (hχ : CIK.chiralAnomaly = 0) :
    CIK.SpectralMetricCommute :=
  (CIK.chiralAnomaly_eq_zero_iff_spectralMetricCommute).1 hχ

/-- Constructive reverse direction for the certified left anomaly corridor. -/
theorem chiralAnomaly_eq_zero_of_spectralMetricCommute
    (hComm : CIK.SpectralMetricCommute) :
    CIK.chiralAnomaly = 0 :=
  (CIK.chiralAnomaly_eq_zero_iff_spectralMetricCommute).2 hComm

/-- Constructive forward direction for the certified right anomaly corridor. -/
theorem spectralRangeCommute_of_rightChiralAnomaly_eq_zero
    (hχ : CIK.rightChiralAnomaly = 0) :
    CIK.SpectralRangeCommute :=
  (CIK.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute).1 hχ

/-- Constructive reverse direction for the certified right anomaly corridor. -/
theorem rightChiralAnomaly_eq_zero_of_spectralRangeCommute
    (hComm : CIK.SpectralRangeCommute) :
    CIK.rightChiralAnomaly = 0 :=
  (CIK.rightChiralAnomaly_eq_zero_iff_spectralRangeCommute).2 hComm

/-- Spectral/metric commutation places the metric projector in the spectral compact sector. -/
theorem metricProjector_isSpectralCompact_of_spectralMetricCommute
    (hComm : CIK.SpectralMetricCommute) :
    CIK.IsSpectralCompact CIK.metricProjector := by
  have hComm' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  rw [CIK.isSpectralCompact_iff_commute_GammaS]
  change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
    (2 * CIK.spectralProjector - 1) * CIK.metricProjector
  noncomm_ring [hComm']

/-- Spectral/range commutation places the Moore-Penrose range projector in the spectral compact sector. -/
theorem mpRangeProjector_isSpectralCompact_of_spectralRangeCommute
    (hComm : CIK.SpectralRangeCommute) :
    CIK.IsSpectralCompact CIK.mpRangeProjector := by
  have hComm' :
      CIK.spectralProjector * CIK.mpRangeProjector =
        CIK.mpRangeProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralRangeCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  rw [CIK.isSpectralCompact_iff_commute_GammaS]
  change CIK.mpRangeProjector * (2 * CIK.spectralProjector - 1) =
    (2 * CIK.spectralProjector - 1) * CIK.mpRangeProjector
  noncomm_ring [hComm']

/-- Under spectral/metric commutation, the mismatch operator is spectral-compact. -/
theorem projectorMismatch_isSpectralCompact_of_spectralMetricCommute
    (hComm : CIK.SpectralMetricCommute) :
    CIK.IsSpectralCompact CIK.projectorMismatch := by
  have hComm' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  have hSpectralΓ :
      CIK.spectralProjector * CIK.GammaS = CIK.GammaS * CIK.spectralProjector := by
    change CIK.spectralProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.spectralProjector
    noncomm_ring [CIK.spectralProjector_idempotent]
  have hMetricΓ :
      CIK.metricProjector * CIK.GammaS = CIK.GammaS * CIK.metricProjector := by
    change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.metricProjector
    noncomm_ring [hComm']
  rw [CIK.isSpectralCompact_iff_commute_GammaS]
  change (CIK.spectralProjector - CIK.metricProjector) * CIK.GammaS =
    CIK.GammaS * (CIK.spectralProjector - CIK.metricProjector)
  simp [sub_mul, mul_sub, hSpectralΓ, hMetricΓ]

/-- If both Moore-Penrose projectors commute with the spectral projector, the dilation gap is spectral-compact. -/
theorem dilationGap_isSpectralCompact_of_spectralMoorePenroseCommute
    (hLeft : CIK.SpectralMetricCommute)
    (hRight : CIK.SpectralRangeCommute) :
    CIK.IsSpectralCompact CIK.dilationGap := by
  have hLeft' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hLeft
  have hRight' :
      CIK.spectralProjector * CIK.mpRangeProjector =
        CIK.mpRangeProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralRangeCommute, CertifiedInverseKernel.toInverseKernel'] using hRight
  have hMetricΓ :
      CIK.metricProjector * CIK.GammaS = CIK.GammaS * CIK.metricProjector := by
    change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.metricProjector
    noncomm_ring [hLeft']
  have hRangeΓ :
      CIK.mpRangeProjector * CIK.GammaS = CIK.GammaS * CIK.mpRangeProjector := by
    change CIK.mpRangeProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.mpRangeProjector
    noncomm_ring [hRight']
  rw [CIK.isSpectralCompact_iff_commute_GammaS]
  change (((2 : ℝ)⁻¹) • (CIK.mpRangeProjector - CIK.metricProjector)) * CIK.GammaS =
    CIK.GammaS * (((2 : ℝ)⁻¹) • (CIK.mpRangeProjector - CIK.metricProjector))
  simp [sub_mul, mul_sub, hRangeΓ, hMetricΓ]

/-- Spectral/metric commutation fixes the metric projector under the spectral grading flow. -/
theorem metricProjector_fixed_under_spectralGradingFlow_of_spectralMetricCommute
    (hComm : CIK.SpectralMetricCommute)
    (t : ℝ) :
    CIK.spectralAdjointFlow CIK.GammaS t CIK.metricProjector = CIK.metricProjector := by
  have hComm' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  simpa [CertifiedInverseKernel.spectralAdjointFlow, CertifiedInverseKernel.GammaS,
    CertifiedInverseKernel.cartanTriple, CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.metricProjector_fixed_under_spectralGradingFlow_of_projector_commute hComm' t

/-- Spectral/range commutation fixes the range projector under the spectral grading flow. -/
theorem mpRangeProjector_fixed_under_spectralGradingFlow_of_spectralRangeCommute
    (hComm : CIK.SpectralRangeCommute)
    (t : ℝ) :
    CIK.spectralAdjointFlow CIK.GammaS t CIK.mpRangeProjector = CIK.mpRangeProjector := by
  have hComm' :
      CIK.spectralProjector * CIK.mpRangeProjector =
        CIK.mpRangeProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralRangeCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  simpa [CertifiedInverseKernel.spectralAdjointFlow, CertifiedInverseKernel.GammaS,
    CertifiedInverseKernel.cartanTriple, CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.mpRangeProjector_fixed_under_spectralGradingFlow_of_rightProjector_commute hComm' t

/-- Spectral/metric commutation fixes the mismatch operator under the spectral grading flow. -/
theorem projectorMismatch_fixed_under_spectralGradingFlow_of_spectralMetricCommute
    (hComm : CIK.SpectralMetricCommute)
    (t : ℝ) :
    CIK.spectralAdjointFlow CIK.GammaS t CIK.projectorMismatch = CIK.projectorMismatch := by
  have hComm' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hComm
  simpa [CertifiedInverseKernel.spectralAdjointFlow, CertifiedInverseKernel.GammaS,
    CertifiedInverseKernel.cartanTriple, CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.projectorMismatch_fixed_under_spectralGradingFlow_of_projector_commute hComm' t

/-- If both Moore-Penrose projectors commute with the spectral projector, the dilation gap is fixed by the spectral grading flow. -/
theorem dilationGap_fixed_under_spectralGradingFlow_of_spectralMoorePenroseCommute
    (hLeft : CIK.SpectralMetricCommute)
    (hRight : CIK.SpectralRangeCommute)
    (t : ℝ) :
    CIK.spectralAdjointFlow CIK.GammaS t CIK.dilationGap = CIK.dilationGap := by
  have hLeft' :
      CIK.spectralProjector * CIK.metricProjector =
        CIK.metricProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralMetricCommute, CertifiedInverseKernel.toInverseKernel'] using hLeft
  have hRight' :
      CIK.spectralProjector * CIK.mpRangeProjector =
        CIK.mpRangeProjector * CIK.spectralProjector := by
    simpa [CertifiedInverseKernel.SpectralRangeCommute, CertifiedInverseKernel.toInverseKernel'] using hRight
  simpa [CertifiedInverseKernel.spectralAdjointFlow, CertifiedInverseKernel.GammaS,
    CertifiedInverseKernel.cartanTriple, CertifiedInverseKernel.toInformationCartanTriple] using
    CIK.dilationGap_fixed_under_spectralGradingFlow_of_projector_commute hLeft' hRight' t

end CertifiedInverseKernel

end InfoGeometry.Canonical
