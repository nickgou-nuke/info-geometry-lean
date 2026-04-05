import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.CartanDecomposition
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.SpineAttributes
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Canonical.CartanDecomposition

/-!
# Certified Inverse Kernel

Canonical proof-carrying center for operator packages that carry both a Drazin
and a Moore-Penrose regularization. Downstream surfaces such as conformal,
spectral, and modular theories should adapt to this kernel rather than re-bundle
the same inverse data ad hoc.
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

/-- Witness-level inverse kernel with chosen Drazin and Moore-Penrose data. -/
structure InverseKernel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  A : E →L[ℝ] E
  A_D : E →L[ℝ] E
  A_MP : E →L[ℝ] E

/--
Proof-carrying certified inverse kernel. This is the canonical center bundle for
inverse/projector/anomaly data.
-/
structure CertifiedInverseKernel (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] extends InverseKernel E where
  drazinIndex : ℕ
  hDrazin : IsDrazinInverse A A_D drazinIndex
  hMoorePenrose : IsMoorePenroseInverse A A_MP

attribute [spine_object] CertifiedInverseKernel

namespace InverseKernel

variable (IK : InverseKernel E)

/-- The Drazin spectral projector attached to the kernel. -/
abbrev spectralProjector : E →L[ℝ] E :=
  IsDrazinInverse.projection IK.A IK.A_D

/-- The Moore-Penrose range projector attached to the kernel. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  IsMoorePenroseInverse.rightProjector IK.A IK.A_MP

/-- The Moore-Penrose domain projector attached to the kernel. -/
abbrev metricProjector : E →L[ℝ] E :=
  IsMoorePenroseInverse.leftProjector IK.A IK.A_MP

/-- Spectral-metric projector mismatch. -/
def projectorMismatch : E →L[ℝ] E :=
  IK.spectralProjector - IK.metricProjector

/-- Left-projector anomaly commutator. -/
def chiralAnomaly : E →L[ℝ] E :=
  IK.spectralProjector * IK.metricProjector - IK.metricProjector * IK.spectralProjector

/-- Right-projector anomaly commutator. -/
def rightChiralAnomaly : E →L[ℝ] E :=
  IK.spectralProjector * IK.mpRangeProjector - IK.mpRangeProjector * IK.spectralProjector

/-- Half-difference between the Moore-Penrose range and domain projectors. -/
noncomputable def dilationGap : E →L[ℝ] E :=
  ((2 : ℝ)⁻¹) • (IK.mpRangeProjector - IK.metricProjector)

/-- Norm of the certified left-projector anomaly commutator. -/
noncomputable def chiralScale : ℝ :=
  nnnorm IK.chiralAnomaly

/-- The mismatch commutator with the metric projector is exactly the left anomaly. -/
theorem chiralAnomaly_eq_mismatch_commutator_metric :
    IK.chiralAnomaly =
      IK.projectorMismatch * IK.metricProjector
        - IK.metricProjector * IK.projectorMismatch := by
  simpa [InverseKernel.chiralAnomaly, InverseKernel.projectorMismatch,
    InverseKernel.spectralProjector, InverseKernel.metricProjector] using
    InfoGeometry.Canonical.MoorePenrose.chiralAnomaly_eq_mismatch_commutator_metric
      IK.A IK.A_D IK.A_MP

/-- Vanishing mismatch is equivalent to agreement of the spectral and metric projectors. -/
theorem projectorMismatch_eq_zero_iff :
    IK.projectorMismatch = 0 ↔ IK.spectralProjector = IK.metricProjector := by
  simpa [InverseKernel.projectorMismatch, InverseKernel.spectralProjector,
    InverseKernel.metricProjector] using
    (InfoGeometry.Canonical.MoorePenrose.projectorMismatch_eq_zero_iff
      (a := IK.A) (a_d := IK.A_D) (a_mp := IK.A_MP))

/-- Vanishing anomaly scale is equivalent to vanishing left-projector anomaly. -/
theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero :
    IK.chiralScale = 0 ↔ IK.chiralAnomaly = 0 := by
  simp [InverseKernel.chiralScale, InverseKernel.chiralAnomaly]

/-- If the Moore-Penrose range and domain projectors agree, the two anomaly conventions agree. -/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement
    (hProj : IK.mpRangeProjector = IK.metricProjector) :
    IK.rightChiralAnomaly = IK.chiralAnomaly := by
  simp [InverseKernel.rightChiralAnomaly, InverseKernel.chiralAnomaly, hProj]

/-- The spectral/dilation commutator is half the difference of right and left anomalies. -/
theorem spectralProjector_commutator_dilationGap_eq_half_sub_anomalies :
    IK.spectralProjector * IK.dilationGap - IK.dilationGap * IK.spectralProjector =
      ((2 : ℝ)⁻¹) • (IK.rightChiralAnomaly - IK.chiralAnomaly) := by
  unfold InverseKernel.dilationGap InverseKernel.rightChiralAnomaly
  unfold InverseKernel.chiralAnomaly InverseKernel.spectralProjector
  unfold InverseKernel.mpRangeProjector InverseKernel.metricProjector
  simp [sub_eq_add_neg]
  noncomm_ring

/-- Right-projector commutation reduces the spectral/dilation commutator to the left anomaly. -/
theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute
    (hRight : IK.spectralProjector * IK.mpRangeProjector = IK.mpRangeProjector * IK.spectralProjector) :
    IK.spectralProjector * IK.dilationGap - IK.dilationGap * IK.spectralProjector =
      -((2 : ℝ)⁻¹) • IK.chiralAnomaly := by
  rw [IK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies]
  have hRightZero : IK.rightChiralAnomaly = 0 := by
    simp [InverseKernel.rightChiralAnomaly, hRight]
  simp [hRightZero, sub_eq_add_neg]

/-- Right-projector commutation plus vanishing anomaly scale kills the spectral/dilation commutator. -/
theorem spectralProjector_commutator_dilationGap_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
    (hRight : IK.spectralProjector * IK.mpRangeProjector = IK.mpRangeProjector * IK.spectralProjector)
    (hScale : IK.chiralScale = 0) :
    IK.spectralProjector * IK.dilationGap - IK.dilationGap * IK.spectralProjector = 0 := by
  rw [IK.spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute hRight]
  have hχ : IK.chiralAnomaly = 0 :=
    (IK.chiralScale_eq_zero_iff_chiralAnomaly_eq_zero).mp hScale
  simp [hχ]

end InverseKernel

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Canonical Cartan triple attached to the certified inverse kernel. -/
noncomputable def toInformationCartanTriple :
    CartanDecomposition.InformationCartanTriple (E →L[ℝ] E) where
  A := CIK.A
  A_D := CIK.A_D
  A_MP := CIK.A_MP

/-- Forgetful map from the certified kernel to the witness-level kernel. -/
abbrev toInverseKernel' : InverseKernel E :=
  CIK.toInverseKernel

/-- Certified Drazin spectral projector. -/
abbrev spectralProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.spectralProjector

/-- Certified Moore-Penrose range projector. -/
abbrev mpRangeProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.mpRangeProjector

/-- Certified Moore-Penrose domain projector. -/
abbrev metricProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.metricProjector

/-- Certified projector mismatch. -/
abbrev projectorMismatch : E →L[ℝ] E :=
  CIK.toInverseKernel'.projectorMismatch

/-- Certified left-projector anomaly commutator. -/
abbrev chiralAnomaly : E →L[ℝ] E :=
  CIK.toInverseKernel'.chiralAnomaly

/-- Certified right-projector anomaly commutator. -/
abbrev rightChiralAnomaly : E →L[ℝ] E :=
  CIK.toInverseKernel'.rightChiralAnomaly

/-- Certified half-difference between Moore-Penrose projectors. -/
noncomputable abbrev dilationGap : E →L[ℝ] E :=
  CIK.toInverseKernel'.dilationGap

/-- Certified anomaly scale. -/
noncomputable abbrev chiralScale : ℝ :=
  CIK.toInverseKernel'.chiralScale

/-- The certified Drazin projector is idempotent. -/
theorem spectralProjector_idempotent :
    CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector := by
  simpa [CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.spectralProjector] using
    IsDrazinInverse.projection_is_idempotent CIK.hDrazin

/-- The certified Moore-Penrose range projector is idempotent. -/
theorem mpRangeProjector_idempotent :
    CIK.mpRangeProjector * CIK.mpRangeProjector = CIK.mpRangeProjector := by
  simpa [CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.mpRangeProjector] using
    IsMoorePenroseInverse.rightProjector_idempotent CIK.hMoorePenrose

/-- The certified Moore-Penrose domain projector is idempotent. -/
theorem metricProjector_idempotent :
    CIK.metricProjector * CIK.metricProjector = CIK.metricProjector := by
  simpa [CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
    IsMoorePenroseInverse.leftProjector_idempotent CIK.hMoorePenrose

/-- The certified Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeProjector_star :
    star CIK.mpRangeProjector = CIK.mpRangeProjector := by
  simpa [CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.mpRangeProjector] using
    IsMoorePenroseInverse.rightProjector_star CIK.hMoorePenrose

/-- The certified Moore-Penrose domain projector is self-adjoint. -/
theorem metricProjector_star :
    star CIK.metricProjector = CIK.metricProjector := by
  simpa [CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel',
    InverseKernel.metricProjector] using
    IsMoorePenroseInverse.leftProjector_star CIK.hMoorePenrose

/-- Certified mismatch commutator identity. -/
theorem chiralAnomaly_eq_mismatch_commutator_metric :
    CIK.chiralAnomaly =
      CIK.projectorMismatch * CIK.metricProjector
        - CIK.metricProjector * CIK.projectorMismatch := by
  simpa [CertifiedInverseKernel.chiralAnomaly, CertifiedInverseKernel.projectorMismatch,
    CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.chiralAnomaly_eq_mismatch_commutator_metric

/-- Certified vanishing mismatch iff spectral and metric projectors agree. -/
theorem projectorMismatch_eq_zero_iff :
    CIK.projectorMismatch = 0 ↔ CIK.spectralProjector = CIK.metricProjector := by
  simpa [CertifiedInverseKernel.projectorMismatch, CertifiedInverseKernel.spectralProjector,
    CertifiedInverseKernel.metricProjector, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.projectorMismatch_eq_zero_iff

/-- Certified vanishing anomaly scale iff the certified anomaly operator vanishes. -/
theorem chiralScale_eq_zero_iff_chiralAnomaly_eq_zero :
    CIK.chiralScale = 0 ↔ CIK.chiralAnomaly = 0 := by
  simpa [CertifiedInverseKernel.chiralScale, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.chiralScale_eq_zero_iff_chiralAnomaly_eq_zero

/-- Certified range/domain projector agreement identifies the two anomaly conventions. -/
theorem rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement
    (hProj : CIK.mpRangeProjector = CIK.metricProjector) :
    CIK.rightChiralAnomaly = CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.rightChiralAnomaly, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.metricProjector,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_chiralAnomaly_of_projectorAgreement hProj

/-- Certified spectral/dilation commutator decomposition. -/
theorem spectralProjector_commutator_dilationGap_eq_half_sub_anomalies :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector =
      ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly) := by
  simpa [CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.rightChiralAnomaly, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies

/-- Certified right-projector commutation reduction of the spectral/dilation commutator. -/
theorem spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute
    (hRight : CIK.spectralProjector * CIK.mpRangeProjector = CIK.mpRangeProjector * CIK.spectralProjector) :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector =
      -((2 : ℝ)⁻¹) • CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.chiralAnomaly,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute hRight

/-- Certified vanishing anomaly scale kills the spectral/dilation commutator under right-projector commutation. -/
theorem spectralProjector_commutator_dilationGap_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
    (hRight : CIK.spectralProjector * CIK.mpRangeProjector = CIK.mpRangeProjector * CIK.spectralProjector)
    (hScale : CIK.chiralScale = 0) :
    CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector = 0 := by
  simpa [CertifiedInverseKernel.spectralProjector, CertifiedInverseKernel.dilationGap,
    CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.chiralScale,
    CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.spectralProjector_commutator_dilationGap_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero hRight hScale

/-- If the metric projector commutes with the spectral projector, it is fixed by the spectral grading flow. -/
theorem metricProjector_fixed_under_spectralGradingFlow_of_projector_commute
    (hMetric : CIK.spectralProjector * CIK.metricProjector = CIK.metricProjector * CIK.spectralProjector)
    (t : ℝ) :
    (CIK.toInformationCartanTriple).spectralAdjointFlow
        (CIK.toInformationCartanTriple).GammaS t CIK.metricProjector
      =
    CIK.metricProjector := by
  let T := CIK.toInformationCartanTriple
  have hMetricΓ : Commute CIK.metricProjector T.GammaS := by
    change CIK.metricProjector * T.GammaS = T.GammaS * CIK.metricProjector
    change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.metricProjector
    noncomm_ring [hMetric]
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_self_of_commute_GammaS T hMetricΓ t

/-- If the Moore-Penrose range projector commutes with the spectral projector, it is fixed by the spectral grading flow. -/
theorem mpRangeProjector_fixed_under_spectralGradingFlow_of_rightProjector_commute
    (hRight : CIK.spectralProjector * CIK.mpRangeProjector = CIK.mpRangeProjector * CIK.spectralProjector)
    (t : ℝ) :
    (CIK.toInformationCartanTriple).spectralAdjointFlow
        (CIK.toInformationCartanTriple).GammaS t CIK.mpRangeProjector
      =
    CIK.mpRangeProjector := by
  let T := CIK.toInformationCartanTriple
  have hRangeΓ : Commute CIK.mpRangeProjector T.GammaS := by
    change CIK.mpRangeProjector * T.GammaS = T.GammaS * CIK.mpRangeProjector
    change CIK.mpRangeProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.mpRangeProjector
    noncomm_ring [hRight]
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_self_of_commute_GammaS T hRangeΓ t

/-- If the metric projector commutes with the spectral projector, the mismatch operator is fixed by the spectral grading flow. -/
theorem projectorMismatch_fixed_under_spectralGradingFlow_of_projector_commute
    (hMetric : CIK.spectralProjector * CIK.metricProjector = CIK.metricProjector * CIK.spectralProjector)
    (t : ℝ) :
    (CIK.toInformationCartanTriple).spectralAdjointFlow
        (CIK.toInformationCartanTriple).GammaS t CIK.projectorMismatch
      =
    CIK.projectorMismatch := by
  let T := CIK.toInformationCartanTriple
  have hSpectralΓ : Commute CIK.spectralProjector T.GammaS := by
    have hP2 : CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector :=
      CIK.spectralProjector_idempotent
    have hLeft :
        CIK.spectralProjector * (2 * CIK.spectralProjector) = 2 * CIK.spectralProjector := by
      calc
        CIK.spectralProjector * (2 * CIK.spectralProjector)
            = 2 * (CIK.spectralProjector * CIK.spectralProjector) := by
                noncomm_ring
        _ = 2 * CIK.spectralProjector := by rw [hP2]
    have hRight :
        (2 * CIK.spectralProjector) * CIK.spectralProjector = 2 * CIK.spectralProjector := by
      calc
        (2 * CIK.spectralProjector) * CIK.spectralProjector
            = 2 * (CIK.spectralProjector * CIK.spectralProjector) := by
                noncomm_ring
        _ = 2 * CIK.spectralProjector := by rw [hP2]
    change CIK.spectralProjector * T.GammaS = T.GammaS * CIK.spectralProjector
    rw [show T.GammaS = 2 * CIK.spectralProjector - 1 by
          rfl, mul_sub, sub_mul]
    simp [hLeft, hRight]
  have hMismatchΓ : Commute CIK.projectorMismatch T.GammaS := by
    have hMetricΓ : Commute CIK.metricProjector T.GammaS := by
      change CIK.metricProjector * T.GammaS = T.GammaS * CIK.metricProjector
      change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
        (2 * CIK.spectralProjector - 1) * CIK.metricProjector
      noncomm_ring [hMetric]
    change CIK.projectorMismatch * T.GammaS = T.GammaS * CIK.projectorMismatch
    simp [CertifiedInverseKernel.projectorMismatch, CertifiedInverseKernel.toInverseKernel',
      InverseKernel.projectorMismatch, sub_mul, mul_sub, hSpectralΓ.eq, hMetricΓ.eq]
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_self_of_commute_GammaS T hMismatchΓ t

/-- If both Moore-Penrose projectors commute with the spectral projector, the dilation gap is fixed by the spectral grading flow. -/
theorem dilationGap_fixed_under_spectralGradingFlow_of_projector_commute
    (hLeft : CIK.spectralProjector * CIK.metricProjector = CIK.metricProjector * CIK.spectralProjector)
    (hRight : CIK.spectralProjector * CIK.mpRangeProjector = CIK.mpRangeProjector * CIK.spectralProjector)
    (t : ℝ) :
    (CIK.toInformationCartanTriple).spectralAdjointFlow
        (CIK.toInformationCartanTriple).GammaS t CIK.dilationGap
      =
    CIK.dilationGap := by
  let T := CIK.toInformationCartanTriple
  have hMetricΓ : Commute CIK.metricProjector T.GammaS := by
    change CIK.metricProjector * T.GammaS = T.GammaS * CIK.metricProjector
    change CIK.metricProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.metricProjector
    noncomm_ring [hLeft]
  have hRangeΓ : Commute CIK.mpRangeProjector T.GammaS := by
    change CIK.mpRangeProjector * T.GammaS = T.GammaS * CIK.mpRangeProjector
    change CIK.mpRangeProjector * (2 * CIK.spectralProjector - 1) =
      (2 * CIK.spectralProjector - 1) * CIK.mpRangeProjector
    noncomm_ring [hRight]
  have hGapΓ : Commute CIK.dilationGap T.GammaS := by
    have hDiffΓ : Commute (CIK.mpRangeProjector - CIK.metricProjector) T.GammaS := by
      change (CIK.mpRangeProjector - CIK.metricProjector) * T.GammaS =
        T.GammaS * (CIK.mpRangeProjector - CIK.metricProjector)
      simp [sub_mul, mul_sub, hRangeΓ.eq, hMetricΓ.eq]
    simpa [CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel',
      InverseKernel.dilationGap] using ((hDiffΓ.smul_left ((2 : ℝ)⁻¹)).eq)
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_self_of_commute_GammaS T hGapΓ t

/-- The left anomaly operator anticommutes with the spectral grading. -/
theorem chiralAnomaly_anticommutes_GammaS :
    let T := CIK.toInformationCartanTriple
    CIK.chiralAnomaly * T.GammaS = -(T.GammaS * CIK.chiralAnomaly) := by
  let T := CIK.toInformationCartanTriple
  have hP2 : CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector :=
    CIK.spectralProjector_idempotent
  have hPPL :
      CIK.spectralProjector * (CIK.spectralProjector * CIK.metricProjector)
        =
      CIK.spectralProjector * CIK.metricProjector := by
    simpa [mul_assoc] using congrArg (fun Z : EndH => Z * CIK.metricProjector) hP2
  change CIK.chiralAnomaly * T.GammaS = -(T.GammaS * CIK.chiralAnomaly)
  change
    (CIK.spectralProjector * CIK.metricProjector - CIK.metricProjector * CIK.spectralProjector) *
        (2 * CIK.spectralProjector - 1)
      =
    -((2 * CIK.spectralProjector - 1) *
        (CIK.spectralProjector * CIK.metricProjector - CIK.metricProjector * CIK.spectralProjector))
  noncomm_ring [hP2, hPPL]

/-- The right anomaly operator anticommutes with the spectral grading. -/
theorem rightChiralAnomaly_anticommutes_GammaS :
    let T := CIK.toInformationCartanTriple
    CIK.rightChiralAnomaly * T.GammaS = -(T.GammaS * CIK.rightChiralAnomaly) := by
  let T := CIK.toInformationCartanTriple
  have hP2 : CIK.spectralProjector * CIK.spectralProjector = CIK.spectralProjector :=
    CIK.spectralProjector_idempotent
  have hPPR :
      CIK.spectralProjector * (CIK.spectralProjector * CIK.mpRangeProjector)
        =
      CIK.spectralProjector * CIK.mpRangeProjector := by
    simpa [mul_assoc] using congrArg (fun Z : EndH => Z * CIK.mpRangeProjector) hP2
  change CIK.rightChiralAnomaly * T.GammaS = -(T.GammaS * CIK.rightChiralAnomaly)
  change
    (CIK.spectralProjector * CIK.mpRangeProjector - CIK.mpRangeProjector * CIK.spectralProjector) *
        (2 * CIK.spectralProjector - 1)
      =
    -((2 * CIK.spectralProjector - 1) *
        (CIK.spectralProjector * CIK.mpRangeProjector - CIK.mpRangeProjector * CIK.spectralProjector))
  noncomm_ring [hP2, hPPR]

/-- The left anomaly lies in the spectral noncompact sector. -/
theorem chiralAnomaly_isSpectralNonCompact :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact CIK.chiralAnomaly := by
  let T := CIK.toInformationCartanTriple
  rw [CartanDecomposition.InformationCartanTriple.isSpectralNonCompact_iff_anticommute T CIK.hDrazin]
  simpa [T] using CIK.chiralAnomaly_anticommutes_GammaS

/-- The right anomaly lies in the spectral noncompact sector. -/
theorem rightChiralAnomaly_isSpectralNonCompact :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact CIK.rightChiralAnomaly := by
  let T := CIK.toInformationCartanTriple
  rw [CartanDecomposition.InformationCartanTriple.isSpectralNonCompact_iff_anticommute T CIK.hDrazin]
  simpa [T] using CIK.rightChiralAnomaly_anticommutes_GammaS

/-- The grading adjoint flow preserves the spectral noncompactness of the left anomaly sector. -/
theorem chiralAnomaly_spectralAdjointFlow_mem_noncompact
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact (T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly) := by
  let T := CIK.toInformationCartanTriple
  have hΓ :
      T.IsSpectralCompact T.GammaS :=
    CartanDecomposition.InformationCartanTriple.GammaS_isSpectralCompact T CIK.hDrazin
  have hχ :
      T.IsSpectralNonCompact CIK.chiralAnomaly := by
    simpa [T] using CIK.chiralAnomaly_isSpectralNonCompact
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_mem_noncompact
      T CIK.hDrazin (X := T.GammaS) (Y := CIK.chiralAnomaly) hΓ hχ t

/-- The grading adjoint flow preserves the spectral noncompactness of the right anomaly sector. -/
theorem rightChiralAnomaly_spectralAdjointFlow_mem_noncompact
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.IsSpectralNonCompact (T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly) := by
  let T := CIK.toInformationCartanTriple
  have hΓ :
      T.IsSpectralCompact T.GammaS :=
    CartanDecomposition.InformationCartanTriple.GammaS_isSpectralCompact T CIK.hDrazin
  have hχ :
      T.IsSpectralNonCompact CIK.rightChiralAnomaly := by
    simpa [T] using CIK.rightChiralAnomaly_isSpectralNonCompact
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_mem_noncompact
      T CIK.hDrazin (X := T.GammaS) (Y := CIK.rightChiralAnomaly) hΓ hχ t

/--
The spectral grading adjoint flow transports the left anomaly by the doubled
negative-time grading flow.
-/
theorem chiralAnomaly_spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly =
      CIK.chiralAnomaly * T.spectralGradingFlow (-(2 * t)) := by
  let T := CIK.toInformationCartanTriple
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two_of_anticommute_GammaS
      T CIK.hDrazin (Y := CIK.chiralAnomaly) CIK.chiralAnomaly_anticommutes_GammaS t

/--
The spectral grading adjoint flow transports the right anomaly by the doubled
negative-time grading flow.
-/
theorem rightChiralAnomaly_spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly =
      CIK.rightChiralAnomaly * T.spectralGradingFlow (-(2 * t)) := by
  let T := CIK.toInformationCartanTriple
  simpa [T] using
    CartanDecomposition.InformationCartanTriple.spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two_of_anticommute_GammaS
      T CIK.hDrazin (Y := CIK.rightChiralAnomaly) CIK.rightChiralAnomaly_anticommutes_GammaS t

/--
The spectral/dilation commutator transported by the grading flow is exactly half
the difference of the transported right and left anomalies.
-/
theorem spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_half_sub_anomaly_flows
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    CIK.spectralProjector * T.spectralAdjointFlow T.GammaS t CIK.dilationGap
      - T.spectralAdjointFlow T.GammaS t CIK.dilationGap * CIK.spectralProjector
      =
    ((2 : ℝ)⁻¹) •
      (T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly
        - T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly) := by
  let T := CIK.toInformationCartanTriple
  let e : EndH := T.spectralGradingFlow t
  let f : EndH := T.spectralGradingFlow (-t)
  have hPe : Commute CIK.spectralProjector e := by
    simpa [T, e] using
      CartanDecomposition.InformationCartanTriple.spectralProjector_commutes_spectralGradingFlow
        T CIK.hDrazin t
  have hPf : Commute CIK.spectralProjector f := by
    simpa [T, f] using
      CartanDecomposition.InformationCartanTriple.spectralProjector_commutes_spectralGradingFlow
        T CIK.hDrazin (-t)
  have hCommTransport :
      CIK.spectralProjector * T.spectralAdjointFlow T.GammaS t CIK.dilationGap
        - T.spectralAdjointFlow T.GammaS t CIK.dilationGap * CIK.spectralProjector
        =
      T.spectralAdjointFlow T.GammaS t
        (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) := by
    unfold CartanDecomposition.InformationCartanTriple.spectralAdjointFlow
    calc
      CIK.spectralProjector * (T.spectralGradingFlow t * CIK.dilationGap * T.spectralGradingFlow (-t))
          - (T.spectralGradingFlow t * CIK.dilationGap * T.spectralGradingFlow (-t))
              * CIK.spectralProjector
          =
        (CIK.spectralProjector * T.spectralGradingFlow t) * CIK.dilationGap * T.spectralGradingFlow (-t)
          - T.spectralGradingFlow t * CIK.dilationGap *
              (T.spectralGradingFlow (-t) * CIK.spectralProjector) := by
            simp [mul_assoc]
      _ =
        (T.spectralGradingFlow t * CIK.spectralProjector) * CIK.dilationGap * T.spectralGradingFlow (-t)
          - T.spectralGradingFlow t * CIK.dilationGap *
              (CIK.spectralProjector * T.spectralGradingFlow (-t)) := by
            rw [hPe.eq, hPf.eq]
      _ =
        T.spectralGradingFlow t * CIK.spectralProjector * CIK.dilationGap * T.spectralGradingFlow (-t)
          - T.spectralGradingFlow t * CIK.dilationGap * CIK.spectralProjector * T.spectralGradingFlow (-t) := by
            simp [mul_assoc]
      _ =
        T.spectralGradingFlow t *
          (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) *
            T.spectralGradingFlow (-t) := by
              noncomm_ring
      _ =
        T.spectralAdjointFlow T.GammaS t
          (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) := by
            rfl
  have hLinear :
      T.spectralAdjointFlow T.GammaS t (((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly))
        =
      ((2 : ℝ)⁻¹) •
        (T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly
          - T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly) := by
    unfold CartanDecomposition.InformationCartanTriple.spectralAdjointFlow
    simp [sub_eq_add_neg, add_mul, mul_add, mul_assoc]
  calc
    CIK.spectralProjector * T.spectralAdjointFlow T.GammaS t CIK.dilationGap
        - T.spectralAdjointFlow T.GammaS t CIK.dilationGap * CIK.spectralProjector
      =
    T.spectralAdjointFlow T.GammaS t
      (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) := hCommTransport
    _ =
    T.spectralAdjointFlow T.GammaS t
      (((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly)) := by
        rw [CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies]
    _ =
    ((2 : ℝ)⁻¹) •
      (T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly
        - T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly) := hLinear

/--
The spectral/dilation commutator closes under the grading adjoint flow as a
single odd transport mode.
-/
theorem spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_mul_spectralGradingFlow_neg_two
    (t : ℝ) :
    let T := CIK.toInformationCartanTriple
    CIK.spectralProjector * T.spectralAdjointFlow T.GammaS t CIK.dilationGap
      - T.spectralAdjointFlow T.GammaS t CIK.dilationGap * CIK.spectralProjector
      =
    (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) *
      T.spectralGradingFlow (-(2 * t)) := by
  let T := CIK.toInformationCartanTriple
  calc
    CIK.spectralProjector * T.spectralAdjointFlow T.GammaS t CIK.dilationGap
        - T.spectralAdjointFlow T.GammaS t CIK.dilationGap * CIK.spectralProjector
      =
    ((2 : ℝ)⁻¹) •
      (T.spectralAdjointFlow T.GammaS t CIK.rightChiralAnomaly
        - T.spectralAdjointFlow T.GammaS t CIK.chiralAnomaly) := by
          simpa [T] using
            CIK.spectralProjector_commutator_spectralAdjointFlow_dilationGap_eq_half_sub_anomaly_flows t
    _ =
    ((2 : ℝ)⁻¹) •
      ((CIK.rightChiralAnomaly - CIK.chiralAnomaly) * T.spectralGradingFlow (-(2 * t))) := by
          rw [CIK.rightChiralAnomaly_spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two,
            CIK.chiralAnomaly_spectralAdjointFlow_eq_mul_spectralGradingFlow_neg_two]
          simp [sub_eq_add_neg, add_mul, T]
    _ =
    (CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector) *
      T.spectralGradingFlow (-(2 * t)) := by
          have hBase :
              CIK.spectralProjector * CIK.dilationGap - CIK.dilationGap * CIK.spectralProjector
                =
              ((2 : ℝ)⁻¹) • (CIK.rightChiralAnomaly - CIK.chiralAnomaly) :=
            CIK.spectralProjector_commutator_dilationGap_eq_half_sub_anomalies
          simpa [smul_mul_assoc] using
            (congrArg (fun Z : EndH => Z * T.spectralGradingFlow (-(2 * t))) hBase).symm

end CertifiedInverseKernel

end InfoGeometry.Canonical
