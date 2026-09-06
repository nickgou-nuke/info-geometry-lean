import InfoGeometry.Canonical.CertifiedInverseKernel
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.MoorePenrose

/-!
# Inverse Kernel Algebra

The certified inverse kernel already packages the core Drazin/Moore-Penrose
data. This file develops the next algebraic layer built from that package:
complementary projectors, left/right mismatch operators, and the exact
identities relating these observables to the dilation gap and anomaly
commutators.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace InverseKernel

variable (IK : InverseKernel E)

/-- Complementary projector to the Drazin spectral projector. -/
abbrev spectralComplementaryProjector : E →L[ℝ] E :=
  1 - IK.spectralProjector

/-- Complementary projector to the Moore-Penrose range projector. -/
abbrev mpRangeComplementaryProjector : E →L[ℝ] E :=
  1 - IK.mpRangeProjector

/-- Complementary projector to the Moore-Penrose domain projector. -/
abbrev metricComplementaryProjector : E →L[ℝ] E :=
  1 - IK.metricProjector

/-- Spectral-versus-range mismatch operator. -/
def rightProjectorMismatch : E →L[ℝ] E :=
  IK.spectralProjector - IK.mpRangeProjector

/-- The spectral projector and its complement decompose the identity. -/
theorem spectralProjector_add_spectralComplementaryProjector :
    IK.spectralProjector + IK.spectralComplementaryProjector = (1 : E →L[ℝ] E) := by
  simp [InverseKernel.spectralComplementaryProjector]

/-- The Moore-Penrose range projector and its complement decompose the identity. -/
theorem mpRangeProjector_add_mpRangeComplementaryProjector :
    IK.mpRangeProjector + IK.mpRangeComplementaryProjector = (1 : E →L[ℝ] E) := by
  simp [InverseKernel.mpRangeComplementaryProjector]

/-- The Moore-Penrose domain projector and its complement decompose the identity. -/
theorem metricProjector_add_metricComplementaryProjector :
    IK.metricProjector + IK.metricComplementaryProjector = (1 : E →L[ℝ] E) := by
  simp [InverseKernel.metricComplementaryProjector]

/-- The Moore-Penrose range/domain difference is exactly twice the dilation gap. -/
theorem mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap :
    IK.mpRangeProjector - IK.metricProjector = (2 : ℝ) • IK.dilationGap := by
  calc
    IK.mpRangeProjector - IK.metricProjector
        = (1 : ℝ) • (IK.mpRangeProjector - IK.metricProjector) := by simp
    _ = ((2 : ℝ) * ((2 : ℝ)⁻¹)) • (IK.mpRangeProjector - IK.metricProjector) := by norm_num
    _ = (2 : ℝ) • IK.dilationGap := by
          simp [InverseKernel.dilationGap, smul_smul]

/--
The left/right mismatch difference is exactly twice the dilation gap:
`Δ_L - Δ_R = 2D`.
-/
theorem projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap :
    IK.projectorMismatch - IK.rightProjectorMismatch = (2 : ℝ) • IK.dilationGap := by
  calc
    IK.projectorMismatch - IK.rightProjectorMismatch
        = IK.mpRangeProjector - IK.metricProjector := by
            unfold InverseKernel.projectorMismatch InverseKernel.rightProjectorMismatch
            noncomm_ring
    _ = (2 : ℝ) • IK.dilationGap :=
          IK.mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap

/--
Equivalently, the right mismatch differs from the left mismatch by the negative
twice-dilation term.
-/
theorem rightProjectorMismatch_sub_projectorMismatch_eq_neg_two_smul_dilationGap :
    IK.rightProjectorMismatch - IK.projectorMismatch = -((2 : ℝ) • IK.dilationGap) := by
  calc
    IK.rightProjectorMismatch - IK.projectorMismatch
        = -(IK.projectorMismatch - IK.rightProjectorMismatch) := by
            noncomm_ring
    _ = -((2 : ℝ) • IK.dilationGap) := by
          rw [IK.projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap]

/--
The right-projector anomaly is exactly the commutator of the right mismatch
with the Moore-Penrose range projector.
-/
theorem rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange :
    IK.rightChiralAnomaly =
      IK.rightProjectorMismatch * IK.mpRangeProjector
        - IK.mpRangeProjector * IK.rightProjectorMismatch := by
  unfold InverseKernel.rightChiralAnomaly InverseKernel.rightProjectorMismatch
  noncomm_ring

end InverseKernel

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Certified complementary projector to the Drazin spectral projector. -/
abbrev spectralComplementaryProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.spectralComplementaryProjector

/-- Certified complementary projector to the Moore-Penrose range projector. -/
abbrev mpRangeComplementaryProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.mpRangeComplementaryProjector

/-- Certified complementary projector to the Moore-Penrose domain projector. -/
abbrev metricComplementaryProjector : E →L[ℝ] E :=
  CIK.toInverseKernel'.metricComplementaryProjector

/-- Certified spectral-versus-range mismatch operator. -/
abbrev rightProjectorMismatch : E →L[ℝ] E :=
  CIK.toInverseKernel'.rightProjectorMismatch

/-- Certified spectral projector decomposition of identity. -/
theorem spectralProjector_add_spectralComplementaryProjector :
    CIK.spectralProjector + CIK.spectralComplementaryProjector = (1 : E →L[ℝ] E) := by
  exact CIK.toInverseKernel'.spectralProjector_add_spectralComplementaryProjector

/-- Certified Moore-Penrose range projector decomposition of identity. -/
theorem mpRangeProjector_add_mpRangeComplementaryProjector :
    CIK.mpRangeProjector + CIK.mpRangeComplementaryProjector = (1 : E →L[ℝ] E) := by
  exact CIK.toInverseKernel'.mpRangeProjector_add_mpRangeComplementaryProjector

/-- Certified Moore-Penrose domain projector decomposition of identity. -/
theorem metricProjector_add_metricComplementaryProjector :
    CIK.metricProjector + CIK.metricComplementaryProjector = (1 : E →L[ℝ] E) := by
  exact CIK.toInverseKernel'.metricProjector_add_metricComplementaryProjector

/-- The certified complementary Drazin projector is idempotent. -/
theorem spectralComplementaryProjector_idempotent :
    CIK.spectralComplementaryProjector * CIK.spectralComplementaryProjector =
      CIK.spectralComplementaryProjector := by
  change (1 - CIK.spectralProjector) * (1 - CIK.spectralProjector) = 1 - CIK.spectralProjector
  noncomm_ring [CIK.spectralProjector_idempotent]

/-- The certified Drazin projector is left-orthogonal to its complement. -/
theorem spectralProjector_mul_spectralComplementaryProjector :
    CIK.spectralProjector * CIK.spectralComplementaryProjector = 0 := by
  change CIK.spectralProjector * (1 - CIK.spectralProjector) = 0
  noncomm_ring [CIK.spectralProjector_idempotent]

/-- The certified Drazin projector is right-orthogonal to its complement. -/
theorem spectralComplementaryProjector_mul_spectralProjector :
    CIK.spectralComplementaryProjector * CIK.spectralProjector = 0 := by
  change (1 - CIK.spectralProjector) * CIK.spectralProjector = 0
  noncomm_ring [CIK.spectralProjector_idempotent]

/-- The certified complementary Moore-Penrose range projector is idempotent. -/
theorem mpRangeComplementaryProjector_idempotent :
    CIK.mpRangeComplementaryProjector * CIK.mpRangeComplementaryProjector =
      CIK.mpRangeComplementaryProjector := by
  change (1 - CIK.mpRangeProjector) * (1 - CIK.mpRangeProjector) = 1 - CIK.mpRangeProjector
  noncomm_ring [CIK.mpRangeProjector_idempotent]

/-- The certified Moore-Penrose range projector is left-orthogonal to its complement. -/
theorem mpRangeProjector_mul_mpRangeComplementaryProjector :
    CIK.mpRangeProjector * CIK.mpRangeComplementaryProjector = 0 := by
  change CIK.mpRangeProjector * (1 - CIK.mpRangeProjector) = 0
  noncomm_ring [CIK.mpRangeProjector_idempotent]

/-- The certified Moore-Penrose range projector is right-orthogonal to its complement. -/
theorem mpRangeComplementaryProjector_mul_mpRangeProjector :
    CIK.mpRangeComplementaryProjector * CIK.mpRangeProjector = 0 := by
  change (1 - CIK.mpRangeProjector) * CIK.mpRangeProjector = 0
  noncomm_ring [CIK.mpRangeProjector_idempotent]

/-- The certified complementary Moore-Penrose domain projector is idempotent. -/
theorem metricComplementaryProjector_idempotent :
    CIK.metricComplementaryProjector * CIK.metricComplementaryProjector =
      CIK.metricComplementaryProjector := by
  change (1 - CIK.metricProjector) * (1 - CIK.metricProjector) = 1 - CIK.metricProjector
  noncomm_ring [CIK.metricProjector_idempotent]

/-- The certified Moore-Penrose domain projector is left-orthogonal to its complement. -/
theorem metricProjector_mul_metricComplementaryProjector :
    CIK.metricProjector * CIK.metricComplementaryProjector = 0 := by
  change CIK.metricProjector * (1 - CIK.metricProjector) = 0
  noncomm_ring [CIK.metricProjector_idempotent]

/-- The certified Moore-Penrose domain projector is right-orthogonal to its complement. -/
theorem metricComplementaryProjector_mul_metricProjector :
    CIK.metricComplementaryProjector * CIK.metricProjector = 0 := by
  change (1 - CIK.metricProjector) * CIK.metricProjector = 0
  noncomm_ring [CIK.metricProjector_idempotent]

/-- The certified complementary Moore-Penrose range projector is self-adjoint. -/
theorem mpRangeComplementaryProjector_star :
    star CIK.mpRangeComplementaryProjector = CIK.mpRangeComplementaryProjector := by
  change star (1 - CIK.mpRangeProjector) = 1 - CIK.mpRangeProjector
  simp [CIK.mpRangeProjector_star]

/-- The certified complementary Moore-Penrose domain projector is self-adjoint. -/
theorem metricComplementaryProjector_star :
    star CIK.metricComplementaryProjector = CIK.metricComplementaryProjector := by
  change star (1 - CIK.metricProjector) = 1 - CIK.metricProjector
  simp [CIK.metricProjector_star]

/-- Certified right-projector mismatch is the spectral-minus-range difference. -/
theorem mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap :
    CIK.mpRangeProjector - CIK.metricProjector = (2 : ℝ) • CIK.dilationGap := by
  simpa [CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.metricProjector,
    CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap

/-- Certified left/right mismatch difference is exactly twice the dilation gap. -/
theorem projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap :
    CIK.projectorMismatch - CIK.rightProjectorMismatch = (2 : ℝ) • CIK.dilationGap := by
  simpa [CertifiedInverseKernel.projectorMismatch, CertifiedInverseKernel.rightProjectorMismatch,
    CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.projectorMismatch_sub_rightProjectorMismatch_eq_two_smul_dilationGap

/-- Certified right mismatch differs from the left mismatch by the negative twice-dilation term. -/
theorem rightProjectorMismatch_sub_projectorMismatch_eq_neg_two_smul_dilationGap :
    CIK.rightProjectorMismatch - CIK.projectorMismatch = -((2 : ℝ) • CIK.dilationGap) := by
  simpa [CertifiedInverseKernel.rightProjectorMismatch, CertifiedInverseKernel.projectorMismatch,
    CertifiedInverseKernel.dilationGap, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightProjectorMismatch_sub_projectorMismatch_eq_neg_two_smul_dilationGap

/-- Certified right-projector anomaly commutator identity. -/
theorem rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange :
    CIK.rightChiralAnomaly =
      CIK.rightProjectorMismatch * CIK.mpRangeProjector
        - CIK.mpRangeProjector * CIK.rightProjectorMismatch := by
  simpa [CertifiedInverseKernel.rightChiralAnomaly, CertifiedInverseKernel.rightProjectorMismatch,
    CertifiedInverseKernel.mpRangeProjector, CertifiedInverseKernel.toInverseKernel'] using
    CIK.toInverseKernel'.rightChiralAnomaly_eq_rightProjectorMismatch_commutator_mpRange

/--
Regular-block diagonal compression of `χ = [P_D, P_L]` vanishes:
`P_D * χ * P_D = 0`.
-/
theorem spectralProjector_mul_chiralAnomaly_mul_spectralProjector_eq_zero :
    CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralProjector = 0 := by
  set P : E →L[ℝ] E := CIK.spectralProjector
  set L : E →L[ℝ] E := CIK.metricProjector
  have hP2 : P * P = P := by
    simpa [P] using CIK.spectralProjector_idempotent
  change P * (P * L - L * P) * P = 0
  calc
    P * (P * L - L * P) * P
        = (P * P) * L * P - P * L * (P * P) := by
            noncomm_ring
    _ = P * L * P - P * L * P := by
          simp [hP2, mul_assoc]
    _ = 0 := by simp

/--
Defect-block diagonal compression of `χ = [P_D, P_L]` vanishes:
`P₀ * χ * P₀ = 0`.
-/
theorem spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero :
    CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector = 0 := by
  set P : E →L[ℝ] E := CIK.spectralProjector
  set L : E →L[ℝ] E := CIK.metricProjector
  set Q : E →L[ℝ] E := 1 - P
  have hP2 : P * P = P := by
    simpa [P] using CIK.spectralProjector_idempotent
  have hQP : Q * P = 0 := by
    calc
      Q * P = (1 - P) * P := by simp [Q]
      _ = P - P * P := by noncomm_ring
      _ = 0 := by simp [hP2]
  have hPQ : P * Q = 0 := by
    calc
      P * Q = P * (1 - P) := by simp [Q]
      _ = P - P * P := by noncomm_ring
      _ = 0 := by simp [hP2]
  change Q * (P * L - L * P) * Q = 0
  calc
    Q * (P * L - L * P) * Q
        = (Q * P) * L * Q - Q * L * (P * Q) := by
            noncomm_ring
    _ = 0 := by simp [hQP, hPQ]

/--
Off-diagonal Drazin-split decomposition of the certified anomaly:
`χ = P_D χ P₀ + P₀ χ P_D`.
-/
theorem chiralAnomaly_eq_offDiagonal_spectralSplit :
    CIK.chiralAnomaly
      =
    CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector
      +
    CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralProjector := by
  have hDiagReg :
      CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralProjector = 0 :=
    CIK.spectralProjector_mul_chiralAnomaly_mul_spectralProjector_eq_zero
  have hDiagDef :
      CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector
        = 0 :=
    CIK.spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero
  calc
    CIK.chiralAnomaly
        =
      (CIK.spectralProjector + CIK.spectralComplementaryProjector)
        * CIK.chiralAnomaly
        * (CIK.spectralProjector + CIK.spectralComplementaryProjector) := by
          simp [CIK.spectralProjector_add_spectralComplementaryProjector]
    _ =
      CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralProjector
        + CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector
        + (CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralProjector
            + CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector) := by
          noncomm_ring
    _ =
      CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector
        + CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralProjector := by
          simp [hDiagReg, hDiagDef]

/--
Support profile package for `χ = [P_D, P_L]` on the Drazin split:
both diagonal compressions vanish and only off-diagonal blocks remain.
-/
theorem chiralAnomaly_spectralSupportProfile :
    CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralProjector = 0
      ∧
    CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector = 0
      ∧
    CIK.chiralAnomaly
      =
      CIK.spectralProjector * CIK.chiralAnomaly * CIK.spectralComplementaryProjector
        +
      CIK.spectralComplementaryProjector * CIK.chiralAnomaly * CIK.spectralProjector := by
  refine ⟨?_, ?_, ?_⟩
  · exact CIK.spectralProjector_mul_chiralAnomaly_mul_spectralProjector_eq_zero
  · exact CIK.spectralComplementaryProjector_mul_chiralAnomaly_mul_spectralComplementaryProjector_eq_zero
  · exact CIK.chiralAnomaly_eq_offDiagonal_spectralSplit

end CertifiedInverseKernel

end InfoGeometry.Canonical
