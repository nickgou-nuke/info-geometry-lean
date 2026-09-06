import InfoGeometry.Canonical.DrazinCoreFlow
import InfoGeometry.Canonical.EPAndGroupInverse
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.EPDefectAlgebra

Operator-side defect algebra for the property inverse-kernel package.

This file packages the exact repo-native objects:

- Moore-Penrose left/right projectors,
- their difference `mpChiralGap`,
- the raw commutator `A*A_MP - A_MP*A`,
- equivalence of vanishing gap with the EP corridor,
- the existing spectral-projector/dilation/chiral-anomaly bridge.
-/

namespace InfoGeometry.Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace CertifiedInverseKernel

variable (CIK : CertifiedInverseKernel E)

/-- Moore-Penrose left projector. -/
@[rep_depth operator]
abbrev mpLeftProj : E →L[ℝ] E :=
  CIK.metricProjector

/-- Moore-Penrose right projector. -/
@[rep_depth operator]
abbrev mpRightProj : E →L[ℝ] E :=
  CIK.mpRangeProjector

/-- Left/right Moore-Penrose projector mismatch. -/
@[rep_depth operator]
def mpChiralGap : E →L[ℝ] E :=
  CIK.mpRightProj - CIK.mpLeftProj

/-- Raw Moore-Penrose inverse commutator. -/
@[rep_depth operator]
def mpInverseCommutator : E →L[ℝ] E :=
  CIK.A * CIK.A_MP - CIK.A_MP * CIK.A

@[rep_depth operator, simp] theorem mpLeftProj_idempotent :
    CIK.mpLeftProj * CIK.mpLeftProj = CIK.mpLeftProj :=
  CIK.metricProjector_idempotent

@[rep_depth operator, simp] theorem mpRightProj_idempotent :
    CIK.mpRightProj * CIK.mpRightProj = CIK.mpRightProj :=
  CIK.mpRangeProjector_idempotent

@[rep_depth operator, simp] theorem drazinCoreProj_idempotent :
    CIK.drazinCoreProj * CIK.drazinCoreProj = CIK.drazinCoreProj :=
  CIK.spectralProjector_idempotent

@[rep_depth operator, simp] theorem mpInverseCommutator_eq_mpChiralGap :
    CIK.mpInverseCommutator = CIK.mpChiralGap := by
  rfl

@[rep_depth operator] theorem mpChiralGap_eq_two_smul_dilationGap :
    CIK.mpChiralGap = (2 : ℝ) • CIK.dilationGap := by
  simpa [CertifiedInverseKernel.mpChiralGap, CertifiedInverseKernel.mpRightProj,
    CertifiedInverseKernel.mpLeftProj] using
    CIK.mpRangeProjector_sub_metricProjector_eq_two_smul_dilationGap

@[rep_depth operator, simp] theorem dilationGap_eq_half_smul_mpChiralGap :
    CIK.dilationGap = ((2 : ℝ)⁻¹) • CIK.mpChiralGap := by
  rfl

@[rep_depth operator, simp] theorem dilationGap_eq_half_smul_mpInverseCommutator :
    CIK.dilationGap = ((2 : ℝ)⁻¹) • CIK.mpInverseCommutator := by
  rw [CIK.mpInverseCommutator_eq_mpChiralGap]
  exact CIK.dilationGap_eq_half_smul_mpChiralGap

@[rep_depth operator] theorem mpChiralGap_eq_zero_iff_isEP :
    CIK.mpChiralGap = 0 ↔ CIK.IsEP := by
  constructor
  · intro hGap
    have hDilSmul : (2 : ℝ) • CIK.dilationGap = 0 := by
      rw [← CIK.mpChiralGap_eq_two_smul_dilationGap]
      exact hGap
    have hDil : CIK.dilationGap = 0 := by
      exact (smul_eq_zero.mp hDilSmul).resolve_left (by norm_num)
    exact CIK.isEP_of_dilationGap_eq_zero hDil
  · intro hEP
    rw [CIK.mpChiralGap_eq_two_smul_dilationGap, CIK.dilationGap_eq_zero_of_isEP hEP]
    simp

@[rep_depth operator] theorem mpInverseCommutator_eq_zero_iff_isEP :
    CIK.mpInverseCommutator = 0 ↔ CIK.IsEP := by
  rw [CIK.mpInverseCommutator_eq_mpChiralGap]
  exact CIK.mpChiralGap_eq_zero_iff_isEP

@[rep_depth operator] theorem spectralProjector_commutator_dilationGap_eq_neg_half_chiralAnomaly_of_mpRightCommute
    (hRight : CIK.drazinCoreProj * CIK.mpRightProj = CIK.mpRightProj * CIK.drazinCoreProj) :
    CIK.drazinCoreProj * CIK.dilationGap - CIK.dilationGap * CIK.drazinCoreProj =
      -((2 : ℝ)⁻¹) • CIK.chiralAnomaly := by
  simpa [CertifiedInverseKernel.drazinCoreProj, CertifiedInverseKernel.mpRightProj] using
    CIK.spectralProjector_commutator_dilationGap_eq_neg_half_anomaly_of_rightProjector_commute hRight

@[rep_depth operator] theorem spectralProjector_commutator_dilationGap_eq_zero_of_mpRightCommute_of_chiralScale_eq_zero
    (hRight : CIK.drazinCoreProj * CIK.mpRightProj = CIK.mpRightProj * CIK.drazinCoreProj)
    (hScale : CIK.chiralScale = 0) :
    CIK.drazinCoreProj * CIK.dilationGap - CIK.dilationGap * CIK.drazinCoreProj = 0 := by
  simpa [CertifiedInverseKernel.drazinCoreProj, CertifiedInverseKernel.mpRightProj] using
    CIK.spectralProjector_commutator_dilationGap_eq_zero_of_rightProjector_commute_of_chiralScale_eq_zero
      hRight hScale

end CertifiedInverseKernel

end InfoGeometry.Canonical
