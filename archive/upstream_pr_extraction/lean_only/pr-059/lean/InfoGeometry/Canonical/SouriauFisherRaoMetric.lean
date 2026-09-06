import InfoGeometry.Geometry.LegendreHessianInverse

/-!
# Souriau/Fisher geometry: canonical Hessian owner

This module deliberately does not introduce a coordinate matrix model or a
second packet of Fisher axioms.  The owner is
`InfoGeometry.Geometry.LegendreHessianInverse`: its constructive datum uses a
continuous-linear equivalence for the Fisher map, defines the inverse map by
the equivalence inverse, and proves both composition laws in the kernel.

The remaining analytic content of a concrete Souriau ensemble is the
identification of its Massieu Hessian and entropy-gradient derivative with
this datum.  Those are represented by the two explicit fields of the owner,
not hidden behind a scalar or diagonal surrogate.
-/

namespace InfoGeometry.Canonical.SouriauFisherRaoMetric

open InfoGeometry.Geometry

variable {Θ : Type*}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

abbrev Data (Θ : Type*) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] :=
  LegendreContinuousLinearEquivInverseData Θ

/-- The contact moment is the Massieu gradient at the temperature point. -/
theorem moment_eq_massieu_gradient
    (D : Data Θ) :
    D.moment = dualCoord D.massieu D.beta := by
  rfl

/-- The Fisher operator is the Hessian of the Massieu potential. -/
theorem fisher_hessian_eq_massieu_hessian
    (D : Data Θ) :
    D.fisherHessian = hessian D.massieu D.beta :=
  D.fisherEquiv_eq_massieuHessian

/-- The entropy-gradient derivative is the inverse Fisher operator. -/
theorem entropy_hessian_eq_fisher_inverse_map
    (D : Data Θ) :
    D.entropyHessian =
      D.fisherEquiv.symm := by
  rfl

/-- The inverse Fisher map recovers the temperature tangent. -/
theorem entropy_hessian_comp_fisher_hessian
    (D : Data Θ) :
    D.entropyHessian.comp D.fisherHessian =
      ContinuousLinearMap.id ℝ Θ :=
  D.entropyHessian_comp_fisherHessian

/-- The Fisher map recovers the moment tangent. -/
theorem fisher_hessian_comp_entropy_hessian
    (D : Data Θ) :
    D.fisherHessian.comp D.entropyHessian =
      ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  D.fisherHessian_comp_entropyHessian

theorem continuous_fisher_hessian
    (D : Data Θ) :
    Continuous D.fisherHessian :=
  D.fisherHessian.continuous

theorem continuous_entropy_hessian
    (D : Data Θ) :
    Continuous D.entropyHessian :=
  D.entropyHessian.continuous

noncomputable def fisher_hessian_homeomorph
    (D : Data Θ) :
    Θ ≃ₜ MomentCoord Θ :=
  D.fisherEquiv.toHomeomorph

theorem isCompact_fisher_hessian_image
    (D : Data Θ) (K : Set Θ) (hK : IsCompact K) :
    IsCompact (fisher_hessian_homeomorph D '' K) := by
  exact (fisher_hessian_homeomorph D).isCompact_image.mpr hK

theorem isPathConnected_fisher_hessian_image
    (D : Data Θ) (K : Set Θ) (hK : IsPathConnected K) :
    IsPathConnected (fisher_hessian_homeomorph D '' K) := by
  exact (fisher_hessian_homeomorph D).isPathConnected_image.mpr hK

theorem isClosed_fisher_hessian_image
    (D : Data Θ) (K : Set Θ) (hK : IsClosed K) :
    IsClosed (fisher_hessian_homeomorph D '' K) := by
  exact (fisher_hessian_homeomorph D).isClosed_image.mpr hK

theorem isOpen_fisher_hessian_image
    (D : Data Θ) (K : Set Θ) (hK : IsOpen K) :
    IsOpen (fisher_hessian_homeomorph D '' K) := by
  exact (fisher_hessian_homeomorph D).isOpen_image.mpr hK

theorem fisher_hessian_homeomorph_preimage_image
    (D : Data Θ) (K : Set Θ) :
    fisher_hessian_homeomorph D ⁻¹' (fisher_hessian_homeomorph D '' K) = K := by
  exact (fisher_hessian_homeomorph D).preimage_image K

theorem fisher_hessian_homeomorph_image_preimage
    (D : Data Θ) (M : Set (MomentCoord Θ)) :
    fisher_hessian_homeomorph D ''
        (fisher_hessian_homeomorph D ⁻¹' M) = M := by
  exact (fisher_hessian_homeomorph D).image_preimage M

/-- Complete owner theorem for the local Fisher/Legendre inverse geometry. -/
theorem fisher_legendre_inverse_packet
    (D : Data Θ) :
    D.moment = dualCoord D.massieu D.beta
      ∧ D.entropyGradient D.moment = D.beta
      ∧ D.fisherHessian = hessian D.massieu D.beta
      ∧ D.entropyHessian = fderiv ℝ D.entropyGradient D.moment
      ∧ D.entropyHessian.comp D.fisherHessian =
          ContinuousLinearMap.id ℝ Θ
      ∧ D.fisherHessian.comp D.entropyHessian =
          ContinuousLinearMap.id ℝ (MomentCoord Θ) :=
  D.toLegendreHessianInverseContext.legendre_hessian_inverse_packet

end InfoGeometry.Canonical.SouriauFisherRaoMetric
