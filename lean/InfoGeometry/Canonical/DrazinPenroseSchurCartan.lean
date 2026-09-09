import InfoGeometry.Canonical.ConformalProjectorCore

/-! A theorem-facing bridge for Cartan involutions, certified projectors, and
pseudoinverse-stabilized Schur reduction.  No physical emergence claim is
made by this interface. -/
namespace InfoGeometry.Canonical.DrazinPenroseSchurCartan

open InfoGeometry.Canonical.ConformalUnification

universe u

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

structure CartanInvolutionData where
  theta : E →L[ℝ] E
  involutive : theta.comp theta = ContinuousLinearMap.id ℝ E

namespace CartanInvolutionData
variable (C : CartanInvolutionData (E := E))
def fixed : Set E := {x | C.theta x = x}
def antiFixed : Set E := {x | C.theta x = -x}
theorem theta_sq_eq_id : C.theta.comp C.theta = ContinuousLinearMap.id ℝ E :=
  C.involutive
end CartanInvolutionData
end

section
variable {P Θ : Type u} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [CompleteSpace P] [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

noncomputable def schurPenroseEffective
    (L_PP : P →L[ℝ] P) (L_PΘ : Θ →L[ℝ] P)
    (L_ΘΘ_MP : Θ →L[ℝ] Θ) (L_ΘP : P →L[ℝ] Θ) : P →L[ℝ] P :=
  L_PP - L_PΘ.comp (L_ΘΘ_MP.comp L_ΘP)
end

section
variable {E P Θ : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [CompleteSpace P] [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]

structure CartanDrazinPenroseSchurPacket where
  cartan : CartanInvolutionData (E := E)
  conformal : CertifiedConformalInference E
  L_PP : P →L[ℝ] P
  L_PΘ : Θ →L[ℝ] P
  L_ΘΘ_MP : Θ →L[ℝ] Θ
  L_ΘP : P →L[ℝ] Θ
  theta_fixed_iff_spectral : ∀ x : E,
    cartan.theta x = x ↔ conformal.spectralProjector x = x
  theta_antiFixed_iff_metric : ∀ x : E,
    cartan.theta x = -x ↔ conformal.metricProjector x = x

namespace CartanDrazinPenroseSchurPacket
variable (C : CartanDrazinPenroseSchurPacket (E := E) (P := P) (Θ := Θ))

abbrev topologicalProjector : E →L[ℝ] E := C.conformal.spectralProjector
abbrev transportProjector : E →L[ℝ] E := C.conformal.metricProjector
noncomputable def effectiveTransport : P →L[ℝ] P :=
  schurPenroseEffective C.L_PP C.L_PΘ C.L_ΘΘ_MP C.L_ΘP

theorem theta_fixed_iff_topological (x : E) :
    C.cartan.theta x = x ↔ C.topologicalProjector x = x :=
  C.theta_fixed_iff_spectral x

theorem theta_antiFixed_iff_transport (x : E) :
    C.cartan.theta x = -x ↔ C.transportProjector x = x :=
  C.theta_antiFixed_iff_metric x

theorem effectiveTransport_eq_schurPenrose :
    C.effectiveTransport = schurPenroseEffective C.L_PP C.L_PΘ
      C.L_ΘΘ_MP C.L_ΘP := rfl

theorem package (x : E) :
    (C.cartan.theta x = x ↔ C.topologicalProjector x = x) ∧
    (C.cartan.theta x = -x ↔ C.transportProjector x = x) ∧
    C.effectiveTransport = schurPenroseEffective C.L_PP C.L_PΘ
      C.L_ΘΘ_MP C.L_ΘP :=
  ⟨C.theta_fixed_iff_topological x, C.theta_antiFixed_iff_transport x,
    C.effectiveTransport_eq_schurPenrose⟩
end CartanDrazinPenroseSchurPacket
end

end InfoGeometry.Canonical.DrazinPenroseSchurCartan
