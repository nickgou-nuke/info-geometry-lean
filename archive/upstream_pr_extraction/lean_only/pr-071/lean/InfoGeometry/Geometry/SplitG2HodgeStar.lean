import InfoGeometry.Canonical.G2HolonomyDifferentialForms

namespace InfoGeometry.Geometry

/-!
# Geometry-level split-`G₂` Hodge data

This file is a geometry-facing bridge to the already verified canonical
`3 ↔ 4` duality owner.  It re-exports the alternating 3- and 4-form carriers
and the transport lemmas, but it does not claim a new metric-based Hodge
theorem on a smooth manifold.
-/

abbrev SplitG2HodgeData := InfoGeometry.Canonical.SplitG2HodgeDualData
abbrev SplitG2ThreeForm := InfoGeometry.Canonical.SplitG2ThreeForms
abbrev SplitG2FourForm := InfoGeometry.Canonical.SplitG2FourForms
abbrev PreservesFourForm := InfoGeometry.Canonical.PreservesFourForm

noncomputable def coassociativeFourForm
    (H : SplitG2HodgeData) (φ : SplitG2ThreeForm) : SplitG2FourForm :=
  H.coassociativeFourForm φ

theorem coassociativeFourForm_eq_hodgeStar
    (H : SplitG2HodgeData) (φ : SplitG2ThreeForm) :
    coassociativeFourForm H φ = H.star34 φ := by
  rfl

theorem parallelTransport_preserves_fourForm
    {E : Type*} (A : InfoGeometry.Canonical.SplitG2GaugeConnection E)
    (ψ : SplitG2FourForm)
    (hψ : ∀ e, PreservesFourForm (A.edgeToG2 e) ψ)
    (path : List E)
    (X : Fin 4 → InfoGeometry.Canonical.imaginarySplitOctonion) :
    ψ (fun i => InfoGeometry.Canonical.parallelTransport A path (X i)) = ψ X := by
  exact InfoGeometry.Canonical.parallelTransport_preserves_fourForm A ψ hψ path X

theorem curvature_preserves_fourForm
    {E : Type*} (A : InfoGeometry.Canonical.SplitG2GaugeConnection E)
    (ψ : SplitG2FourForm)
    (hψ : ∀ e, PreservesFourForm (A.edgeToG2 e) ψ)
    (e₁ e₂ e₃ : E)
    (X : Fin 4 → InfoGeometry.Canonical.imaginarySplitOctonion) :
    ψ (fun i => InfoGeometry.Canonical.curvature A e₁ e₂ e₃ (X i)) = ψ X := by
  exact InfoGeometry.Canonical.curvature_preserves_fourForm A ψ hψ e₁ e₂ e₃ X

end InfoGeometry.Geometry
