import InfoGeometry.Canonical.G2HolonomyGaugeConnections
import InfoGeometry.Canonical.SplitG2HodgeDualFourForm

namespace InfoGeometry.Canonical

/-!
# Differential-form bridge for the discrete split-`G₂` transport owner

The Hodge owner supplies an explicit `3 ↔ 4` inverse pair on alternating
maps.  This file only transports a chosen four-form along the existing
discrete gauge connection.  In particular, it does not identify the current
three-form value property with an `AlternatingMap`, and it does not infer
closedness from Moufang identities.
-/

abbrev SplitG2ThreeForm := SplitG2ThreeForms
abbrev SplitG2FourForm := SplitG2FourForms

noncomputable def coassociativeFourForm
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForm) : SplitG2FourForm :=
  H.coassociativeFourForm φ

theorem coassociativeFourForm_eq_hodgeStar
    (H : SplitG2HodgeDualData) (φ : SplitG2ThreeForm) :
    coassociativeFourForm H φ = H.star34 φ :=
  rfl

def PreservesFourForm (g : SplitG2Automorphism) (ψ : SplitG2FourForm) : Prop :=
  ∀ X : Fin 4 → imaginarySplitOctonion,
    ψ (fun i => g (X i)) = ψ X

theorem parallelTransport_preserves_fourForm
    {E : Type*} (A : SplitG2GaugeConnection E)
    (ψ : SplitG2FourForm)
    (hψ : ∀ e, PreservesFourForm (A.edgeToG2 e) ψ)
    (path : List E) (X : Fin 4 → imaginarySplitOctonion) :
    ψ (fun i => parallelTransport A path (X i)) = ψ X := by
  induction path with
  | nil => rfl
  | cons e path ih =>
      calc
        ψ (fun i => parallelTransport A (e :: path) (X i)) =
            ψ (fun i => (A.edgeToG2 e) (parallelTransport A path (X i))) := by
                simp [parallelTransport_cons, SplitG2Automorphism.comp_apply]
        _ = ψ (fun i => parallelTransport A path (X i)) := hψ e _
        _ = ψ X := ih

theorem curvature_preserves_fourForm
    {E : Type*} (A : SplitG2GaugeConnection E)
    (ψ : SplitG2FourForm)
    (hψ : ∀ e, PreservesFourForm (A.edgeToG2 e) ψ)
    (e₁ e₂ e₃ : E) (X : Fin 4 → imaginarySplitOctonion) :
    ψ (fun i => curvature A e₁ e₂ e₃ (X i)) = ψ X := by
  exact parallelTransport_preserves_fourForm A ψ hψ [e₁, e₂, e₃] X

end InfoGeometry.Canonical
