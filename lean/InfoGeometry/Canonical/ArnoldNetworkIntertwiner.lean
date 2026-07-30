import InfoGeometry.Canonical.ArnoldNetworkPresentation
import InfoGeometry.Canonical.FierzReadout
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ArnoldNetworkIntertwiner

Compositional bridge from the Arnold network presentation lane into the
doubled/Krein readout lane.

This file provides an explicit `Intertwiner` skeleton. It is intentionally
guarded by fixed-point hypotheses on experts, so the generator-preservation
field is mathematically honest.
-/

namespace InfoGeometry.Canonical.ArnoldNetworkIntertwiner

open InfoGeometry.Canonical.QuantumPresentation
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.ArnoldNetworkPresentation
open InfoGeometry.Canonical.FierzReadout
open InfoGeometry.Canonical.FierzReadout.FierzChannelReadout

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
Intertwiner from Arnold-network presentation to doubled/Krein Fierz
presentation under expert fixed-point hypotheses.
-/
@[rep_depth krein]
noncomputable def arnoldToDoubledKreinIntertwiner_of_expertsFix
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    [Nonempty (Fin n)]
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = v) :
    Intertwiner
      (ArnoldNetworkPresentation.toQuantumPresentation (E := E) n net β)
      ((doubledFierzReadout (E := E)).toQuantumPresentation) where
  mapState := fun ψ => ψ
  mapObservable := fun A => A
  mapScalar := fun x => x
  map_act := by
    intro o s
    rfl
  map_support := by
    intro s _
    simpa [FierzChannelReadout.toQuantumPresentation,
      toQuantumPresentationWith, defaultSupport, doubledFierzReadout] using
      (InfoGeometry.Quantum.Fierz.infoHilbert_nonneg s)
  map_generator := by
    intro s
    change arnoldGenerator (E := E) n net β s = s
    exact arnoldGenerator_eq_of_experts_fix
      (E := E) (n := n) (net := net) (β := β) (ψ := s)
      (hfix := by
        intro e
        exact hfix e s)

/--
Readout-preservation contract for the Arnold→doubled/Krein intertwiner,
parametrized by pointwise readout-identification hypotheses.
-/
@[rep_depth krein]
theorem arnoldToDoubledKrein_readoutPreservation_of_pointwise_eq
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    [Nonempty (Fin n)]
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = v)
    (hMetric : ∀ ψ : ArnoldMajoranaCarrier E,
      arnoldMetricReadout (E := E) ψ
        = (doubledFierzReadout (E := E)).hilbert ψ)
    (hPhase : ∀ ψ : ArnoldMajoranaCarrier E,
      arnoldPhaseReadout (E := E) ψ
        = (doubledFierzReadout (E := E)).symplectic ψ) :
    ReadoutPreservation
      (arnoldToDoubledKreinIntertwiner_of_expertsFix
        (E := E) n net β hfix) := by
  refine ⟨?_, ?_⟩
  · intro s
    simpa [arnoldToDoubledKreinIntertwiner_of_expertsFix,
      ArnoldNetworkPresentation.toQuantumPresentation, doubledFierzReadout,
      FierzChannelReadout.toQuantumPresentation] using hMetric s
  · intro s
    simpa [arnoldToDoubledKreinIntertwiner_of_expertsFix,
      ArnoldNetworkPresentation.toQuantumPresentation, doubledFierzReadout,
      FierzChannelReadout.toQuantumPresentation] using hPhase s

end InfoGeometry.Canonical.ArnoldNetworkIntertwiner
