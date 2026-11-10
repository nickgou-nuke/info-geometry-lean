import InfoGeometry.Canonical.ArnoldNetworkPresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

/-- The Arnold norm readout is not the doubled Fierz quadratic readout in
general. On the vector `(1,1) : ℝ × ℝ`, the former is `√2` while the latter is
`2`; thus the identity state map does not by itself preserve these readouts. -/
@[rep_depth krein]
theorem arnold_metric_readout_differs_from_fierz_on_pair_one :
    let ψ : ArnoldMajoranaCarrier ℝ := WithLp.toLp (2 : ENNReal) (1, 1)
    arnoldMetricReadout ψ ≠
      (doubledFierzReadout (E := ℝ)).hilbert ψ := by
  intro ψ
  change ‖ψ‖ ≠ InfoGeometry.Quantum.Fierz.infoHilbert ψ
  have hnorm : ‖ψ‖ ^ 2 = 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp [ψ]
    norm_num
  have htarget : InfoGeometry.Quantum.Fierz.infoHilbert ψ = 2 := by
    simp [InfoGeometry.Quantum.Fierz.infoHilbert, ψ]
    norm_num
  intro h
  rw [h, htarget] at hnorm
  norm_num at hnorm

end InfoGeometry.Canonical.ArnoldNetworkIntertwiner
