import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.QuantumPresentation
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.ArnoldNetworkPresentation

Translator surface from the Arnold-Majorana network lane to
`QuantumPresentation`.

This file does not redefine the Arnold owner logic. It packages the existing
network output as the generator lane on the doubled carrier.
-/

namespace InfoGeometry.Canonical.ArnoldNetworkPresentation

open InfoGeometry.Canonical.QuantumPresentation
open InfoGeometry.Canonical.MoE

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- One-token Arnold network generator on the doubled carrier. -/
@[rep_depth operator]
noncomputable def arnoldGenerator
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E :=
  fun ψ => arnoldNetworkOutput n net β (fun _ : Unit => ψ) ()

/-- Default metric readout for the Arnold doubled carrier. -/
@[rep_depth operator]
noncomputable def arnoldMetricReadout (ψ : ArnoldMajoranaCarrier E) : ℝ :=
  ‖ψ‖

/-- Phase-style signed readout on the doubled carrier. -/
@[rep_depth operator]
noncomputable def arnoldPhaseReadout (ψ : ArnoldMajoranaCarrier E) : ℝ :=
  ‖WithLp.fst ψ‖ - ‖WithLp.snd ψ‖

/-- Arnold metric readout is always nonnegative. -/
@[rep_depth operator]
theorem arnoldMetricReadout_nonneg (ψ : ArnoldMajoranaCarrier E) :
    0 ≤ arnoldMetricReadout ψ := by
  simp [arnoldMetricReadout]

/--
Translator map from Arnold-Majorana network data to `QuantumPresentation`.
-/
@[rep_depth operator]
noncomputable def toQuantumPresentation
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    QuantumPresentation where
  Scalar := ℝ
  State := ArnoldMajoranaCarrier E
  Observable := ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E
  act := fun A ψ => A ψ
  support := fun _ => True
  generator := arnoldGenerator n net β
  metricReadout := arnoldMetricReadout
  phaseReadout := arnoldPhaseReadout

@[rep_depth operator]
theorem toQuantumPresentation_generator_eq_arnold
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    (ψ : ArnoldMajoranaCarrier E) :
    (toQuantumPresentation (E := E) n net β).generator ψ
      = arnoldNetworkOutput n net β (fun _ : Unit => ψ) () := by
  rfl

/--
Transport bridge: if every expert preserves a submodule, the one-token Arnold
generator preserves it as well.
-/
@[rep_depth transport]
theorem arnoldGenerator_mem_submodule
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    (U : Submodule ℝ (ArnoldMajoranaCarrier E))
    (ψ : ArnoldMajoranaCarrier E)
    (hU : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ U → (net.moe.experts e).apply v ∈ U)
    (hψ : ψ ∈ U) :
    arnoldGenerator (E := E) n net β ψ ∈ U := by
  simpa [arnoldGenerator] using
    (arnoldNetwork_preserves_submodule (E := E)
      (n := n) (net := net) (β := β)
      (U := U) (x := fun _ : Unit => ψ) (i := ())
      hU hψ)

/--
Fixed-point bridge: if every expert fixes the current state, the one-token
Arnold generator is the identity on that state.
-/
@[rep_depth transport]
theorem arnoldGenerator_eq_of_experts_fix
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    [Nonempty (Fin n)]
    (ψ : ArnoldMajoranaCarrier E)
    (hfix : ∀ e : ExpertIdx n, (net.moe.experts e).apply ψ = ψ) :
    arnoldGenerator (E := E) n net β ψ = ψ := by
  simpa [arnoldGenerator] using
    (arnoldNetworkOutput_eq_of_experts_fix (E := E)
      (n := n) (net := net) (β := β)
      (x := fun _ : Unit => ψ) (i := ())
      (hfix := by
        intro e
        simpa using hfix e))

/-- Tagged presentation witness for the Arnold/Majorana doubled lane. -/
@[rep_depth operator]
noncomputable def taggedPresentation
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    TaggedPresentation where
  lane := PresentationLane.arnoldNetwork
  data := toQuantumPresentation (E := E) n net β

end InfoGeometry.Canonical.ArnoldNetworkPresentation
