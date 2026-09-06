import InfoGeometry.Canonical.ArnoldMajoranaNetwork
import InfoGeometry.Canonical.ArnoldApproximationCore
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
open InfoGeometry.Canonical.ArnoldApproximationCore

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

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- Arnold metric readout is always nonnegative. -/
theorem arnoldMetricReadout_nonneg (ψ : ArnoldMajoranaCarrier E) :
    0 ≤ arnoldMetricReadout ψ := by
  simp [arnoldMetricReadout]

attribute [rep_depth operator] arnoldMetricReadout_nonneg

/--
Translator map from Arnold-Majorana network data to `QuantumPresentation`.
-/
@[rep_depth operator]
noncomputable def toQuantumPresentation
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    Presentation where
  Scalar := ℝ
  State := ArnoldMajoranaCarrier E
  Observable := ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E
  act := fun A ψ => A ψ
  support := fun ψ => 0 ≤ arnoldMetricReadout ψ
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
Approximation bridge: a shape/scale cost contract on the Arnold lane controls
the one-token generator error on the declared domain.
-/
@[rep_depth operator]
theorem arnoldGenerator_totalCost_le_of_contract
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    {ψ : ArnoldMajoranaCarrier E} (hψ : ψ ∈ C.domain) :
    C.costModel.totalCost
      (arnoldGenerator (E := E) n net β ψ)
      (C.target ψ) ≤ C.costBound := by
  simpa [arnoldGenerator] using
    (arnoldGeneratorCost_le (E := E) (C := C) hψ)

/--
Readout bridge: if the shape/scale cost dominates norm-readout differences, the
metric readout discrepancy is bounded by the property Arnold cost bound.
-/
@[rep_depth operator]
theorem arnoldMetricReadout_error_le_of_shapeScaleContract
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    (hdom : ∀ x y : ArnoldMajoranaCarrier E,
      |arnoldMetricReadout (E := E) x - arnoldMetricReadout (E := E) y|
        ≤ C.costModel.totalCost x y)
    {ψ : ArnoldMajoranaCarrier E} (hψ : ψ ∈ C.domain) :
    |arnoldMetricReadout (E := E) (arnoldGenerator (E := E) n net β ψ)
      - arnoldMetricReadout (E := E) (C.target ψ)| ≤ C.costBound := by
  have hdom' : ∀ x y : ArnoldMajoranaCarrier E,
      |‖x‖ - ‖y‖| ≤ C.costModel.totalCost x y := by
    intro x y
    simpa [arnoldMetricReadout] using hdom x y
  simpa [arnoldMetricReadout, arnoldGenerator] using
    (metricReadout_error_le_of_contract (E := E) (C := C) hdom' hψ)

/--
Presentation-level restatement of the Arnold shape/scale approximation bound.
-/
@[rep_depth operator]
theorem toQuantumPresentation_generator_totalCost_le_of_contract
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ)
    (C : ArnoldGeneratorApproximationContract (E := E) n net β)
    {ψ : ArnoldMajoranaCarrier E} (hψ : ψ ∈ C.domain) :
    C.costModel.totalCost
      ((toQuantumPresentation (E := E) n net β).generator ψ)
      (C.target ψ) ≤ C.costBound := by
  simpa [toQuantumPresentation] using
    (arnoldGenerator_totalCost_le_of_contract (E := E) n net β C hψ)

/--
Transport bridge: if every expert preserves a submodule, the one-token Arnold
generator preserves it as well.
-/
@[rep_depth krein]
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
@[rep_depth krein]
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

/-- Tagged presentation property for the Arnold/Majorana doubled lane. -/
@[rep_depth operator]
noncomputable def taggedPresentation
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    TaggedPresentation where
  lane := PresentationLane.arnoldNetwork
  data := toQuantumPresentation (E := E) n net β

end InfoGeometry.Canonical.ArnoldNetworkPresentation
