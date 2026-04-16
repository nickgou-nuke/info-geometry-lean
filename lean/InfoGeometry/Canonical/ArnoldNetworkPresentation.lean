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

/-- Tagged presentation witness for the Arnold/Majorana doubled lane. -/
@[rep_depth operator]
noncomputable def taggedPresentation
    (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) :
    TaggedPresentation where
  lane := PresentationLane.doubledKrein
  data := toQuantumPresentation (E := E) n net β

end InfoGeometry.Canonical.ArnoldNetworkPresentation
