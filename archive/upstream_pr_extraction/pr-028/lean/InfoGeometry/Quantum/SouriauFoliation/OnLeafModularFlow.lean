/-
InfoGeometry/Quantum/SouriauFoliation/OnLeafModularFlow.lean
-/
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

/--
Reversible on-leaf flow.

The field `preserves_leaf` is the only geometric law required here.  Entropy and
Weyl-scale conservation are then consequences of the leaf constants.
-/
structure OnLeafModularFlow
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Time-indexed reversible flow. -/
  flow : ℝ → State → State

  /-- The flow stays on the selected leaf. -/
  preserves_leaf :
    ∀ (t : ℝ) ⦃x : State⦄, x ∈ L.carrier → flow t x ∈ L.carrier

namespace OnLeafModularFlow

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (F : OnLeafModularFlow L)

/-- Entropy is preserved by any supplied on-leaf flow. -/
theorem entropy_preserved
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    L.entropyReadout (F.flow t x) = L.entropyReadout x :=
  L.entropy_eq_of_mem (F.preserves_leaf t hx) hx

/-- Weyl scale is preserved by any supplied on-leaf flow. -/
theorem weylScale_preserved
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    L.weylScaleReadout (F.flow t x) = L.weylScaleReadout x :=
  L.weylScale_eq_of_mem (F.preserves_leaf t hx) hx

end OnLeafModularFlow

end InfoGeometry.Quantum.SouriauFoliation
