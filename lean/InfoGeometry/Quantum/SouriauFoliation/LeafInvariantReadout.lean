/-
InfoGeometry/Quantum/SouriauFoliation/LeafInvariantReadout.lean
-/
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf
import InfoGeometry.Quantum.SouriauFoliation.OnLeafModularFlow

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

/--
A readout which is constant on a Souriau leaf.

This is the sidecar form of an invariant Itakura-Saito / shape-core readout.
It is deliberately weaker than a global metric theorem.
-/
structure LeafInvariantReadout
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- Leaf-level shape/core readout. -/
  readout : State → ℝ

  /-- The readout is constant along the leaf. -/
  invariant_on_leaf :
    ∀ ⦃x y : State⦄,
      x ∈ L.carrier → y ∈ L.carrier →
        readout x = readout y

namespace LeafInvariantReadout

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (R : LeafInvariantReadout L)

/-- The leaf-invariant readout is preserved by any supplied on-leaf flow. -/
theorem readout_preserved_by_onLeafFlow
    (F : OnLeafModularFlow L)
    (t : ℝ)
    {x : State}
    (hx : x ∈ L.carrier) :
    R.readout (F.flow t x) = R.readout x :=
  R.invariant_on_leaf (F.preserves_leaf t hx) hx

end LeafInvariantReadout

end InfoGeometry.Quantum.SouriauFoliation
