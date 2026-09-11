/-
InfoGeometry/Quantum/SouriauFoliation/LeafInvariantReadout.lean
-/
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.SouriauFoliation.OnLeafModularFlow

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

/--
A readout which is constant on a Souriau leaf.

This is the sidecar form of an invariant Itakura-Saito / shape-core readout.
It is deliberately weaker than a global metric theorem.
-/
def LeafInvariantReadout
    {State : Type*}
    (L : SymplecticLeaf State) :=
  {readout : State → ℝ //
    ∀ ⦃x y : State⦄,
      x ∈ L.carrier → y ∈ L.carrier →
        readout x = readout y}

namespace LeafInvariantReadout

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (R : LeafInvariantReadout L)

abbrev readout : State → ℝ := R.1

theorem invariant_on_leaf
    {x y : State}
    (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) :
    R.readout x = R.readout y :=
  R.2 hx hy

def mk
    (readout : State → ℝ)
    (invariant_on_leaf :
      ∀ ⦃x y : State⦄,
        x ∈ L.carrier → y ∈ L.carrier →
          readout x = readout y) :
    LeafInvariantReadout L :=
  ⟨readout, invariant_on_leaf⟩

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
