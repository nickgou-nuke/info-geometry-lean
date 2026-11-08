import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

/-!
# Topological readout for the split-Clifford Heisenberg property

This file packages the existing source-side split-Clifford Heisenberg property
as a discrete topological readout.  It does not claim that every current
representation comes from such a property; it only records the continuity and
local constancy of the property-to-current / property-to-Sugawara maps under the
discrete topology.
-/

namespace InfoGeometry.Topology.SplitCliffordHeisenbergTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

noncomputable section

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

instance splitCliffordHeisenbergWitnessTopologicalSpace :
    TopologicalSpace (SplitCliffordHeisenbergWitness 𝕜 V) := ⊥

instance splitCliffordHeisenbergWitnessDiscreteTopology :
    DiscreteTopology (SplitCliffordHeisenbergWitness 𝕜 V) := ⟨rfl⟩

instance currentHeisenbergRepTopologicalSpace :
    TopologicalSpace (CurrentHeisenbergRep 𝕜 V) := ⊥

instance currentHeisenbergRepDiscreteTopology :
    DiscreteTopology (CurrentHeisenbergRep 𝕜 V) := ⟨rfl⟩

instance currentSugawaraMorphismTopologicalSpace :
    TopologicalSpace (CurrentSugawaraMorphism 𝕜 V) := ⊥

instance currentSugawaraMorphismDiscreteTopology :
    DiscreteTopology (CurrentSugawaraMorphism 𝕜 V) := ⟨rfl⟩

/-- The split-Clifford property read as a topological current representation. -/
def topologicalSplitCliffordToCurrentHeisenbergRep
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V :=
  W.toCurrentHeisenbergRep

@[simp] theorem topologicalSplitCliffordToCurrentHeisenbergRep_eq
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    topologicalSplitCliffordToCurrentHeisenbergRep (𝕜 := 𝕜) (V := V) W =
      W.toCurrentHeisenbergRep := by
  rfl

theorem continuous_topologicalSplitCliffordToCurrentHeisenbergRep :
    Continuous (topologicalSplitCliffordToCurrentHeisenbergRep
      (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalSplitCliffordToCurrentHeisenbergRep] using
    (continuous_of_discreteTopology :
      Continuous (topologicalSplitCliffordToCurrentHeisenbergRep
        (𝕜 := 𝕜) (V := V)))

theorem isLocallyConstant_topologicalSplitCliffordToCurrentHeisenbergRep :
    IsLocallyConstant (topologicalSplitCliffordToCurrentHeisenbergRep
      (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalSplitCliffordToCurrentHeisenbergRep] using
    (IsLocallyConstant.of_discrete
      (f := topologicalSplitCliffordToCurrentHeisenbergRep (𝕜 := 𝕜) (V := V)))

/-- The split-Clifford property read as a topological Sugawara morphism package. -/
def topologicalSplitCliffordToCurrentSugawaraMorphism
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  W.toCurrentSugawaraMorphism

@[simp] theorem topologicalSplitCliffordToCurrentSugawaraMorphism_eq
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    topologicalSplitCliffordToCurrentSugawaraMorphism (𝕜 := 𝕜) (V := V) W =
      W.toCurrentSugawaraMorphism := by
  rfl

theorem continuous_topologicalSplitCliffordToCurrentSugawaraMorphism :
    Continuous (topologicalSplitCliffordToCurrentSugawaraMorphism
      (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalSplitCliffordToCurrentSugawaraMorphism] using
    (continuous_of_discreteTopology :
      Continuous (topologicalSplitCliffordToCurrentSugawaraMorphism
        (𝕜 := 𝕜) (V := V)))

theorem isLocallyConstant_topologicalSplitCliffordToCurrentSugawaraMorphism :
    IsLocallyConstant (topologicalSplitCliffordToCurrentSugawaraMorphism
      (𝕜 := 𝕜) (V := V)) := by
  simpa [topologicalSplitCliffordToCurrentSugawaraMorphism] using
    (IsLocallyConstant.of_discrete
      (f := topologicalSplitCliffordToCurrentSugawaraMorphism
        (𝕜 := 𝕜) (V := V)))

end
end InfoGeometry.Topology.SplitCliffordHeisenbergTopological
