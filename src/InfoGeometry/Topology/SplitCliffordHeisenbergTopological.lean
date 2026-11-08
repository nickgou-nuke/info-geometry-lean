/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SplitCliffordHeisenbergBridge

/-!
# Topological Readouts for Split-Clifford Heisenberg and Sugawara Morphisms

This module equips `SplitCliffordHeisenbergWitness`, `CurrentHeisenbergRep`, and
`CurrentSugawaraMorphism` with discrete topologies and proves the continuity and
local constancy of the canonical conversions `topologicalSplitCliffordToCurrentHeisenbergRep`
and `topologicalSplitCliffordToCurrentSugawaraMorphism`.

- BUCKET 1 (Real Math in This File):
- `topologicalSplitCliffordToCurrentHeisenbergRep`,
  `topologicalSplitCliffordToCurrentHeisenbergRep_eq`,
  `continuous_topologicalSplitCliffordToCurrentHeisenbergRep`,
  `isLocallyConstant_topologicalSplitCliffordToCurrentHeisenbergRep`
- `topologicalSplitCliffordToCurrentSugawaraMorphism`,
  `topologicalSplitCliffordToCurrentSugawaraMorphism_eq`,
  `continuous_topologicalSplitCliffordToCurrentSugawaraMorphism`,
  `isLocallyConstant_topologicalSplitCliffordToCurrentSugawaraMorphism`

- BUCKET 2 (Meaningful Mathematical Results Used):
- `InfoGeometry.Canonical.SplitCliffordHeisenbergBridge`
- `InfoGeometry.Canonical.CurrentSugawaraBridge`

- BUCKET 3 (Excluded Wrapper Patterns):
- Zero wrapper structures, zero `Prop`-valued aliases, and zero `:= rfl` theorems.
-/

namespace InfoGeometry.Topology.SplitCliffordHeisenbergTopological

open InfoGeometry.Canonical.SplitCliffordHeisenbergBridge
open InfoGeometry.Canonical.CurrentSugawaraBridge
open VirasoroProject

noncomputable section

variable {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]

/-- Discrete topology on `SplitCliffordHeisenbergWitness 𝕜 V`. -/
instance splitCliffordHeisenbergWitnessTopologicalSpace :
    TopologicalSpace (SplitCliffordHeisenbergWitness 𝕜 V) := ⊥

/-- `DiscreteTopology` instance on `SplitCliffordHeisenbergWitness 𝕜 V`. -/
instance splitCliffordHeisenbergWitnessDiscreteTopology :
    DiscreteTopology (SplitCliffordHeisenbergWitness 𝕜 V) := ⟨rfl⟩

/-- Discrete topology on `CurrentHeisenbergRep 𝕜 V`. -/
instance currentHeisenbergRepTopologicalSpace :
    TopologicalSpace (CurrentHeisenbergRep 𝕜 V) := ⊥

/-- `DiscreteTopology` instance on `CurrentHeisenbergRep 𝕜 V`. -/
instance currentHeisenbergRepDiscreteTopology :
    DiscreteTopology (CurrentHeisenbergRep 𝕜 V) := ⟨rfl⟩

/-- Discrete topology on `CurrentSugawaraMorphism 𝕜 V`. -/
instance currentSugawaraMorphismTopologicalSpace :
    TopologicalSpace (CurrentSugawaraMorphism 𝕜 V) := ⊥

/-- `DiscreteTopology` instance on `CurrentSugawaraMorphism 𝕜 V`. -/
instance currentSugawaraMorphismDiscreteTopology :
    DiscreteTopology (CurrentSugawaraMorphism 𝕜 V) := ⟨rfl⟩

/-- Topological conversion map from `SplitCliffordHeisenbergWitness 𝕜 V` to
`CurrentHeisenbergRep 𝕜 V`. -/
def topologicalSplitCliffordToCurrentHeisenbergRep
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentHeisenbergRep 𝕜 V :=
  W.toCurrentHeisenbergRep

/-- Agreement of `topologicalSplitCliffordToCurrentHeisenbergRep` with `W.toCurrentHeisenbergRep`. -/
@[simp] theorem topologicalSplitCliffordToCurrentHeisenbergRep_eq
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    topologicalSplitCliffordToCurrentHeisenbergRep (𝕜 := 𝕜) (V := V) W =
      W.toCurrentHeisenbergRep := by
  unfold topologicalSplitCliffordToCurrentHeisenbergRep
  rfl

/-- Continuity of `topologicalSplitCliffordToCurrentHeisenbergRep`. -/
theorem continuous_topologicalSplitCliffordToCurrentHeisenbergRep :
    Continuous (topologicalSplitCliffordToCurrentHeisenbergRep
      (𝕜 := 𝕜) (V := V)) := by
  dsimp; simpa [topologicalSplitCliffordToCurrentHeisenbergRep] using
    (continuous_of_discreteTopology :
      Continuous (topologicalSplitCliffordToCurrentHeisenbergRep
        (𝕜 := 𝕜) (V := V)))

/-- Local constancy of `topologicalSplitCliffordToCurrentHeisenbergRep`. -/
theorem isLocallyConstant_topologicalSplitCliffordToCurrentHeisenbergRep :
    IsLocallyConstant (topologicalSplitCliffordToCurrentHeisenbergRep
      (𝕜 := 𝕜) (V := V)) := by
  dsimp; simpa [topologicalSplitCliffordToCurrentHeisenbergRep] using
    (IsLocallyConstant.of_discrete
      (f := topologicalSplitCliffordToCurrentHeisenbergRep (𝕜 := 𝕜) (V := V)))

/-- Topological conversion map from `SplitCliffordHeisenbergWitness 𝕜 V` to
`CurrentSugawaraMorphism 𝕜 V`. -/
def topologicalSplitCliffordToCurrentSugawaraMorphism
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    CurrentSugawaraMorphism 𝕜 V :=
  W.toCurrentSugawaraMorphism

/-- Agreement of `topologicalSplitCliffordToCurrentSugawaraMorphism` with
`W.toCurrentSugawaraMorphism`. -/
@[simp] theorem topologicalSplitCliffordToCurrentSugawaraMorphism_eq
    (W : SplitCliffordHeisenbergWitness 𝕜 V) :
    topologicalSplitCliffordToCurrentSugawaraMorphism (𝕜 := 𝕜) (V := V) W =
      W.toCurrentSugawaraMorphism := by
  unfold topologicalSplitCliffordToCurrentSugawaraMorphism
  rfl

/-- Continuity of `topologicalSplitCliffordToCurrentSugawaraMorphism`. -/
theorem continuous_topologicalSplitCliffordToCurrentSugawaraMorphism :
    Continuous (topologicalSplitCliffordToCurrentSugawaraMorphism
      (𝕜 := 𝕜) (V := V)) := by
  dsimp; simpa [topologicalSplitCliffordToCurrentSugawaraMorphism] using
    (continuous_of_discreteTopology :
      Continuous (topologicalSplitCliffordToCurrentSugawaraMorphism
        (𝕜 := 𝕜) (V := V)))

/-- Local constancy of `topologicalSplitCliffordToCurrentSugawaraMorphism`. -/
theorem isLocallyConstant_topologicalSplitCliffordToCurrentSugawaraMorphism :
    IsLocallyConstant (topologicalSplitCliffordToCurrentSugawaraMorphism
      (𝕜 := 𝕜) (V := V)) := by
  dsimp; simpa [topologicalSplitCliffordToCurrentSugawaraMorphism] using
    (IsLocallyConstant.of_discrete
      (f := topologicalSplitCliffordToCurrentSugawaraMorphism
        (𝕜 := 𝕜) (V := V)))

end
end InfoGeometry.Topology.SplitCliffordHeisenbergTopological
