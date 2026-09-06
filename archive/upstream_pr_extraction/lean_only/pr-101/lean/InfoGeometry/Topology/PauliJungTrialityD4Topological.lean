import Mathlib
import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

instance colorChannelTopologicalSpace : TopologicalSpace ColorChannel := ⊥

instance colorChannelDiscreteTopology : DiscreteTopology ColorChannel :=
  ⟨rfl⟩

/-!
# Topology of the finite grading labels

The color and Klein-four labels are finite discrete carriers.  This file
proves continuity of their relabellings only; it does not promote the label
action to continuity of a projective or octonionic action.
-/

theorem continuous_trialityPermute
    [TopologicalSpace ColorChannel] [DiscreteTopology ColorChannel] :
    Continuous trialityPermute := by
  exact continuous_of_discreteTopology

theorem continuous_colorPermutation
    [TopologicalSpace ColorChannel] [DiscreteTopology ColorChannel]
    (p : ColorPermutation) :
    Continuous p := by
  exact continuous_of_discreteTopology

theorem continuous_gradeCycle
    [TopologicalSpace KleinFour] [DiscreteTopology KleinFour] :
    Continuous gradeCycle := by
  exact continuous_of_discreteTopology

def colorOrbit (c : ColorChannel) : Set ColorChannel :=
  {d | ∃ p : ColorPermutation, p c = d}

def colorOrbitMap (c : ColorChannel) : ColorPermutation → ColorChannel :=
  fun p => p c

theorem continuous_colorOrbitMap
    [TopologicalSpace ColorPermutation] [DiscreteTopology ColorPermutation]
    (c : ColorChannel) :
    Continuous (colorOrbitMap c) := by
  exact continuous_of_discreteTopology

theorem colorOrbit_eq_univ (c : ColorChannel) :
    colorOrbit c = Set.univ := by
  ext d
  constructor
  · intro _
    trivial
  · intro _
    by_cases h : c = d
    · exact ⟨Equiv.refl ColorChannel, by simpa [h]⟩
    · exact ⟨Equiv.swap c d, by simp [h]⟩

theorem isClosed_colorOrbit
    (c : ColorChannel) :
    IsClosed (colorOrbit c) := by
  rw [colorOrbit_eq_univ]
  exact isClosed_univ

theorem closure_colorOrbit (c : ColorChannel) :
    closure (colorOrbit c) = Set.univ := by
  rw [colorOrbit_eq_univ]
  exact closure_univ

end InfoGeometry.Topology
