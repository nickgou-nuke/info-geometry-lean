import InfoGeometry.Topology.PauliJungD4StarTopology

namespace InfoGeometry.Topology.G2AutomorphismTrialityGroup

open InfoGeometry.Canonical
open InfoGeometry.Topology.PauliJungD4Star

/-!
# Finite triality shadow of the D₄ star graph

This file stays theorem-honest: it packages the order-three color cycle as a
discrete star-graph automorphism. It does **not** claim a formal Lie-group
construction of `G₂`; that would require a separate representation-theoretic
development.
-/

/-- The order-three automorphism of the four-vertex star, induced by the
cyclic permutation of the three outer colors. -/
def trialityStarPermutation : FourPlaneVertex ≃ FourPlaneVertex :=
  vertexPermutation trialityCyclePerm

@[simp] theorem trialityStarPermutation_outer (c : ColorChannel) :
    trialityStarPermutation (outerVertex c) =
      outerVertex (trialityPermute c) := rfl

@[simp] theorem trialityStarPermutation_centre :
    trialityStarPermutation centralVertex = centralVertex := rfl

theorem trialityStarPermutation_order_three (v : FourPlaneVertex) :
    trialityStarPermutation (trialityStarPermutation
      (trialityStarPermutation v)) = v := by
  cases v with
  | inl c =>
      cases c <;> rfl
  | inr _ =>
      rfl

theorem trialityStarPermutation_adj_iff (v w : FourPlaneVertex) :
    d4StarGraph.Adj v w ↔
      d4StarGraph.Adj (trialityStarPermutation v) (trialityStarPermutation w) := by
  cases v <;> cases w <;> simp [trialityStarPermutation, d4StarGraph, vertexPermutation, trialityCyclePerm]

theorem continuous_trialityStarPermutation :
    Continuous trialityStarPermutation := by
  exact continuous_of_discreteTopology

theorem continuous_trialityStarPermutation_inverse :
    Continuous trialityStarPermutation.symm := by
  exact continuous_of_discreteTopology

theorem trialityStarPermutation_preserves_centre :
    trialityStarPermutation centralVertex = centralVertex :=
  trialityStarPermutation_centre

theorem trialityStarPermutation_preserves_outer_orbit
    (c : ColorChannel) :
    trialityStarPermutation (outerVertex c) =
      outerVertex (trialityPermute c) :=
  trialityStarPermutation_outer c

end InfoGeometry.Topology.G2AutomorphismTrialityGroup
