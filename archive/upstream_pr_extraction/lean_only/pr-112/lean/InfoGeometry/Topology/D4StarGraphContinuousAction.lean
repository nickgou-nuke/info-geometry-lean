import InfoGeometry.Topology.PauliJungD4StarTopology

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-!
## The finite D₄ star as a topological graph shadow

The relation below is the incidence relation of one centre and three arms.
It is deliberately stated independently of a particular graph API: this
keeps the topological result reusable by later graph and quotient owners.
-/

def starAdjacent : FourPlaneVertex → FourPlaneVertex → Prop
  | Sum.inr _, Sum.inl _ => True
  | Sum.inl _, Sum.inr _ => True
  | _, _ => False

theorem starAdjacent_symmetric (v w : FourPlaneVertex) :
    starAdjacent v w ↔ starAdjacent w v := by
  cases v <;> cases w <;> simp [starAdjacent]

def PreservesStarAdjacency (e : FourPlaneVertex ≃ FourPlaneVertex) : Prop :=
  ∀ v w, starAdjacent v w ↔ starAdjacent (e v) (e w)

theorem vertexPermutation_preserves_starAdjacency
    (σ : Equiv.Perm ColorChannel) :
    PreservesStarAdjacency (vertexPermutation σ) := by
  intro v w
  cases v <;> cases w <;> simp [PreservesStarAdjacency, starAdjacent,
    vertexPermutation]

structure ContinuousStarGraphAction where
  map : FourPlaneVertex ≃ₜ FourPlaneVertex
  preserves_adjacency : PreservesStarAdjacency map

def vertexPermutationHomeomorph (σ : Equiv.Perm ColorChannel) :
    FourPlaneVertex ≃ₜ FourPlaneVertex where
  toEquiv := vertexPermutation σ
  continuous_toFun := continuous_vertexPermutation σ
  continuous_invFun := continuous_vertexPermutation_inverse σ

def colorPermutationStarAction (σ : Equiv.Perm ColorChannel) :
    ContinuousStarGraphAction :=
  { map := vertexPermutationHomeomorph σ
    preserves_adjacency := vertexPermutation_preserves_starAdjacency σ }

@[simp] theorem colorPermutationStarAction_centre
    (σ : Equiv.Perm ColorChannel) :
    (colorPermutationStarAction σ).map centralVertex = centralVertex :=
  vertexPermutation_preserves_centre σ

theorem colorPermutationStarAction_outer
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    (colorPermutationStarAction σ).map (outerVertex c) =
      outerVertex (σ c) :=
  vertexPermutation_preserves_outer_orbit σ c

end InfoGeometry.Topology.PauliJungD4Star
