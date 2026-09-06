import InfoGeometry.Canonical.PauliJungTrialityD4Synthesis

namespace InfoGeometry.Topology.PauliJungD4Star

open InfoGeometry.Canonical

/-!
Topological shadow of the finite D₄ star: the centre is fixed while a
permutation acts on the three outer vertices.  Since the vertex type is
finite, its canonical topology is discrete and every vertex permutation is
continuous.
-/

instance fourPlaneVertexTopologicalSpace : TopologicalSpace FourPlaneVertex := ⊥

instance fourPlaneVertexDiscreteTopology : DiscreteTopology FourPlaneVertex :=
  ⟨rfl⟩

def centralVertex : FourPlaneVertex := Sum.inr ()

def outerVertex (c : ColorChannel) : FourPlaneVertex := Sum.inl c

def vertexPermutation (σ : Equiv.Perm ColorChannel) :
    FourPlaneVertex ≃ FourPlaneVertex :=
  { toFun := fun v =>
      match v with
      | Sum.inl c => Sum.inl (σ c)
      | Sum.inr u => Sum.inr u
    invFun := fun v =>
      match v with
      | Sum.inl c => Sum.inl (σ.symm c)
      | Sum.inr u => Sum.inr u
    left_inv := by
      intro v
      cases v with
      | inl c => simp
      | inr u => rfl
    right_inv := by
      intro v
      cases v with
      | inl c => simp
      | inr u => rfl }

@[simp] theorem vertexPermutation_apply_outer
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    vertexPermutation σ (outerVertex c) = outerVertex (σ c) := rfl

@[simp] theorem vertexPermutation_apply_centre
    (σ : Equiv.Perm ColorChannel) :
    vertexPermutation σ centralVertex = centralVertex := rfl

theorem continuous_vertexPermutation
    (σ : Equiv.Perm ColorChannel) :
    Continuous (vertexPermutation σ) := by
  exact continuous_of_discreteTopology

theorem continuous_vertexPermutation_inverse
    (σ : Equiv.Perm ColorChannel) :
    Continuous (vertexPermutation σ).symm := by
  exact continuous_of_discreteTopology

theorem vertexPermutation_preserves_centre
    (σ : Equiv.Perm ColorChannel) :
    vertexPermutation σ centralVertex = centralVertex :=
  vertexPermutation_apply_centre σ

theorem vertexPermutation_preserves_outer_orbit
    (σ : Equiv.Perm ColorChannel) (c : ColorChannel) :
    vertexPermutation σ (outerVertex c) = outerVertex (σ c) :=
  vertexPermutation_apply_outer σ c

end InfoGeometry.Topology.PauliJungD4Star
