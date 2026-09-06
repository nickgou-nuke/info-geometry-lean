import Mathlib.Topology.Category.TopCat.Basic
import InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

/-!
# `TopCat` packaging for the finite D₄-star crossed-product generators

This owner keeps the finite crossed-product carrier at the topological level:
the coefficient space is the native function space, the permutation group is
treated as discrete, and the canonical observable and group-unitary generators
are exposed as continuous maps.

No completion, quotient identification, or spectral triple is claimed here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct

open CategoryTheory
open InfoGeometry.Canonical
open InfoGeometry.Topology.PauliJungD4Star

abbrev D4Perm := Equiv.Perm ColorChannel

instance crossedProductGroupTopologicalSpace :
    TopologicalSpace D4Perm := ⊥

instance crossedProductGroupDiscreteTopology :
    DiscreteTopology D4Perm :=
  ⟨rfl⟩

theorem continuous_observableEmbedding :
    Continuous observableEmbedding := by
  classical
  apply continuous_pi
  intro r
  by_cases hr : r = 1
  · simpa [observableEmbedding, hr] using
      (continuous_id : Continuous fun f : D4StarObservable => f)
  · simpa [observableEmbedding, hr] using
      (continuous_const : Continuous fun _ : D4StarObservable =>
        (0 : D4StarObservable))

def observableEmbeddingTopCatHom :
    TopCat.of D4StarObservable ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := observableEmbedding
      continuous_toFun := continuous_observableEmbedding }

@[simp] theorem observableEmbeddingTopCatHom_apply
    (f : D4StarObservable) :
    observableEmbeddingTopCatHom f = observableEmbedding f :=
  rfl

theorem continuous_groupUnitary :
    Continuous groupUnitary := by
  exact continuous_of_discreteTopology

def groupUnitaryTopCatHom
    :
    TopCat.of D4Perm ⟶ TopCat.of D4StarCrossedProduct :=
  TopCat.ofHom
    { toFun := groupUnitary
      continuous_toFun := continuous_groupUnitary }

@[simp] theorem groupUnitaryTopCatHom_apply
    (x : D4Perm) :
    groupUnitaryTopCatHom x = groupUnitary x :=
  rfl

end InfoGeometry.OperatorAlgebra.D4StarFiniteCrossedProduct
