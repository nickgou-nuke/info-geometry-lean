import Mathlib
import InfoGeometry.Topology.SymbolicLatentSpace

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# TopCat readout of the symbolic latent observation map

This file exposes the native continuous observation map from
`SymbolicLatentSpace` as a morphism in `TopCat`.
It does not add any new quotient or algebraic structure.
-/

def symbolicObservationTopCatHom
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) :
    TopCat.of X ⟶ TopCat.of (ι → ℝ) :=
  TopCat.ofHom
    { toFun := symbolicObservationMap S
      continuous_toFun := continuous_symbolicObservationMap S }

theorem symbolicObservationTopCatHom_apply
    {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι]
    (S : FiniteSymbolicLatentSystem X ι) (x : X) :
    symbolicObservationTopCatHom S x = symbolicObservationMap S x :=
  rfl

end InfoGeometry.Topology
