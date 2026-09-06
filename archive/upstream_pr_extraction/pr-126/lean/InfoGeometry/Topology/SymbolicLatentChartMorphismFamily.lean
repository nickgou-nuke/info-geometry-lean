import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamily
import InfoGeometry.Topology.SymbolicLatentChartMorphism

namespace InfoGeometry.Topology

/-!
Family-level transport for symbolic chart morphisms.  The defining
intertwining law is lifted pointwise from latent states to a jointly
continuous parameter-time family.
-/

def SymbolicLatentChartMorphism.mapPathFamily
    {P X Y : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    SymbolicLatentPathFamily P Y := {
  toFun := fun q => F.toFun (H q)
  continuous_toFun := F.continuous_toFun.comp H.continuous
}

theorem SymbolicLatentChartMorphism.mapPathFamily_apply
    {P X Y : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    F.mapPathFamily H q = F.toFun (H q) := rfl

theorem SymbolicLatentChartMorphism.mapPathFamily_observation
    {P X Y : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
      symbolicObservationMap D.system (F.mapPathFamily H q) =
      F.featureMap (symbolicObservationMap C.system (H q)) := by
  exact (F.intertwines (H q)).symm

theorem SymbolicLatentChartMorphism.mapPathFamily_slice_apply
    {P X Y : Type*} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type*} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X)
    (p : P) (t : SymbolicPathDomain) :
    (F.mapPathFamily H).slice p t = F.toFun (H (p, t)) := rfl

end InfoGeometry.Topology
