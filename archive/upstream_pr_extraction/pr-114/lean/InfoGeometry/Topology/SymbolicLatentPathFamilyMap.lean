import Mathlib
import InfoGeometry.Topology.SymbolicLatentLocalPathMap

namespace InfoGeometry.Topology

/-!
Transport of jointly continuous path families through a continuous local-chart
map.  The map is total as a function, while chart-domain preservation remains
available separately through `SymbolicLatentLocalChartMap.map_domain`.
-/

def SymbolicLatentLocalChartMap.mapFamily
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    SymbolicLatentPathFamily P Y := {
  toFun := fun q => F.toFun (H q)
  continuous_toFun := F.continuous_toFun.comp H.continuous
}

theorem SymbolicLatentLocalChartMap.mapFamily_apply
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) (q : P × SymbolicPathDomain) :
    F.mapFamily H q = F.toFun (H q) := rfl

theorem SymbolicLatentLocalChartMap.mapFamily_slice_apply
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    (p : P) (t : SymbolicPathDomain) :
    (F.mapFamily H).slice p t = F.toFun (H (p, t)) := rfl

theorem SymbolicLatentLocalChartMap.mapFamily_startFamily_apply
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) (p : P) :
    (F.mapFamily H).startFamily p = F.toFun (H.startFamily p) := rfl

theorem SymbolicLatentLocalChartMap.mapFamily_finishFamily_apply
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) (p : P) :
    (F.mapFamily H).finishFamily p = F.toFun (H.finishFamily p) := rfl

theorem SymbolicLatentLocalChartMap.mapFamily_inTargetDomain
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    (hH : H.InRegion (C.domain F.sourceChart))
    (p : P) (t : SymbolicPathDomain) :
    (F.mapFamily H) (p, t) ∈ D.domain F.targetChart := by
  exact F.map_domain (H (p, t)) (hH p t)

theorem SymbolicLatentLocalChartMap.mapFamilyImage_subset_targetDomain
    {P X Y κ : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    (hH : H.InRegion (C.domain F.sourceChart)) :
    symbolicLatentPathFamilyImage (F.mapFamily H) ⊆
      D.domain F.targetChart := by
  intro y hy
  rcases hy with ⟨⟨p, t⟩, rfl⟩
  exact F.mapFamily_inTargetDomain H hH p t

end InfoGeometry.Topology
