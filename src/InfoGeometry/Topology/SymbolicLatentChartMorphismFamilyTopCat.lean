import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentChartMorphismFamily
import InfoGeometry.Topology.SymbolicLatentChartMorphismTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport for chart-morphism path families

This is the categorical surface of `mapPathFamily`.  The underlying owner
already contains the continuity and pointwise observation intertwining; this
file only exposes those facts as native `TopCat` morphisms.
-/

def SymbolicLatentChartMorphism.mapPathFamilyTopCatHom
    {P X Y : Type} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (P × SymbolicPathDomain) ⟶ TopCat.of Y :=
  symbolicLatentPathFamilyTopCatHom (F.mapPathFamily H)

theorem SymbolicLatentChartMorphism.mapPathFamilyTopCatHom_apply
    {P X Y : Type} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    F.mapPathFamilyTopCatHom H q = F.toFun (H q) :=
  rfl

theorem SymbolicLatentChartMorphism.mapPathFamilyTopCatHom_factorization
    {P X Y : Type} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyTopCatHom H ≫ F.toFunTopCatHom =
      F.mapPathFamilyTopCatHom H := by
  ext q
  rfl

theorem SymbolicLatentChartMorphism.mapPathFamily_feature_intertwining_topCat
    {P X Y : Type} [TopologicalSpace P]
    [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} [Fintype ι]
    {C : SymbolicLatentChart X ι}
    {D : SymbolicLatentChart Y ι}
    (F : SymbolicLatentChartMorphism C D)
    (H : SymbolicLatentPathFamily P X) :
    F.mapPathFamilyTopCatHom H ≫ D.observationTopCatHom =
      symbolicLatentPathFamilyTopCatHom H ≫ C.observationTopCatHom ≫
        F.featureMapTopCatHom := by
  apply TopCat.hom_ext
  ext q i
  exact congrFun (F.mapPathFamily_observation H q) i

end InfoGeometry.Topology
