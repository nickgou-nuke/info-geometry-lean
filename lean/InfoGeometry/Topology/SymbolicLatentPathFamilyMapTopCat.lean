import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyMap
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport of jointly continuous symbolic-latent path families

The local-chart map owner already transports a family by composition.  This
file exposes that transport categorically and records its factorization
through the ambient latent map.
-/

def symbolicLatentLocalChartMapTopCatHom
    {X Y κ : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D)) :
    TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom
    { toFun := F.toFun
      continuous_toFun := F.continuous_toFun }

def symbolicLatentPathFamilyMapTopCatHom
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (P × SymbolicPathDomain) ⟶ TopCat.of Y :=
  symbolicLatentPathFamilyTopCatHom (F.mapFamily H)

theorem symbolicLatentPathFamilyMapTopCatHom_apply
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) (q : P × SymbolicPathDomain) :
    symbolicLatentPathFamilyMapTopCatHom F H q = F.toFun (H q) :=
  rfl

theorem symbolicLatentPathFamilyMapTopCatHom_factorization
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F =
      symbolicLatentPathFamilyMapTopCatHom F H := by
  ext q
  rfl

theorem symbolicLatentPathFamilyMapTopCatHom_factorization_unique
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    {u : TopCat.of (P × SymbolicPathDomain) ⟶ TopCat.of Y}
    (hu : symbolicLatentPathFamilyTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F =
      u) :
    u = symbolicLatentPathFamilyMapTopCatHom F H := by
  apply TopCat.hom_ext
  ext q
  have hq := congrArg (fun m => m q) hu
  simpa [symbolicLatentPathFamilyMapTopCatHom,
    symbolicLatentPathFamilyTopCatHom,
    symbolicLatentLocalChartMapTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hq.symm

theorem symbolicLatentPathFamilyMapTopCatHom_comp
    {P X Y Z κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (hFG : F.targetChart = G.sourceChart)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyMapTopCatHom F H ≫
        symbolicLatentLocalChartMapTopCatHom G =
      symbolicLatentPathFamilyMapTopCatHom (F.comp G hFG) H := by
  ext q
  rfl

@[simp] theorem symbolicLatentPathFamilyMapTopCatHom_comp_apply
    {P X Y Z κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (hFG : F.targetChart = G.sourceChart)
    (H : SymbolicLatentPathFamily P X)
    (q : P × SymbolicPathDomain) :
    (symbolicLatentPathFamilyMapTopCatHom F H ≫
        symbolicLatentLocalChartMapTopCatHom G) q =
      symbolicLatentPathFamilyMapTopCatHom (F.comp G hFG) H q := by
  simpa [CategoryTheory.comp_apply] using
    congrArg (fun h => h q)
      (symbolicLatentPathFamilyMapTopCatHom_comp F G hFG H)

theorem symbolicLatentPathFamilyMapStartTopCatHom_natural
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyStartTopCatHom (F.mapFamily H) =
      symbolicLatentPathFamilyStartTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F := by
  ext p
  rfl

theorem symbolicLatentPathFamilyMapFinishTopCatHom_natural
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyFinishTopCatHom (F.mapFamily H) =
      symbolicLatentPathFamilyFinishTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F := by
  ext p
  rfl

end InfoGeometry.Topology
