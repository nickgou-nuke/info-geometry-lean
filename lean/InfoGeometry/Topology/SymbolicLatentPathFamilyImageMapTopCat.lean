import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamilyImageTopCat
import InfoGeometry.Topology.SymbolicLatentPathFamilyMapTopCat

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# Transport on path-family image subtypes

The image of a transported family receives a canonical map from the image of
the original family.  No injectivity is assumed here; the map is simply the
restriction of the continuous latent map, with its range property carried
along explicitly.
-/

def symbolicLatentPathFamilyImageMap
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImage H →
      symbolicLatentPathFamilyImage (F.mapFamily H) :=
  fun y =>
    ⟨F.toFun y.1, by
      rcases y.2 with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      rw [← hq]
      rfl⟩

theorem symbolicLatentPathFamilyImageMap_apply
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage H) :
    (symbolicLatentPathFamilyImageMap F H y).1 = F.toFun y.1 :=
  rfl

def symbolicLatentPathFamilyImageMapTopCatHom
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of (symbolicLatentPathFamilyImage H) ⟶
      TopCat.of (symbolicLatentPathFamilyImage (F.mapFamily H)) :=
  TopCat.ofHom
    { toFun := symbolicLatentPathFamilyImageMap F H
      continuous_toFun :=
        (F.continuous_toFun.comp continuous_subtype_val).subtype_mk _ }

theorem symbolicLatentPathFamilyImageEvaluation_map_factorization
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageEvaluationTopCatHom H ≫
        symbolicLatentPathFamilyImageMapTopCatHom F H =
      symbolicLatentPathFamilyImageEvaluationTopCatHom (F.mapFamily H) := by
  ext q
  rfl

def symbolicLatentPathFamilyImageStartTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of P ⟶ TopCat.of (symbolicLatentPathFamilyImage H) :=
  symbolicLatentPathFamilyStartParameterTopCatHom P ≫
    symbolicLatentPathFamilyImageEvaluationTopCatHom H

def symbolicLatentPathFamilyImageFinishTopCatHom
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    TopCat.of P ⟶ TopCat.of (symbolicLatentPathFamilyImage H) :=
  symbolicLatentPathFamilyFinishParameterTopCatHom P ≫
    symbolicLatentPathFamilyImageEvaluationTopCatHom H

theorem symbolicLatentPathFamilyImageStart_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageStartTopCatHom H ≫
        symbolicLatentPathFamilyImageInclusionTopCatHom H =
      symbolicLatentPathFamilyStartTopCatHom H := by
  ext p
  rfl

theorem symbolicLatentPathFamilyImageFinish_factorization
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageFinishTopCatHom H ≫
        symbolicLatentPathFamilyImageInclusionTopCatHom H =
      symbolicLatentPathFamilyFinishTopCatHom H := by
  ext p
  rfl

theorem symbolicLatentPathFamilyImageMap_start_natural
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageStartTopCatHom H ≫
        symbolicLatentPathFamilyImageMapTopCatHom F H =
      symbolicLatentPathFamilyImageStartTopCatHom (F.mapFamily H) := by
  ext p
  rfl

theorem symbolicLatentPathFamilyImageMap_finish_natural
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageFinishTopCatHom H ≫
        symbolicLatentPathFamilyImageMapTopCatHom F H =
      symbolicLatentPathFamilyImageFinishTopCatHom (F.mapFamily H) := by
  ext p
  rfl

theorem symbolicLatentPathFamilyImageMap_inclusion_natural
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageMapTopCatHom F H ≫
        symbolicLatentPathFamilyImageInclusionTopCatHom (F.mapFamily H) =
      symbolicLatentPathFamilyImageInclusionTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F := by
  ext y
  rfl

theorem symbolicLatentPathFamilyImageMapTopCatHom_comp
    {P X Y Z κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (hFG : F.targetChart = G.sourceChart)
    (H : SymbolicLatentPathFamily P X) :
    symbolicLatentPathFamilyImageMapTopCatHom F H ≫
        symbolicLatentPathFamilyImageMapTopCatHom G (F.mapFamily H) =
      symbolicLatentPathFamilyImageMapTopCatHom (F.comp G hFG) H := by
  ext y
  rfl

theorem symbolicLatentPathFamilyImageMapTopCatHom_comp_apply
    {P X Y Z κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    {E : SymbolicLatentOpenCover Z κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (G : SymbolicLatentLocalChartMap Y Z κ (C := D) (D := E))
    (hFG : F.targetChart = G.sourceChart)
    (H : SymbolicLatentPathFamily P X)
    (y : symbolicLatentPathFamilyImage H) :
    (symbolicLatentPathFamilyImageMapTopCatHom F H ≫
        symbolicLatentPathFamilyImageMapTopCatHom G (F.mapFamily H)) y =
      symbolicLatentPathFamilyImageMapTopCatHom (F.comp G hFG) H y := by
  rfl

theorem symbolicLatentPathFamilyImageMapTopCatHom_factorization_unique
    {P X Y κ : Type} [TopologicalSpace P] [TopologicalSpace X]
    [TopologicalSpace Y] [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (H : SymbolicLatentPathFamily P X)
    {u : TopCat.of (symbolicLatentPathFamilyImage H) ⟶
      TopCat.of (symbolicLatentPathFamilyImage (F.mapFamily H))}
    (hu : u ≫ symbolicLatentPathFamilyImageInclusionTopCatHom
        (F.mapFamily H) =
      symbolicLatentPathFamilyImageInclusionTopCatHom H ≫
        symbolicLatentLocalChartMapTopCatHom F) :
    u = symbolicLatentPathFamilyImageMapTopCatHom F H := by
  apply TopCat.hom_ext
  ext y
  have hy := congrArg (fun m => m y) hu
  simpa [symbolicLatentPathFamilyImageMapTopCatHom,
    symbolicLatentPathFamilyImageInclusionTopCatHom,
    symbolicLatentLocalChartMapTopCatHom,
    TopCat.comp_app, TopCat.ofHom] using hy

end InfoGeometry.Topology
