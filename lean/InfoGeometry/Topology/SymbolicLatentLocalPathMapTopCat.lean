import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentLocalPathTopCat
import InfoGeometry.Topology.SymbolicLatentLocalPathMap

namespace InfoGeometry.Topology

open CategoryTheory

/-!
# `TopCat` transport of chart-local path images

The local chart map owner already constructs `mapPath`.  This file packages
the induced map on its image subtypes and records the ambient commuting
square.
-/

def SymbolicLatentLocalChartMap.mapPathImageTopCatHom
    {X Y κ : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) :
    TopCat.of (SymbolicLatentLocalPathImage γ) ⟶
      TopCat.of (SymbolicLatentLocalPathImage (F.mapPath γ hγ)) :=
  TopCat.ofHom
    { toFun := fun y =>
        ⟨F.toFun y.1, by
          rcases y.2 with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [← ht]
          exact (F.mapPath_apply γ hγ t).symm⟩
      continuous_toFun :=
        (F.continuous_toFun.comp continuous_subtype_val).subtype_mk _ }

theorem SymbolicLatentLocalChartMap.mapPathImageTopCatHom_apply
    {X Y κ : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart)
    (y : SymbolicLatentLocalPathImage γ) :
    F.mapPathImageTopCatHom γ hγ y =
      ⟨F.toFun y.1, by
        rcases y.2 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        rw [← ht]
        exact (F.mapPath_apply γ hγ t).symm⟩ :=
  rfl

theorem SymbolicLatentLocalChartMap.mapPathImageTopCatHom_factorization
    {X Y κ : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart) :
    F.mapPathImageTopCatHom γ hγ ≫
        (F.mapPath γ hγ).imageInclusionTopCatHom =
      γ.imageInclusionTopCatHom ≫
        TopCat.ofHom
          { toFun := F.toFun
            continuous_toFun := F.continuous_toFun } := by
  ext y
  rfl

theorem SymbolicLatentLocalChartMap.mapPathImageTopCatHom_factorization_unique
    {X Y κ : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [Fintype κ]
    {C : SymbolicLatentOpenCover X κ}
    {D : SymbolicLatentOpenCover Y κ}
    (F : SymbolicLatentLocalChartMap X Y κ (C := C) (D := D))
    (γ : SymbolicLatentLocalPath X κ C)
    (hγ : γ.chart = F.sourceChart)
    {u : TopCat.of (SymbolicLatentLocalPathImage γ) ⟶
      TopCat.of (SymbolicLatentLocalPathImage (F.mapPath γ hγ))}
    (hu : u ≫ (F.mapPath γ hγ).imageInclusionTopCatHom =
      γ.imageInclusionTopCatHom ≫
        TopCat.ofHom
          { toFun := F.toFun
            continuous_toFun := F.continuous_toFun }) :
    u = F.mapPathImageTopCatHom γ hγ := by
  apply TopCat.hom_ext
  ext y
  have hy : (u y).1 = F.toFun y.1 := by
    simpa [TopCat.comp_app, TopCat.ofHom] using
      congrArg (fun m => m y) hu
  simpa [SymbolicLatentLocalChartMap.mapPathImageTopCatHom] using hy

end InfoGeometry.Topology
