import InfoGeometry.Topology.SpinorSpectrumTopCatColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentObservedFamilyTopCat

/-!
# `TopCat` colimit for a symbolic-latent path-family corridor

This file uses Mathlib's native `TopCat` colimit API for the symbolic-latent
parameter corridor and records the observed path-family readout.
-/

namespace InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Topology
open InfoGeometry.Topology.SpinorSpectrumTopCatColimit

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
variable [Fintype ι]
variable (S : FiniteSymbolicLatentSystem X ι)
variable (H : SymbolicLatentPathFamily P X)
variable (h_obs : Continuous (symbolicObservationMap S))

/-- The `TopCat` diagram for the symbolic-latent corridor. -/
def symbolicLatentPathFamilyTopCatDiagram : SpinorStage ⥤ TopCat :=
  SpinorSpectrumTopCatColimit.spinorSpectrumTopCatDiagram
    P (P × SymbolicPathDomain)
    (fun p => (p, 0))
    (continuous_id.prodMk continuous_const)

/-- The target `TopCat` constant diagram for the observed feature space. -/
def symbolicLatentPathFamilyTopCatTarget
    (ι : Type) [Fintype ι] : SpinorStage ⥤ TopCat :=
  (Functor.const SpinorStage).obj (TopCat.of (SymbolicFeatureSpace ι))

/-- The categorical colimit of the corridor diagram. -/
noncomputable def symbolicLatentPathFamilyTopCatColimit : TopCat :=
  colimit (symbolicLatentPathFamilyTopCatDiagram (P := P))

/-- The observed path-family readout as a cocone over the corridor diagram. -/
def symbolicLatentPathFamilyTopCatReadout
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyTopCatDiagram (P := P) ⟶
      symbolicLatentPathFamilyTopCatTarget (ι := ι) where
  app
    | .initial => observedSymbolicLatentPathFamilyStartTopCatHom
        (S := S) (H := H) h_obs
    | .extended => observedSymbolicLatentPathFamilyTopCatHom
        (S := S) (H := H) h_obs
  naturality := by
    intro i j g
    change SpinorStage.Hom i j at g
    cases g with
    | idInitial =>
        rfl
    | idExtended =>
        rfl
    | step =>
        simpa [symbolicLatentPathFamilyTopCatDiagram,
          symbolicLatentPathFamilyTopCatTarget] using
          observedSymbolicLatentPathFamily_start_natural
          (S := S) (H := H) h_obs

/-- The induced colimit readout into the feature space. -/
noncomputable def symbolicLatentPathFamilyTopCatColimitReadout
    (S : FiniteSymbolicLatentSystem X ι)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      TopCat.of (SymbolicFeatureSpace ι) :=
  colimit.desc (symbolicLatentPathFamilyTopCatDiagram (P := P))
    { pt := TopCat.of (SymbolicFeatureSpace ι)
      ι := symbolicLatentPathFamilyTopCatReadout S H h_obs }

theorem symbolicLatentPathFamilyTopCatColimitReadout_stage
    (i : SpinorStage) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        symbolicLatentPathFamilyTopCatColimitReadout S H h_obs =
      (symbolicLatentPathFamilyTopCatReadout S H h_obs).app i := by
  exact colimit.ι_desc
    { pt := TopCat.of (SymbolicFeatureSpace ι)
      ι := symbolicLatentPathFamilyTopCatReadout S H h_obs } i

theorem symbolicLatentPathFamilyTopCatColimitReadout_unique
    {u v : symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      TopCat.of (SymbolicFeatureSpace ι)}
    (h : ∀ i : SpinorStage,
      colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ u =
        colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫ v) :
    u = v := by
  apply colimit.hom_ext
  intro i
  exact h i

/-- Stagewise commuting squares descend through the categorical colimit. -/
theorem colimit_desc_comp_of_stage
    {J : Type} [Category J]
    {D : J ⥤ TopCat} {Y : TopCat}
    (r s : D ⟶ (Functor.const J).obj Y)
    (u : Y ⟶ Y)
    (h : ∀ j, r.app j ≫ u = s.app j) :
    colimit.desc D { pt := Y, ι := r } ≫ u =
      colimit.desc D { pt := Y, ι := s } := by
  apply colimit.hom_ext
  intro j
  calc
    colimit.ι D j ≫ colimit.desc D { pt := Y, ι := r } ≫ u
        = r.app j ≫ u := by
          rw [← Category.assoc, colimit.ι_desc]
    _ = s.app j := h j
    _ = colimit.ι D j ≫ colimit.desc D { pt := Y, ι := s } := by
          rw [colimit.ι_desc]

theorem colimit_desc_comp_of_stage_apply
    {J : Type} [Category J]
    {D : J ⥤ TopCat} {Y : TopCat}
    (r s : D ⟶ (Functor.const J).obj Y)
    (u : Y ⟶ Y)
    (h : ∀ j, r.app j ≫ u = s.app j)
    (x : ↑(colimit D)) :
    (colimit.desc D { pt := Y, ι := r } ≫ u) x =
      (colimit.desc D { pt := Y, ι := s }) x := by
  exact congrArg (fun m => m x) (colimit_desc_comp_of_stage
    (D := D) (Y := Y) r s u h)

end InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
