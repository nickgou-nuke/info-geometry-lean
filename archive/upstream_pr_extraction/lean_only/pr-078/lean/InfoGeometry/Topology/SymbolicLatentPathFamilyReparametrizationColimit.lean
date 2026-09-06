import Mathlib
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationTopCat

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentPathFamilyTopCatColimit
open SpinorSpectrumTopCatColimit

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι]

/-!
# Reparametrization on the corridor colimit

An endpoint-preserving reparametrization need not be invertible.  The honest
categorical object is therefore the endomorphism of the two-stage colimit
induced by the identity on the initial stage and by the parameter map on the
extended stage.
-/

noncomputable def symbolicLatentPathFamilyReparametrizationColimitCocone
    (R : SymbolicLatentPathReparametrization) :
    Cocone (symbolicLatentPathFamilyTopCatDiagram (P := P)) :=
  { pt := symbolicLatentPathFamilyTopCatColimit (P := P)
    ι :=
      { app := fun i => match i with
          | .initial =>
              colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .initial
          | .extended =>
              symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
                colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended
        naturality := by
          intro i j g
          change SpinorStage.Hom i j at g
          cases g with
          | idInitial => rfl
          | idExtended => rfl
          | step =>
              have hparameter :
                  (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                      SpinorStage.Hom.step ≫
                    symbolicLatentPathFamilyParameterReparametrizationTopCatHom R =
                (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                    SpinorStage.Hom.step := by
                apply TopCat.hom_ext
                apply ContinuousMap.ext
                intro p
                change (p, R.parameter 0) = (p, 0)
                rw [R.at_zero]
              rw [← Category.assoc, hparameter]
              exact colimit.w
                (symbolicLatentPathFamilyTopCatDiagram (P := P))
                SpinorStage.Hom.step } }

noncomputable def symbolicLatentPathFamilyReparametrizationColimitHom
    (R : SymbolicLatentPathReparametrization) :
    symbolicLatentPathFamilyTopCatColimit (P := P) ⟶
      symbolicLatentPathFamilyTopCatColimit (P := P) :=
  colimit.desc (symbolicLatentPathFamilyTopCatDiagram (P := P))
    (symbolicLatentPathFamilyReparametrizationColimitCocone R)

theorem symbolicLatentPathFamilyReparametrizationColimitHom_stage
    (R : SymbolicLatentPathReparametrization)
    (i : SpinorStage) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) i ≫
        symbolicLatentPathFamilyReparametrizationColimitHom R =
      (symbolicLatentPathFamilyReparametrizationColimitCocone R).ι.app i :=
  colimit.ι_desc
    (symbolicLatentPathFamilyReparametrizationColimitCocone R) i

theorem symbolicLatentPathFamilyReparametrizationColimitHom_initial
    (R : SymbolicLatentPathReparametrization) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .initial ≫
        symbolicLatentPathFamilyReparametrizationColimitHom R =
      colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .initial := by
  simpa [symbolicLatentPathFamilyReparametrizationColimitCocone] using
    symbolicLatentPathFamilyReparametrizationColimitHom_stage
      (P := P) R .initial

theorem symbolicLatentPathFamilyReparametrizationColimitHom_extended
    (R : SymbolicLatentPathReparametrization) :
    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended ≫
        symbolicLatentPathFamilyReparametrizationColimitHom R =
      symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
        colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended := by
  simpa [symbolicLatentPathFamilyReparametrizationColimitCocone] using
    symbolicLatentPathFamilyReparametrizationColimitHom_stage
      (P := P) R .extended

theorem symbolicLatentPathFamilyReparametrizationColimitReadout_natural
    {S : FiniteSymbolicLatentSystem X ι}
    (R : SymbolicLatentPathReparametrization)
    (H : SymbolicLatentPathFamily P X)
    (h_obs : Continuous (symbolicObservationMap S)) :
    symbolicLatentPathFamilyReparametrizationColimitHom R ≫
        symbolicLatentPathFamilyTopCatColimitReadout S H h_obs =
      symbolicLatentPathFamilyTopCatColimitReadout S
        (reparametrizeSymbolicLatentPathFamily R H) h_obs := by
  apply colimit.hom_ext
  intro i
  cases i with
  | initial =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_initial,
        symbolicLatentPathFamilyTopCatColimitReadout_stage,
        symbolicLatentPathFamilyTopCatColimitReadout_stage]
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      change symbolicObservationMap S (H (p, 0)) =
        symbolicObservationMap S (H (p, R.parameter 0))
      rw [R.at_zero]
  | extended =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_extended,
        Category.assoc,
        symbolicLatentPathFamilyTopCatColimitReadout_stage,
        symbolicLatentPathFamilyTopCatColimitReadout_stage]
      change symbolicLatentPathFamilyParameterReparametrizationTopCatHom R ≫
          observedSymbolicLatentPathFamilyTopCatHom S H h_obs =
        observedSymbolicLatentPathFamilyTopCatHom S
          (reparametrizeSymbolicLatentPathFamily R H) h_obs
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro q
      rfl

theorem symbolicLatentPathFamilyReparametrizationColimitHom_identity :
    symbolicLatentPathFamilyReparametrizationColimitHom
        identitySymbolicLatentPathReparametrization =
      𝟙 (symbolicLatentPathFamilyTopCatColimit (P := P)) := by
  apply colimit.hom_ext
  intro i
  cases i with
  | initial =>
      rw [symbolicLatentPathFamilyReparametrizationColimitHom_initial]
      exact (Category.comp_id _).symm
  | extended =>
      rw [symbolicLatentPathFamilyReparametrizationColimitHom_extended,
        symbolicLatentPathFamilyParameterReparametrizationTopCatHom_identity]
      exact (Category.comp_id _).symm

theorem symbolicLatentPathFamilyReparametrizationColimitHom_comp
    (R S : SymbolicLatentPathReparametrization) :
    symbolicLatentPathFamilyReparametrizationColimitHom (P := P) R ≫
        symbolicLatentPathFamilyReparametrizationColimitHom (P := P) S =
      symbolicLatentPathFamilyReparametrizationColimitHom (P := P)
        (composeSymbolicLatentPathReparametrization R S) := by
  apply colimit.hom_ext
  intro i
  cases i with
  | initial =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_initial,
        symbolicLatentPathFamilyReparametrizationColimitHom_initial,
        symbolicLatentPathFamilyReparametrizationColimitHom_initial]
  | extended =>
      rw [← Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_extended,
        Category.assoc,
        symbolicLatentPathFamilyReparametrizationColimitHom_extended,
        ← Category.assoc,
        ← symbolicLatentPathFamilyParameterReparametrizationTopCatHom_comp,
        symbolicLatentPathFamilyReparametrizationColimitHom_extended]

end

end InfoGeometry.Topology
