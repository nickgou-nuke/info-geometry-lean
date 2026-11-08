import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.SymbolicLatentPathFamilyTopCatColimit
import InfoGeometry.Topology.SymbolicLatentPathFamilyReparametrizationTopCat

namespace InfoGeometry.Topology

open CategoryTheory CategoryTheory.Limits
open SymbolicLatentPathFamilyTopCatColimit
open SpinorSpectrumTopCatColimit

noncomputable section

variable {P X ι : Type} [TopologicalSpace P] [TopologicalSpace X]
  [Fintype ι]

def symbolicLatentPathFamilyDiagramParameterReparametrizationHom
    (R : SymbolicLatentPathReparametrization) :
    (symbolicLatentPathFamilyTopCatDiagram (P := P)).obj .extended ⟶
      (symbolicLatentPathFamilyTopCatDiagram (P := P)).obj .extended :=
  { hom' :=
      { toFun := fun q => (q.1, R.parameter q.2)
        continuous_toFun := by
          change Continuous (fun q : P × SymbolicPathDomain =>
            (q.1, R.parameter q.2))
          exact continuous_fst.prodMk
            (R.parameter.continuous.comp continuous_snd) } }

theorem symbolicLatentPathFamilyDiagramParameterReparametrizationHom_identity :
    symbolicLatentPathFamilyDiagramParameterReparametrizationHom
        (P := P) identitySymbolicLatentPathReparametrization =
      𝟙 ((symbolicLatentPathFamilyTopCatDiagram (P := P)).obj .extended) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

theorem symbolicLatentPathFamilyDiagramParameterReparametrizationHom_comp
    (R S : SymbolicLatentPathReparametrization) :
    symbolicLatentPathFamilyDiagramParameterReparametrizationHom
        (P := P) (composeSymbolicLatentPathReparametrization R S) =
      symbolicLatentPathFamilyDiagramParameterReparametrizationHom (P := P) R ≫
        symbolicLatentPathFamilyDiagramParameterReparametrizationHom (P := P) S := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

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
              symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
                colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended
        naturality := by
          intro i j g
          change SpinorStage.Hom i j at g
          cases g with
          | idInitial => rfl
          | idExtended => rfl
          | step =>
              change (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                  SpinorStage.Hom.step ≫
                    (symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
                      colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P))
                        SpinorStage.extended) =
                colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P))
                  SpinorStage.initial
              have hparameter :
                  (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                      SpinorStage.Hom.step ≫
                    symbolicLatentPathFamilyDiagramParameterReparametrizationHom R =
                (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                    SpinorStage.Hom.step := by
                apply TopCat.hom_ext
                apply ContinuousMap.ext
                intro p
                change (p, R.parameter 0) = (p, 0)
                rw [R.at_zero]
              calc
                _ = (symbolicLatentPathFamilyTopCatDiagram (P := P)).map
                      SpinorStage.Hom.step ≫
                    colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P))
                      SpinorStage.extended := by
                    exact (reassoc_of% hparameter)
                      (colimit.ι
                        (symbolicLatentPathFamilyTopCatDiagram (P := P))
                        SpinorStage.extended)
                _ = colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P))
                      SpinorStage.initial :=
                    colimit.w
                      (symbolicLatentPathFamilyTopCatDiagram (P := P))
                      SpinorStage.Hom.step }
  }

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
      symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
        colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended := by
  change colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended ≫
      symbolicLatentPathFamilyReparametrizationColimitHom R =
    symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
      colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended
  exact symbolicLatentPathFamilyReparametrizationColimitHom_stage
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
        symbolicLatentPathFamilyTopCatColimitReadout_stage
          (S := S) (H := H) (h_obs := h_obs) .extended,
        symbolicLatentPathFamilyTopCatColimitReadout_stage
          (S := S) (H := reparametrizeSymbolicLatentPathFamily R H)
          (h_obs := h_obs) .extended]
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
        symbolicLatentPathFamilyDiagramParameterReparametrizationHom_identity]
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
      calc
        _ =
            (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended ≫
              symbolicLatentPathFamilyReparametrizationColimitHom R) ≫
              symbolicLatentPathFamilyReparametrizationColimitHom S :=
          Category.assoc _ _ _
        _ =
            (symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
              colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended) ≫
              symbolicLatentPathFamilyReparametrizationColimitHom S :=
          congrArg (fun f => f ≫ symbolicLatentPathFamilyReparametrizationColimitHom S)
            (symbolicLatentPathFamilyReparametrizationColimitHom_extended
              (P := P) R)
        _ = symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
              (colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended ≫
                symbolicLatentPathFamilyReparametrizationColimitHom S) :=
          Category.assoc _ _ _
        _ = symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
              (symbolicLatentPathFamilyDiagramParameterReparametrizationHom S ≫
                colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended) :=
          congrArg (fun f => symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫ f)
            (symbolicLatentPathFamilyReparametrizationColimitHom_extended
              (P := P) S)
        _ = (symbolicLatentPathFamilyDiagramParameterReparametrizationHom R ≫
              symbolicLatentPathFamilyDiagramParameterReparametrizationHom S) ≫
              colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended :=
          (Category.assoc _ _ _).symm
        _ = symbolicLatentPathFamilyDiagramParameterReparametrizationHom
              (composeSymbolicLatentPathReparametrization R S) ≫
              colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended :=
          congrArg (fun f => f ≫ colimit.ι
            (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended)
            (symbolicLatentPathFamilyDiagramParameterReparametrizationHom_comp
              (P := P) R S).symm
        _ = colimit.ι (symbolicLatentPathFamilyTopCatDiagram (P := P)) .extended ≫
              symbolicLatentPathFamilyReparametrizationColimitHom
                (composeSymbolicLatentPathReparametrization R S) :=
          (symbolicLatentPathFamilyReparametrizationColimitHom_extended
            (P := P) (composeSymbolicLatentPathReparametrization R S)).symm

end

end InfoGeometry.Topology
