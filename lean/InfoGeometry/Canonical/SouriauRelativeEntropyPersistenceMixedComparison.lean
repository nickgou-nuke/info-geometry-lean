import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceBifiltration
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropyPersistenceMixedComparison

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff
open SouriauRelativeEntropyPersistenceCutoffFunctor
open SouriauRelativeEntropyPersistenceCutoffLimit
open SouriauRelativeEntropyPersistenceBifiltration

/-- The cutoff-colimit system, pulled back over the cutoff-time grid. -/
noncomputable def relativeEntropyCutoffColimitGrid
    (n : ℕ) : (ℝᵒᵖ × ℝ) ⥤ TopCat where
  obj I :=
    TopCat.of
      (RelativeEntropyPersistenceColimit (n := n) I.1.unop)
  map {I J} h :=
    TopCat.ofHom
      (relativeEntropyPersistenceCutoffColimitMap
        (leOfHom h.1.unop))
  map_id I := by
    exact
      relativeEntropyPersistenceCutoffColimitMap_refl_hom
        (n := n) I.1.unop
  map_comp {I J K} hIJ hJK := by
    exact
      (relativeEntropyPersistenceCutoffColimitMap_trans_hom
        (n := n) (leOfHom hJK.1.unop)
          (leOfHom hIJ.1.unop)).symm

/-- Finite bifiltration stages map naturally into their time colimits. -/
noncomputable def relativeEntropyBifiltrationToCutoffColimit
    (n : ℕ) :
    relativeEntropyCutoffTimeBifiltration n ⟶
      relativeEntropyCutoffColimitGrid n where
  app I :=
    TopCat.ofHom
      (relativeEntropyPersistenceColimitStage
        I.1.unop I.2)
  naturality := by
    intro I J h
    apply TopCat.hom_ext
    ext x
    exact
      (relativeEntropyCutoffTime_to_colimit
        (leOfHom h.1.unop) (leOfHom h.2) x).symm

@[simp] theorem relativeEntropyBifiltrationToCutoffColimit_app_apply
    (n : ℕ) (I : ℝᵒᵖ × ℝ)
    (x : (relativeEntropyCutoffTimeBifiltration n).obj I) :
    (relativeEntropyBifiltrationToCutoffColimit n).app I x =
      relativeEntropyPersistenceColimitStage
        I.1.unop I.2 x := by
  rfl

/-- The global cutoff inverse limit projects naturally to the cutoff-colimit grid. -/
noncomputable def relativeEntropyCutoffLimitToColimitGrid
    (n : ℕ) :
    (Functor.const (ℝᵒᵖ × ℝ)).obj
        (TopCat.of (RelativeEntropyPersistenceCutoffLimit n)) ⟶
      relativeEntropyCutoffColimitGrid n where
  app I :=
    TopCat.ofHom
      (relativeEntropyPersistenceCutoffLimitProjection
        n I.1.unop)
  naturality := by
    intro I J h
    apply TopCat.hom_ext
    ext x
    exact
      (relativeEntropyPersistenceCutoffLimitProjection_compat
        n (leOfHom h.1.unop) x).symm

@[simp] theorem relativeEntropyCutoffLimitToColimitGrid_app_apply
    (n : ℕ) (I : ℝᵒᵖ × ℝ)
    (x : RelativeEntropyPersistenceCutoffLimit n) :
    (relativeEntropyCutoffLimitToColimitGrid n).app I x =
      relativeEntropyPersistenceCutoffLimitProjection
        n I.1.unop x := by
  rfl

end SouriauRelativeEntropyPersistenceMixedComparison
