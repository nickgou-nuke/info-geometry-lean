import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceCutoff
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropyPersistenceCutoffFunctor

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceColimit
open SouriauRelativeEntropyPersistenceCutoff

variable {n : ℕ}

theorem relativeEntropyPersistenceCutoffColimitMap_refl_hom
    (ε : ℝ) :
    TopCat.ofHom
        (relativeEntropyPersistenceCutoffColimitMap
          (n := n) (le_refl ε)) =
      𝟙 (colimit (relativeEntropyPersistenceRay (n := n) ε)) := by
  apply colimit.hom_ext
  intro t
  apply TopCat.hom_ext
  ext x
  change
    relativeEntropyPersistenceCutoffColimitMap (le_refl ε)
        (relativeEntropyPersistenceColimitStage ε t x) =
      relativeEntropyPersistenceColimitStage ε t x
  rw [relativeEntropyPersistenceCutoffColimitMap_stage]
  rw [relativeEntropyCutoffQuotientMap_refl]

theorem relativeEntropyPersistenceCutoffColimitMap_trans_hom
    {ε₁ ε₂ ε₃ : ℝ} (h₁₂ : ε₁ ≤ ε₂) (h₂₃ : ε₂ ≤ ε₃) :
    TopCat.ofHom
        (relativeEntropyPersistenceCutoffColimitMap
          (n := n) h₂₃) ≫
      TopCat.ofHom
        (relativeEntropyPersistenceCutoffColimitMap
          (n := n) h₁₂) =
      TopCat.ofHom
        (relativeEntropyPersistenceCutoffColimitMap
          (n := n) (h₁₂.trans h₂₃)) := by
  apply colimit.hom_ext
  intro t
  apply TopCat.hom_ext
  ext x
  change
    relativeEntropyPersistenceCutoffColimitMap h₁₂
        (relativeEntropyPersistenceCutoffColimitMap h₂₃
          (relativeEntropyPersistenceColimitStage ε₃ t x)) =
      relativeEntropyPersistenceCutoffColimitMap
        (h₁₂.trans h₂₃)
        (relativeEntropyPersistenceColimitStage ε₃ t x)
  rw [relativeEntropyPersistenceCutoffColimitMap_stage]
  rw [relativeEntropyPersistenceCutoffColimitMap_stage]
  rw [relativeEntropyPersistenceCutoffColimitMap_stage]
  rw [relativeEntropyCutoffQuotientMap_trans]

/-- Persistence colimits form a contravariant topological functor in the cutoff. -/
noncomputable def relativeEntropyPersistenceCutoffFunctor
    (n : ℕ) : ℝᵒᵖ ⥤ TopCat where
  obj ε :=
    TopCat.of
      (RelativeEntropyPersistenceColimit (n := n) ε.unop)
  map {ε₂ ε₁} h :=
    TopCat.ofHom
      (relativeEntropyPersistenceCutoffColimitMap
        (n := n) (leOfHom h.unop))
  map_id ε := by
    exact
      relativeEntropyPersistenceCutoffColimitMap_refl_hom
        (n := n) ε.unop
  map_comp {ε₃ ε₂ ε₁} h₃₂ h₂₁ := by
    exact
      (relativeEntropyPersistenceCutoffColimitMap_trans_hom
        (n := n) (leOfHom h₂₁.unop) (leOfHom h₃₂.unop)).symm

@[simp] theorem relativeEntropyPersistenceCutoffFunctor_obj
    (n : ℕ) (ε : ℝᵒᵖ) :
    (relativeEntropyPersistenceCutoffFunctor n).obj ε =
      TopCat.of
        (RelativeEntropyPersistenceColimit (n := n) ε.unop) := by
  rfl

@[simp] theorem relativeEntropyPersistenceCutoffFunctor_map_apply
    (n : ℕ) {ε₂ ε₁ : ℝᵒᵖ} (h : ε₂ ⟶ ε₁)
    (x : RelativeEntropyPersistenceColimit (n := n) ε₂.unop) :
    (relativeEntropyPersistenceCutoffFunctor n).map h x =
      relativeEntropyPersistenceCutoffColimitMap
        (leOfHom h.unop) x := by
  rfl

end SouriauRelativeEntropyPersistenceCutoffFunctor
