import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace SouriauRelativeEntropyPersistenceUniversal

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceFunctor
open SouriauRelativeEntropyPersistenceColimit

variable {n : ℕ}

/-- A compatible family of continuous maps out of all finite KL stages. -/
structure RelativeEntropyPersistenceCompatibleFamily
    (ε : ℝ) (Y : Type) [TopologicalSpace Y] where
  map :
    ∀ t : ℝ,
      C(RelativeEntropySublevelQuotient (n := n) ε 0 t, Y)
  compatible :
    ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      map s x =
        map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x)

namespace RelativeEntropyPersistenceCompatibleFamily

/-- A compatible family is precisely a cocone over the KL persistence ray. -/
noncomputable def toCocone
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y) :
    Cocone (relativeEntropyPersistenceRay (n := n) ε) where
  pt := TopCat.of Y
  ι :=
    { app := fun t => TopCat.ofHom (family.map t)
      naturality := by
        intro s t hst
        apply TopCat.hom_ext
        ext x
        exact
          (family.compatible
            (InfoGeometry.Categorical.InductivePosetColimit.le_of_poset_hom
              hst) x).symm }

/-- The continuous map induced on the KL persistence colimit. -/
noncomputable def descend
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y) :
    C(RelativeEntropyPersistenceColimit (n := n) ε, Y) :=
  (colimit.desc
    (relativeEntropyPersistenceRay (n := n) ε)
    family.toCocone).hom

@[simp] theorem descend_stage
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 t) :
    family.descend
        (relativeEntropyPersistenceColimitStage ε t x) =
      family.map t x := by
  have hfac :=
    colimit.ι_desc family.toCocone t
  exact congrArg
    (fun k :
      (relativeEntropyPersistenceRay (n := n) ε).obj t ⟶
        TopCat.of Y =>
      k x) hfac

theorem descend_unique
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (g : C(RelativeEntropyPersistenceColimit (n := n) ε, Y))
    (hg :
      ∀ (t : ℝ)
        (x : RelativeEntropySublevelQuotient (n := n) ε 0 t),
        g (relativeEntropyPersistenceColimitStage ε t x) =
          family.map t x) :
    g = family.descend := by
  have hhom :
      TopCat.ofHom g =
        colimit.desc
          (relativeEntropyPersistenceRay (n := n) ε)
          family.toCocone := by
    apply colimit.hom_ext
    intro t
    apply TopCat.hom_ext
    ext x
    exact (hg t x).trans (family.descend_stage t x).symm
  exact congrArg TopCat.Hom.hom hhom

theorem existsUnique_descend
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y) :
    ∃! g : C(RelativeEntropyPersistenceColimit (n := n) ε, Y),
      ∀ (t : ℝ)
        (x : RelativeEntropySublevelQuotient (n := n) ε 0 t),
        g (relativeEntropyPersistenceColimitStage ε t x) =
          family.map t x := by
  refine ⟨family.descend, ?_, ?_⟩
  · intro t x
    exact family.descend_stage t x
  · intro g hg
    exact family.descend_unique g hg

end RelativeEntropyPersistenceCompatibleFamily

end SouriauRelativeEntropyPersistenceUniversal
