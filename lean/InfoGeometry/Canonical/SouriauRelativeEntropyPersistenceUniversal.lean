import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceColimit

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

namespace RelativeEntropyPersistenceCompatibleFamily

/-- A compatible family is precisely a cocone over the KL persistence ray. -/
noncomputable def toCocone
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (hcompat : ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      family.map s x =
        family.map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x)) :
    Cocone (relativeEntropyPersistenceRay (n := n) ε) where
  pt := TopCat.of Y
  ι :=
    { app := fun t => TopCat.ofHom (family.map t)
      naturality := by
        intro s t hst
        apply TopCat.hom_ext
        ext x
        exact
          (hcompat
            (InfoGeometry.Categorical.InductivePosetColimit.le_of_poset_hom
              hst) x).symm }

/-- The continuous map induced on the KL persistence colimit. -/
noncomputable def descend
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (hcompat : ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      family.map s x =
        family.map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x)) :
    C(RelativeEntropyPersistenceColimit (n := n) ε, Y) :=
  (colimit.desc
    (relativeEntropyPersistenceRay (n := n) ε)
    (family.toCocone hcompat)).hom

@[simp] theorem descend_stage
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (hcompat : ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      family.map s x =
        family.map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x))
    (t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 t) :
    family.descend hcompat
        (relativeEntropyPersistenceColimitStage ε t x) =
      family.map t x := by
  have hfac :=
    colimit.ι_desc (family.toCocone hcompat) t
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
    (hcompat : ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      family.map s x =
        family.map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x))
    (g : C(RelativeEntropyPersistenceColimit (n := n) ε, Y))
    (hg :
      ∀ (t : ℝ)
        (x : RelativeEntropySublevelQuotient (n := n) ε 0 t),
        g (relativeEntropyPersistenceColimitStage ε t x) =
          family.map t x) :
    g = family.descend hcompat := by
  have hhom :
      TopCat.ofHom g =
        colimit.desc
          (relativeEntropyPersistenceRay (n := n) ε)
          (family.toCocone hcompat) := by
    apply colimit.hom_ext
    intro t
    apply TopCat.hom_ext
    ext x
    exact (hg t x).trans (family.descend_stage hcompat t x).symm
  exact congrArg TopCat.Hom.hom hhom

theorem existsUnique_descend
    {ε : ℝ} {Y : Type} [TopologicalSpace Y]
    (family :
      RelativeEntropyPersistenceCompatibleFamily
        (n := n) ε Y)
    (hcompat : ∀ {s t : ℝ} (hst : s ≤ t)
      (x : RelativeEntropySublevelQuotient (n := n) ε 0 s),
      family.map s x =
        family.map t
          (relativeEntropySublevelQuotientMap ε
            (le_refl 0) hst x)) :
    ∃! g : C(RelativeEntropyPersistenceColimit (n := n) ε, Y),
      ∀ (t : ℝ)
        (x : RelativeEntropySublevelQuotient (n := n) ε 0 t),
        g (relativeEntropyPersistenceColimitStage ε t x) =
          family.map t x := by
  refine ⟨family.descend hcompat, ?_, ?_⟩
  · intro t x
    exact family.descend_stage hcompat t x
  · intro g hg
    exact descend_unique family hcompat g hg

end RelativeEntropyPersistenceCompatibleFamily

end SouriauRelativeEntropyPersistenceUniversal
