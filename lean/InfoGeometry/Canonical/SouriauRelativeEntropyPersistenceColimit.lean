import Mathlib.Topology.Category.TopCat.Limits.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Categorical.InductivePosetColimit
import InfoGeometry.Canonical.SouriauRelativeEntropyPersistenceDiagram

namespace SouriauRelativeEntropyPersistenceColimit

open CategoryTheory
open CategoryTheory.Limits
open SouriauRelativeEntropyPersistenceQuotient
open SouriauRelativeEntropyPersistenceFunctor

variable {n : ℕ}

/-- The one-parameter persistence ray `t ↦ L_t / L_0`. -/
noncomputable def relativeEntropyPersistenceRay {n : ℕ}
    (ε : ℝ) : ℝ ⥤ TopCat where
  obj t :=
    TopCat.of
      (RelativeEntropySublevelQuotient (n := n) ε 0 t)
  map {s t} h :=
    TopCat.ofHom
      (relativeEntropySublevelQuotientContinuousMap ε
        (le_refl 0) (leOfHom h))
  map_id t := by
    apply TopCat.hom_ext
    ext x
    exact relativeEntropySublevelQuotientMap_refl ε 0 t x
  map_comp {r s t} hrs hst := by
    apply TopCat.hom_ext
    ext x
    exact
      (relativeEntropySublevelQuotientMap_trans ε
        (le_refl 0) (leOfHom hrs)
        (le_refl 0) (leOfHom hst) x).symm

@[simp] theorem relativeEntropyPersistenceRay_map_apply
    (ε : ℝ) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 s) :
    (relativeEntropyPersistenceRay (n := n) ε).map
        (InfoGeometry.Categorical.InductivePosetColimit.poset_hom_of_le hst) x =
      relativeEntropySublevelQuotientMap ε (le_refl 0) hst x := by
  rfl

/-- The carrier of the TopCat direct colimit of the KL persistence ray. -/
abbrev RelativeEntropyPersistenceColimit
    (ε : ℝ) : Type :=
  (colimit (relativeEntropyPersistenceRay (n := n) ε) : TopCat)

/-- Canonical continuous map from a finite KL stage into the direct colimit. -/
noncomputable def relativeEntropyPersistenceColimitStage
    (ε t : ℝ) :
    C(RelativeEntropySublevelQuotient (n := n) ε 0 t,
      RelativeEntropyPersistenceColimit (n := n) ε) :=
  (colimit.ι (relativeEntropyPersistenceRay (n := n) ε) t).hom

@[simp] theorem relativeEntropyPersistenceColimitStage_apply
    (ε t : ℝ)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 t) :
    relativeEntropyPersistenceColimitStage ε t x =
      (colimit.ι (relativeEntropyPersistenceRay (n := n) ε) t) x := by
  rfl

theorem relativeEntropyPersistenceColimitStage_compat
    (ε : ℝ) {s t : ℝ} (hst : s ≤ t)
    (x : RelativeEntropySublevelQuotient (n := n) ε 0 s) :
    relativeEntropyPersistenceColimitStage ε s x =
      relativeEntropyPersistenceColimitStage ε t
        (relativeEntropySublevelQuotientMap ε
          (le_refl 0) hst x) := by
  have hw :=
    colimit.w (relativeEntropyPersistenceRay (n := n) ε)
      (InfoGeometry.Categorical.InductivePosetColimit.poset_hom_of_le hst)
  have hx := congrArg
    (fun k :
      (relativeEntropyPersistenceRay (n := n) ε).obj s ⟶
        colimit (relativeEntropyPersistenceRay (n := n) ε) =>
      k x) hw.symm
  exact hx

end SouriauRelativeEntropyPersistenceColimit
