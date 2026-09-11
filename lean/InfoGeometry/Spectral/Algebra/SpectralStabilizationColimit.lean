import InfoGeometry.Spectral.Algebra.StablePage
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Category.NatCoconeIso
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Stabilized tail cone

This is the first categorical Route B boundary.  It exposes the canonical
legs from the eventual page tail to the stable page.  A genuine `Cocone` and
`IsColimit` theorem are deferred until the page index category and its
`ModuleCat` diagram are fixed.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

open CategoryTheory
open CategoryTheory.Limits

noncomputable def stabilizedPageLeg
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    (page S (h.bound p + n) p : Type u) →ₗ[R] stablePage S h p :=
  (stablePageEquiv S h p (h.bound p + n)
    (Nat.le_add_right (h.bound p) n)).toLinearMap

theorem stabilizedPageLeg_apply
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ)
    (x : page S (h.bound p + n) p) :
    stabilizedPageLeg S h p n x =
      stablePageEquiv S h p (h.bound p + n)
        (Nat.le_add_right (h.bound p) n) x :=
  rfl

/-- The canonical stable-page leg is an isomorphism of `ModuleCat` objects. -/
noncomputable def stabilizedPageLegIso
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    ModuleCat.of R (page S (h.bound p + n) p) ≅
      ModuleCat.of R (stablePage S h p) :=
  (stablePageEquiv S h p (h.bound p + n)
    (Nat.le_add_right (h.bound p) n)).toModuleIso

@[simp]
theorem stabilizedPageLegIso_hom
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    (stabilizedPageLegIso S h p n).hom =
      ModuleCat.ofHom (stabilizedPageLeg S h p n) :=
  rfl

noncomputable def stabilizedPageTailTransport
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m n : ℕ) (_hmn : m ≤ n) :
    (page S (h.bound p + m) p : Type u) →ₗ[R]
      (page S (h.bound p + n) p : Type u) :=
  (stablePageTransport S h p (h.bound p + m) (h.bound p + n)
    (Nat.le_add_right (h.bound p) m)
    (Nat.le_add_right (h.bound p) n)).toLinearMap

theorem stabilizedPageTail_comm
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m n : ℕ) (hmn : m ≤ n) :
    (stabilizedPageLeg S h p n).comp
        (stabilizedPageTailTransport S h p m n hmn) =
      stabilizedPageLeg S h p m := by
  apply LinearMap.ext
  intro x
  simp [stabilizedPageLeg, stabilizedPageTailTransport, stablePageTransport]

/-- Every bonding map in the transported stabilized tail is an isomorphism. -/
noncomputable def stabilizedPageTailTransportIso
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m n : ℕ) (_hmn : m ≤ n) :
    ModuleCat.of R (page S (h.bound p + m) p) ≅
      ModuleCat.of R (page S (h.bound p + n) p) :=
  (stablePageTransport S h p (h.bound p + m) (h.bound p + n)
    (Nat.le_add_right (h.bound p) m)
    (Nat.le_add_right (h.bound p) n)).toModuleIso

@[simp]
theorem stabilizedPageTailTransportIso_hom
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (m n : ℕ) (hmn : m ≤ n) :
    (stabilizedPageTailTransportIso S h p m n hmn).hom =
      ModuleCat.ofHom (stabilizedPageTailTransport S h p m n hmn) :=
  rfl

/-! ## A genuine `ModuleCat` tail diagram -/

/-- The stabilized tail, with canonical transport as its successive map.

This is deliberately the transported tail rather than the original page
differentials: every bonding map is an isomorphism by construction, and the
coherence theorem below is inherited from `stablePageTransport_comp`.
-/
noncomputable def stabilizedPageFunctor
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    ℕ ⥤ ModuleCat R :=
  Functor.ofSequence (fun n =>
    ModuleCat.ofHom
      (stabilizedPageTailTransport S h p n (n + 1) (Nat.le_add_right n 1)))

@[simp]
theorem stabilizedPageFunctor_obj
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    (stabilizedPageFunctor S h p).obj n =
      ModuleCat.of R (page S (h.bound p + n) p) :=
  rfl

@[simp]
theorem stabilizedPageFunctor_step
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    (stabilizedPageFunctor S h p).map
        (CategoryTheory.homOfLE (Nat.le_add_right n 1)) =
      ModuleCat.ofHom
        (stabilizedPageTailTransport S h p n (n + 1)
          (Nat.le_add_right n 1)) := by
  simp [stabilizedPageFunctor]

/-- The successive maps of the transported tail are isomorphisms.  This is
not an additional stabilization hypothesis: the tail was defined by the
canonical transport through the stable page. -/
theorem stabilizedPageFunctor_step_isIso
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    IsIso ((stabilizedPageFunctor S h p).map
      (CategoryTheory.homOfLE (Nat.le_add_right n 1))) := by
  rw [stabilizedPageFunctor_step]
  rw [← stabilizedPageTailTransportIso_hom S h p n (n + 1)
    (Nat.le_add_right n 1)]
  infer_instance

/-- The stable page receives the canonical legs from the transported tail. -/
noncomputable def stabilizedPageCocone
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    Cocone (stabilizedPageFunctor S h p) :=
  { pt := ModuleCat.of R (stablePage S h p)
    ι := NatTrans.ofSequence
      (app := fun n => ModuleCat.ofHom (stabilizedPageLeg S h p n))
      (naturality := by
        intro n
        ext x
        simp [stabilizedPageFunctor,
          stabilizedPageLeg, stabilizedPageTailTransport, stablePageTransport]) }

@[simp]
theorem stabilizedPageCocone_leg
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    (stabilizedPageCocone S h p).ι.app n =
      ModuleCat.ofHom (stabilizedPageLeg S h p n) :=
  rfl

theorem stabilizedPageCocone_leg_isIso
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) (n : ℕ) :
    IsIso ((stabilizedPageCocone S h p).ι.app n) := by
  rw [stabilizedPageCocone_leg]
  exact (stabilizedPageLegIso S h p n).isIso_hom

noncomputable def stabilizedPageCocone_isColimit
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    IsColimit (stabilizedPageCocone S h p) := by
  letI : ∀ n : ℕ, IsIso ((stabilizedPageCocone S h p).ι.app n) :=
    fun n => stabilizedPageCocone_leg_isIso S h p n
  exact InfoGeometry.Category.natCoconeIsColimitOfIsoLegs
    (stabilizedPageCocone S h p)

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
