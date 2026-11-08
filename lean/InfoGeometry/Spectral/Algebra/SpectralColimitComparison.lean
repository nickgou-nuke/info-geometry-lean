import InfoGeometry.Spectral.Algebra.SpectralStabilizationColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Colimit comparison for a stabilized spectral tail

This owner records only the categorical consequence of the stabilized-tail
colimit theorem.  It does not identify the stable page with an associated
graded abutment; that is a separate reconstruction statement.
-/

namespace InfoGeometry.Spectral.Algebra

universe u v

namespace GradedExactCouple

variable {R : Type u} [Ring R]
variable {I : Type v}

open CategoryTheory
open CategoryTheory.Limits

/-- Explicit comparison data from the stabilized tail to a proposed
associated-graded carrier.  The equivalence is not part of the data: it is
recovered from the universal property once the legs are compatible and
invertible. -/
structure StabilizedTailAssociatedGradedData
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) where
  carrier : ModuleCat R
  filtration : ℕ → Submodule R carrier
  pageToGraded : ∀ n, (stabilizedPageFunctor S h p).obj n ⟶ carrier
  pageToGraded_isIso : ∀ n, IsIso (pageToGraded n)
  pageToGraded_compatibility :
    ∀ {m n : ℕ} (f : m ⟶ n),
      (stabilizedPageFunctor S h p).map f ≫ pageToGraded n = pageToGraded m
  exhaustive : filtration 0 = ⊤
  separated : ∀ x : carrier, (∀ n, x ∈ filtration n) → x = 0

noncomputable abbrev stabilizedPageColimitApex
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) : ModuleCat R :=
  (stabilizedPageCocone S h p).pt

/-- The stable page is canonically isomorphic to the colimit of its
stabilized tail. -/
noncomputable def stabilizedPageIsoColimit
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    ModuleCat.of R (stablePage S h p) ≅ stabilizedPageColimitApex S h p :=
  Iso.refl _

/-- The stable page is canonically isomorphic to Mathlib's chosen colimit
object, not merely to the apex of the displayed cocone. -/
noncomputable def stabilizedPageIsoChosenColimit
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (hcolim : HasColimit (stabilizedPageFunctor S h p)) :
    ModuleCat.of R (stablePage S h p) ≅
      colimit (stabilizedPageFunctor S h p) :=
  letI := hcolim
  (stabilizedPageCocone_isColimit S h p).coconePointUniqueUpToIso
    (colimit.isColimit (stabilizedPageFunctor S h p))

theorem stabilizedPageIsoChosenColimit_comp_leg
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (hcolim : HasColimit (stabilizedPageFunctor S h p)) (n : ℕ) :
    (stabilizedPageCocone S h p).ι.app n ≫
        (stabilizedPageIsoChosenColimit S h p hcolim).hom =
      colimit.ι (stabilizedPageFunctor S h p) n := by
  letI := hcolim
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (stabilizedPageCocone_isColimit S h p)
    (colimit.isColimit (stabilizedPageFunctor S h p)) n

theorem stabilizedPageIsoChosenColimit_inv_comp_leg
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (hcolim : HasColimit (stabilizedPageFunctor S h p)) (n : ℕ) :
    colimit.ι (stabilizedPageFunctor S h p) n ≫
        (stabilizedPageIsoChosenColimit S h p hcolim).inv =
      (stabilizedPageCocone S h p).ι.app n := by
  letI := hcolim
  exact IsColimit.comp_coconePointUniqueUpToIso_inv
    (stabilizedPageCocone_isColimit S h p)
    (colimit.isColimit (stabilizedPageFunctor S h p)) n

noncomputable def stabilizedPageColimitApex_isColimit
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    IsColimit (stabilizedPageCocone S h p) :=
  stabilizedPageCocone_isColimit S h p

/-- The compatible page-to-graded maps form a cocone. -/
noncomputable def stabilizedTailAssociatedGradedCocone
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (d : StabilizedTailAssociatedGradedData S h p) :
    Cocone (stabilizedPageFunctor S h p) := by
  letI : ∀ n, IsIso (d.pageToGraded n) := d.pageToGraded_isIso
  refine Cocone.mk d.carrier {
    app := fun n => d.pageToGraded n
    naturality := ?_ }
  intro m n f
  calc
    (stabilizedPageFunctor S h p).map f ≫ d.pageToGraded n =
        d.pageToGraded m := d.pageToGraded_compatibility f
    _ = d.pageToGraded m ≫ 𝟙 d.carrier :=
      (Category.comp_id (d.pageToGraded m)).symm

/-- The stabilized-tail colimit is equivalent to the associated-graded carrier
when the supplied comparison legs satisfy the explicit reconstruction data. -/
noncomputable def stabilizedTailColimitIsoAssociatedGraded
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I)
    (d : StabilizedTailAssociatedGradedData S h p)
    (hcolim : HasColimit (stabilizedPageFunctor S h p)) :
    colimit (stabilizedPageFunctor S h p) ≅ d.carrier := by
  letI := hcolim
  let c := stabilizedTailAssociatedGradedCocone S h p d
  letI : ∀ n, IsIso (c.ι.app n) := by
    intro n
    simpa [c, stabilizedTailAssociatedGradedCocone] using
      d.pageToGraded_isIso n
  simpa [c, stabilizedTailAssociatedGradedCocone] using
    (colimit.isColimit (stabilizedPageFunctor S h p)).coconePointUniqueUpToIso
      (InfoGeometry.Category.natCoconeIsColimitOfIsoLegs c)

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
