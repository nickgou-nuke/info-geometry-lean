import InfoGeometry.Spectral.Algebra.SpectralStabilizationColimit

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

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
