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

noncomputable def stabilizedPageColimitApex_isColimit
    (S : Stage R I) (h : BoundedPageStabilization S) (p : I) :
    IsColimit (stabilizedPageCocone S h p) :=
  stabilizedPageCocone_isColimit S h p

end GradedExactCouple

end InfoGeometry.Spectral.Algebra
