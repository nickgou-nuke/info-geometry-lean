import InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Nonzero annihilator representatives in the projective null boundary

`CanonicalZornNullProjectiveBoundaryBridge` owns the `(5,5)` null-ray quotient.
This file only exposes the nonzero annihilator slice and reuses that quotient;
it deliberately does not introduce a second projective relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CanonicalZornProjectiveNullRepresentative

open InfoGeometry.Canonical.CanonicalZornNullProjectiveBoundaryBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open ProjectiveAffineConformalClosure55

def NonzeroAnnihilator {X : Imaginary} :=
  {Y : Annihilator X // Y.1 ≠ 0}

def projectiveClass {X : Imaginary}
    (Y : NonzeroAnnihilator (X := X)) : ProjectiveNullBoundary55 :=
  annihilatorProjectiveClass Y.1

theorem projectiveClass_eq_quotient_mk {X : Imaginary}
    (Y : NonzeroAnnihilator (X := X)) :
    projectiveClass Y =
      Quotient.mk nullRepresentative55Rel
        (annihilatorProjectiveRepresentative Y.1) :=
  rfl

theorem projectiveRepresentative_null {X : Imaginary}
    (Y : NonzeroAnnihilator (X := X)) :
    Q55 (annihilatorProjectiveRepresentative Y.1).1 = 0 :=
  annihilatorProjectiveRepresentative_null Y.1

theorem projectiveRepresentative_nonzero {X : Imaginary}
    (Y : NonzeroAnnihilator (X := X)) :
    (annihilatorProjectiveRepresentative Y.1).1 ≠
      pacSplit55Zero :=
  (annihilatorProjectiveRepresentative Y.1).2.1

end InfoGeometry.Canonical.CanonicalZornProjectiveNullRepresentative
