import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SupergradedBracket

/-!
# Graded chiral superderivations and algebraic colimit transport

This owner keeps the superalgebraic statement separate from any analytic
completion.  A homogeneous element is tagged by `Bool`; an odd charge sends
parity `p` to `!p`.  The odd--odd superderivation anticommutator is then an
ordinary inner derivation of the operator anticommutator.  Ring homomorphisms
transport this identity, which is the precise finite-stage/cocone statement
needed before invoking a particular inductive-colimit carrier.
-/

namespace InfoGeometry.Canonical.ChiralSuperderivationColimit

def innerDerivation {A : Type*} [Ring A] (Q X : A) : A :=
  Q * X - X * Q

def oddSuperDerivation {A : Type*} [Ring A] (Q X : A) (p : Bool) : A :=
  if p then Q * X + X * Q else Q * X - X * Q

def oddSuperAnticommutator {A : Type*} [Ring A]
    (Qplus Qminus X : A) (p : Bool) : A :=
  oddSuperDerivation Qplus (oddSuperDerivation Qminus X p) (!p) +
    oddSuperDerivation Qminus (oddSuperDerivation Qplus X p) (!p)

theorem oddSuperAnticommutator_eq_innerDerivation
    {A : Type*} [Ring A] (Qplus Qminus X : A) (p : Bool) :
    oddSuperAnticommutator Qplus Qminus X p =
      innerDerivation (Qplus * Qminus + Qminus * Qplus) X := by
  cases p <;>
    simp [oddSuperAnticommutator, oddSuperDerivation, innerDerivation] <;>
    noncomm_ring

theorem oddSuperSquare_eq_innerDerivation
    {A : Type*} [Ring A] (Q X : A) (p : Bool) :
    oddSuperAnticommutator Q Q X p = innerDerivation (Q * Q + Q * Q) X := by
  exact oddSuperAnticommutator_eq_innerDerivation Q Q X p

theorem oddSuperAnticommutator_eq_innerDerivation_superBracket
    {A : Type*} [Ring A] (Qplus Qminus X : A) (p : Bool) :
    oddSuperAnticommutator Qplus Qminus X p =
      innerDerivation
        (InfoGeometry.Algebra.SupergradedBracket.superBracket
          true true Qplus Qminus) X := by
  rw [InfoGeometry.Algebra.SupergradedBracket.superBracket_odd_odd]
  exact oddSuperAnticommutator_eq_innerDerivation Qplus Qminus X p

theorem map_innerDerivation {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (Q X : A) :
    f (innerDerivation Q X) = innerDerivation (f Q) (f X) := by
  simp [innerDerivation]

theorem map_oddSuperAnticommutator {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (Qplus Qminus X : A) (p : Bool) :
    f (oddSuperAnticommutator Qplus Qminus X p) =
      oddSuperAnticommutator (f Qplus) (f Qminus) (f X) p := by
  cases p <;> simp [oddSuperAnticommutator, oddSuperDerivation]

theorem transport_oddSuperClosure {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (Qplus Qminus X P : A) (Pinf : B) (p : Bool)
    (hP : Qplus * Qminus + Qminus * Qplus = P)
    (hPinf : f P = Pinf) :
    oddSuperAnticommutator (f Qplus) (f Qminus) (f X) p =
      innerDerivation Pinf (f X) := by
  rw [← map_oddSuperAnticommutator f Qplus Qminus X p]
  rw [oddSuperAnticommutator_eq_innerDerivation]
  rw [hP, map_innerDerivation, hPinf]

end InfoGeometry.Canonical.ChiralSuperderivationColimit
