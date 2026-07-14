import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Basic

/-!
# InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow

Finite polynomial divisibility shadow for the Weyl/Vandermonde corridor.

This is the honest algebraic precursor to any regular-extension discussion:

* denominator shadow: a Vandermonde-type linear factor `X - a`;
* numerator shadow: an alternating polynomial difference `X^n - a^n`;
* theorem: the numerator is divisible by the denominator.

The file deliberately stays in the two-node polynomial lane.  It does not claim
the full `A₂` or general Weyl-character divisibility theorem.
-/

namespace WeylPolynomialDivisibilityShadow

open Polynomial

/--
Two-node polynomial divisibility data.

`a` is the second node of the finite denominator factor `X - a`; the first node
is the polynomial variable `X`.
-/
@[rep_depth thermo]
structure TwoNodePolynomialShadow (R : Type*) [CommRing R] where
  a : R
  n : ℕ

namespace TwoNodePolynomialShadow

variable {R : Type*} [CommRing R]
variable (P : TwoNodePolynomialShadow R)

/-- The finite Vandermonde-type denominator factor. -/
@[rep_depth thermo]
noncomputable def denominator : R[X] :=
  X - C P.a

/-- The alternating polynomial numerator shadow. -/
@[rep_depth thermo]
noncomputable def numerator : R[X] :=
  X ^ P.n - C (P.a ^ P.n)

/--
The finite denominator divides the alternating polynomial numerator.
-/
@[rep_depth thermo]
theorem denominator_dvd_numerator :
    P.denominator ∣ P.numerator := by
  unfold denominator numerator
  simpa using sub_dvd_pow_sub_pow X (C P.a) P.n

/--
Existence of a quotient polynomial witnessing divisibility.
-/
@[rep_depth thermo]
theorem exists_quotient :
    ∃ q : R[X], P.denominator * q = P.numerator := by
  rcases P.denominator_dvd_numerator with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

/--
Combined divisibility packet for the two-node polynomial shadow.
-/
@[rep_depth thermo]
theorem polynomial_divisibility_packet :
    P.denominator ∣ P.numerator
    ∧ (∃ q : R[X], P.denominator * q = P.numerator)
    := by
  exact
    ⟨P.denominator_dvd_numerator,
      P.exists_quotient⟩

end TwoNodePolynomialShadow

end WeylPolynomialDivisibilityShadow
