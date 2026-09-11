import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow

/-!
# InfoGeometry.Canonical.WeylAntisymmetricDivisibilityShadow

Finite antisymmetric/divisibility shadow for the Weyl/Vandermonde corridor.

This file isolates the first honest alternating bridge:

* numerator shadow: `x^n - y^n`,
* swap antisymmetry: exchanging `x` and `y` negates the numerator,
* Vandermonde divisibility: `x - y` divides the numerator.

This is still only the two-node finite lane.  It does not claim a full
multivariate alternating-polynomial or Weyl-character divisibility theorem.
-/

namespace InfoGeometry.Canonical.WeylAntisymmetricDivisibilityShadow

/-- Two-node alternating shadow data. -/
@[rep_depth thermo]
structure TwoNodeAlternatingShadow (R : Type*) [CommRing R] where
  x : R
  y : R
  n : ℕ

namespace TwoNodeAlternatingShadow

variable {R : Type*} [CommRing R]
variable (A : TwoNodeAlternatingShadow R)

/-- The Vandermonde-type denominator factor in the scalar lane. -/
@[rep_depth thermo]
def denominator : R :=
  A.x - A.y

/-- The alternating numerator in the scalar lane. -/
@[rep_depth thermo]
def numerator : R :=
  A.x ^ A.n - A.y ^ A.n

/-- Swapping the two nodes. -/
@[rep_depth thermo]
def swap : TwoNodeAlternatingShadow R where
  x := A.y
  y := A.x
  n := A.n

/-- The numerator is antisymmetric under swapping the two nodes. -/
@[rep_depth thermo]
theorem numerator_swap_eq_neg :
    A.swap.numerator = -A.numerator := by
  unfold numerator swap
  ring

/-- The denominator is antisymmetric under swapping the two nodes. -/
@[rep_depth thermo]
theorem denominator_swap_eq_neg :
    A.swap.denominator = -A.denominator := by
  unfold denominator swap
  ring

/-- Vandermonde divisibility in the scalar two-node lane. -/
@[rep_depth thermo]
theorem denominator_dvd_numerator :
    A.denominator ∣ A.numerator := by
  unfold denominator numerator
  simpa using sub_dvd_pow_sub_pow A.x A.y A.n

/--
Polynomial specialization packet.

This identifies the repo-owned polynomial divisibility shadow whose scalar
specialization gives the current two-node alternating numerator.
-/
@[rep_depth thermo]
def polynomialShadow : WeylPolynomialDivisibilityShadow.TwoNodePolynomialShadow R where
  a := A.y
  n := A.n

/--
Combined antisymmetry/divisibility packet for the two-node lane.
-/
@[rep_depth thermo]
theorem antisymmetry_divisibility_packet :
    A.swap.numerator = -A.numerator
    ∧ A.swap.denominator = -A.denominator
    ∧ A.denominator ∣ A.numerator := by
  exact
    ⟨A.numerator_swap_eq_neg,
      A.denominator_swap_eq_neg,
      A.denominator_dvd_numerator⟩

end TwoNodeAlternatingShadow

end InfoGeometry.Canonical.WeylAntisymmetricDivisibilityShadow
