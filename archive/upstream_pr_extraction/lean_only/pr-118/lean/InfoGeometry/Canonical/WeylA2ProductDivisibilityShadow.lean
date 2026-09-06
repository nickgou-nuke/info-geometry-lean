import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow

/-!
# InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow

Finite three-node product/divisibility shadow assembled from the existing
two-node polynomial divisibility owners.

This file is deliberately conservative.  It does **not** claim the genuine
`A₂` Vandermonde divisibility theorem.  Instead it proves a product version:

* denominator product:
  `(X - a) * (X - b) * (X - c)`,
* numerator product:
  `(X^n - a^n) * (X^n - b^n) * (X^n - c^n)`,
* theorem: the denominator product divides the numerator product.

This is the honest next step after the 2-node divisibility shadow.
-/

namespace InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow

open Polynomial
open InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow

/-- Three-node product divisibility data. -/
@[rep_depth thermo]
structure ThreeNodePolynomialShadow (R : Type*) [CommRing R] where
  a : R
  b : R
  c : R
  n : ℕ

namespace ThreeNodePolynomialShadow

variable {R : Type*} [CommRing R]
variable (P : ThreeNodePolynomialShadow R)

/-- The three constituent two-node shadows. -/
@[rep_depth thermo]
def shadowA : TwoNodePolynomialShadow R := { a := P.a, n := P.n }

@[rep_depth thermo]
def shadowB : TwoNodePolynomialShadow R := { a := P.b, n := P.n }

@[rep_depth thermo]
def shadowC : TwoNodePolynomialShadow R := { a := P.c, n := P.n }

/-- Product denominator assembled from the three two-node factors. -/
@[rep_depth thermo]
noncomputable def denominator : R[X] :=
  P.shadowA.denominator * P.shadowB.denominator * P.shadowC.denominator

/-- Product numerator assembled from the three two-node numerators. -/
@[rep_depth thermo]
noncomputable def numerator : R[X] :=
  P.shadowA.numerator * P.shadowB.numerator * P.shadowC.numerator

/-- The first denominator factor divides the product numerator. -/
@[rep_depth thermo]
theorem denominatorA_dvd_numerator :
    P.shadowA.denominator ∣ P.numerator := by
  rcases P.shadowA.denominator_dvd_numerator with ⟨q, hq⟩
  refine ⟨q * P.shadowB.numerator * P.shadowC.numerator, ?_⟩
  calc
    P.numerator
        = (P.shadowA.denominator * q) * P.shadowB.numerator * P.shadowC.numerator := by
            unfold numerator
            rw [hq]
    _ = P.shadowA.denominator * (q * P.shadowB.numerator * P.shadowC.numerator) := by
          ring

/-- The second denominator factor divides the product numerator. -/
@[rep_depth thermo]
theorem denominatorB_dvd_numerator :
    P.shadowB.denominator ∣ P.numerator := by
  rcases P.shadowB.denominator_dvd_numerator with ⟨q, hq⟩
  refine ⟨P.shadowA.numerator * q * P.shadowC.numerator, ?_⟩
  calc
    P.numerator
        = P.shadowA.numerator * (P.shadowB.denominator * q) * P.shadowC.numerator := by
            unfold numerator
            rw [hq]
    _ = P.shadowB.denominator * (P.shadowA.numerator * q * P.shadowC.numerator) := by
          ring

/-- The third denominator factor divides the product numerator. -/
@[rep_depth thermo]
theorem denominatorC_dvd_numerator :
    P.shadowC.denominator ∣ P.numerator := by
  rcases P.shadowC.denominator_dvd_numerator with ⟨q, hq⟩
  refine ⟨P.shadowA.numerator * P.shadowB.numerator * q, ?_⟩
  calc
    P.numerator
        = P.shadowA.numerator * P.shadowB.numerator * (P.shadowC.denominator * q) := by
            unfold numerator
            rw [hq]
    _ = P.shadowC.denominator * (P.shadowA.numerator * P.shadowB.numerator * q) := by
          ring

/--
The full denominator product divides the full numerator product.

This is proved by successively inserting the quotient witnesses from the three
two-node divisibility owners.
-/
@[rep_depth thermo]
theorem denominator_dvd_numerator :
    P.denominator ∣ P.numerator := by
  rcases P.shadowA.denominator_dvd_numerator with ⟨qa, hqa⟩
  rcases P.shadowB.denominator_dvd_numerator with ⟨qb, hqb⟩
  rcases P.shadowC.denominator_dvd_numerator with ⟨qc, hqc⟩
  refine ⟨qa * qb * qc, ?_⟩
  calc
    P.numerator
        = (P.shadowA.denominator * qa) * (P.shadowB.denominator * qb) *
            (P.shadowC.denominator * qc) := by
              unfold numerator
              rw [hqa, hqb, hqc]
    _ = (P.shadowA.denominator * P.shadowB.denominator * P.shadowC.denominator) *
          (qa * qb * qc) := by
            ring
    _ = P.denominator * (qa * qb * qc) := by
          unfold denominator
          ring

/-- Existence of a quotient polynomial for the product divisibility shadow. -/
@[rep_depth thermo]
theorem exists_quotient :
    ∃ q : R[X], P.denominator * q = P.numerator := by
  rcases P.denominator_dvd_numerator with ⟨q, hq⟩
  exact ⟨q, hq.symm⟩

end ThreeNodePolynomialShadow

end InfoGeometry.Canonical.WeylA2ProductDivisibilityShadow
