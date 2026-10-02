import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-!
# Principal divisors of split rational functions on the projective line

This is an algebraic projective-line model, not a compact-Riemann-surface or
Abel--Jacobi construction. A rational function presented by nonzero split
polynomials `p / q` has finite zero and pole multisets given by their roots;
its order at infinity is `deg(q) - deg(p)`. The theorem below proves that
this principal divisor has degree zero, with root multiplicities retained.
-/

noncomputable section

namespace InfoGeometry.Algebraic.ProjectiveLineRationalDivisor

open Polynomial

variable (K : Type*) [Field K]

/-- A polynomial presentation of a nonzero rational function whose numerator
and denominator split over the coefficient field. -/
structure SplitRationalFunction where
  numerator : K[X]
  denominator : K[X]
  numerator_ne_zero : numerator ≠ 0
  denominator_ne_zero : denominator ≠ 0
  numerator_splits : numerator.Splits
  denominator_splits : denominator.Splits

/-- Divisor data on `ℙ¹(K)`: finite zero and pole multisets, together with
the signed order at the point at infinity. Multiset repetition records
multiplicity. -/
structure ProjectiveLineDivisor where
  zeros : Multiset K
  poles : Multiset K
  orderAtInfinity : ℤ

/-- The coefficient of the divisor at a finite point, or at infinity when
the argument is `none`. -/
def ProjectiveLineDivisor.orderAt [DecidableEq K]
    (D : ProjectiveLineDivisor K) : Option K → ℤ
  | none => D.orderAtInfinity
  | some z => (D.zeros.count z : ℤ) - D.poles.count z

/-- Degree of divisor data, counting multiplicities and the point at infinity. -/
def ProjectiveLineDivisor.degree (D : ProjectiveLineDivisor K) : ℤ :=
  (D.zeros.card : ℤ) - D.poles.card + D.orderAtInfinity

/-- The divisor associated with the displayed polynomial quotient `p / q`.
The construction is tied to this presentation; no claim of quotient
presentation-independence is needed for the degree theorem. -/
def SplitRationalFunction.divisor (f : SplitRationalFunction K) :
    ProjectiveLineDivisor K where
  zeros := f.numerator.roots
  poles := f.denominator.roots
  orderAtInfinity := (f.denominator.natDegree : ℤ) - f.numerator.natDegree

/-- Every nonzero rational function with split numerator and denominator has
principal divisor of degree zero on the projective line. -/
theorem SplitRationalFunction.divisor_degree_eq_zero
    (f : SplitRationalFunction K) : f.divisor.degree = 0 := by
  have hnum : (f.numerator.natDegree : ℤ) = f.numerator.roots.card := by
    exact_mod_cast f.numerator_splits.natDegree_eq_card_roots
  have hden : (f.denominator.natDegree : ℤ) = f.denominator.roots.card := by
    exact_mod_cast f.denominator_splits.natDegree_eq_card_roots
  unfold SplitRationalFunction.divisor ProjectiveLineDivisor.degree
  rw [← hnum, ← hden]
  ring

/-- The divisor's infinity coefficient is exactly the negative of the net
finite zero count. -/
theorem SplitRationalFunction.orderAtInfinity_eq_neg_finite_degree
    (f : SplitRationalFunction K) :
    f.divisor.orderAtInfinity =
      (f.divisor.poles.card : ℤ) - f.divisor.zeros.card := by
  have hnum : (f.numerator.natDegree : ℤ) = f.numerator.roots.card := by
    exact_mod_cast f.numerator_splits.natDegree_eq_card_roots
  have hden : (f.denominator.natDegree : ℤ) = f.denominator.roots.card := by
    exact_mod_cast f.denominator_splits.natDegree_eq_card_roots
  simp [SplitRationalFunction.divisor, hnum, hden]

end InfoGeometry.Algebraic.ProjectiveLineRationalDivisor
