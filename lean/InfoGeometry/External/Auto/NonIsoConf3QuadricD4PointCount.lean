import InfoGeometry.External.Auto.NonIsoConf3QuadricD4Model
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite-field point-count fingerprint for the D=4 non-isotropic model

For the translated space

`U_4 = {(a,b) | q(a) q(b) q(a-b) != 0}`,

the SymPy/NumPy computation `non_iso_conf3_quadric_d4_point_count.py` counts
`U_4(F_p)` by cyclic convolution for several odd primes and interpolates the
polynomial

`p^2 (p-1)^2 (p+1) (p^3 - 2p^2 - p + 3)`.

This Lean file records the polynomial and checks named point values.  It does not
claim that polynomial count alone proves the complex cohomology ring.
-/

noncomputable section

namespace NonIsoConf3QuadricD4PointCount

/-- Candidate finite-field count polynomial for `U_4(F_p)`. -/
def countPolynomial (p : ℕ) : ℕ :=
  p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 3 - 2 * p ^ 2 - p + 3)

/-- Integer-polynomial count of isotropic vectors for the split four-variable
quadric over odd finite fields. -/
def isotropicVectorCountZ (p : ℤ) : ℤ := p * (p ^ 2 + p - 1)

/-- Integer-polynomial count of non-isotropic vectors. -/
def nonisotropicVectorCountZ (p : ℤ) : ℤ := p * (p - 1) ^ 2 * (p + 1)

/-- Integer-polynomial count of pairs with bad isotropic difference after both
individual vectors are non-isotropic. -/
def badDifferenceCountZ (p : ℤ) : ℤ :=
  p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 2 - 2)

/-- Integer version of the candidate point-count polynomial. -/
def countPolynomialZ (p : ℤ) : ℤ :=
  p ^ 2 * (p - 1) ^ 2 * (p + 1) * (p ^ 3 - 2 * p ^ 2 - p + 3)

theorem nonisotropicVectorCountZ_eq_total_sub_isotropic (p : ℤ) :
    nonisotropicVectorCountZ p = p ^ 4 - isotropicVectorCountZ p := by
  simp only [nonisotropicVectorCountZ, isotropicVectorCountZ]
  ring_nf

theorem countPolynomialZ_eq_good_pairs (p : ℤ) :
    countPolynomialZ p =
      nonisotropicVectorCountZ p ^ 2 - badDifferenceCountZ p := by
  simp only [countPolynomialZ, nonisotropicVectorCountZ, badDifferenceCountZ]
  ring_nf

/-- The bad-difference count decomposes into the zero isotropic difference
plus equal nonzero isotropic-difference fibers. -/
def nonzeroIsotropicDifferenceFiberZ (p : ℤ) : ℤ :=
  p * (p - 1) * (p ^ 2 - p - 1)

theorem badDifferenceCountZ_decomposition (p : ℤ) :
    badDifferenceCountZ p =
      nonisotropicVectorCountZ p +
        (isotropicVectorCountZ p - 1) * nonzeroIsotropicDifferenceFiberZ p := by
  simp only [badDifferenceCountZ, nonisotropicVectorCountZ, isotropicVectorCountZ,
    nonzeroIsotropicDifferenceFiberZ]
  ring_nf

theorem countPolynomial_at_three : countPolynomial 3 = 1296 := by
  norm_num [countPolynomial]

theorem countPolynomial_at_five : countPolynomial 5 = 175200 := by
  norm_num [countPolynomial]

theorem countPolynomial_at_seven : countPolynomial 7 = 3400992 := by
  norm_num [countPolynomial]

theorem countPolynomial_at_eleven : countPolynomial 11 = 156961200 := by
  norm_num [countPolynomial]

end NonIsoConf3QuadricD4PointCount

end noncomputable section
