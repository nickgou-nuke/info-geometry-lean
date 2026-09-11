import InfoGeometry.Quantum.FourierOperatorPolynomial
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.FourierOperatorPolynomialCapstone

open InfoGeometry.Quantum.FourierOperatorPolynomial

theorem capstone_fourier_operator_polynomial_synthesis
    {R : Type*} [CommRing R] (X : R) (k : ℕ)
    (hX : IsFourierFourthRoot X) :
    (X * (X ^ 2 - 1) * (X ^ 2 + 1) = X ^ 5 - X) ∧
    (X * (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1) = X ^ (4 * k + 1) - X) ∧
    (X ^ 5 - X = 0) ∧
    (X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0) := by
  exact ⟨tripartite_factorization_eq_quintic X,
    general_tripartite_factorization X k,
    fourier_fourth_root_annihilates_quintic X hX,
    fourier_tripartite_annihilation X hX⟩

end InfoGeometry.Canonical.FourierOperatorPolynomialCapstone
