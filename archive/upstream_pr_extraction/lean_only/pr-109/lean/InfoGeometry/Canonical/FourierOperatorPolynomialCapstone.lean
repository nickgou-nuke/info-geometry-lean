import InfoGeometry.Quantum.FourierOperatorPolynomial

namespace InfoGeometry.Canonical.FourierOperatorPolynomialCapstone

open InfoGeometry.Quantum.FourierOperatorPolynomial

theorem capstone_fourier_operator_polynomial_synthesis
    {R : Type*} [CommRing R] (X : R) (k : ℕ) (hX : IsFourierFourthRoot X) :
    (X * (X ^ 2 - 1) * (X ^ 2 + 1) = X ^ 5 - X) ∧
    (X * (X ^ (2 * k) - 1) * (X ^ (2 * k) + 1) = X ^ (4 * k + 1) - X) ∧
    (X ^ 5 - X = 0) ∧
    (X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0) :=
  grand_fourier_operator_polynomial_synthesis X k hX

end InfoGeometry.Canonical.FourierOperatorPolynomialCapstone
