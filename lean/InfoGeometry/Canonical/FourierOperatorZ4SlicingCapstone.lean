/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.FourierOperatorZ4Slicing
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.FourierOperatorZ4Slicing

theorem fourier_operator_z4_slicing_canonical_capstone
    {R : Type*} [CommRing R] (X : R) (z : ℂ) :
    (X ^ 5 - X = X * (X ^ 2 - 1) * (X ^ 2 + 1)) ∧
    (X ^ 5 = X ↔ X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0) ∧
    (X ^ 4 = 1 → X ^ 5 = X) ∧
    (z ^ 5 = z → z = 0 ∨ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I) := by
  exact ⟨fourier_quintic_factorization X,
    fourier_quintic_iff_product_zero X,
    fun h4 => fourier_order_four_implies_quintic X h4,
    fun hz => tripartite_spectrum_classification z hz⟩

end InfoGeometry.Canonical
