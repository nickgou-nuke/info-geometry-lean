/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.FourierOperatorZ4Slicing

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.FourierOperatorZ4Slicing

/-- Canonical projection capstone for Fourier Operator Z4 Slicing module. -/
theorem fourier_operator_z4_slicing_canonical_capstone
    {R : Type*} [CommRing R] (X : R) (z : ℂ) :
    (X ^ 5 - X = X * (X ^ 2 - 1) * (X ^ 2 + 1)) ∧
    (X ^ 5 = X ↔ X * (X ^ 2 - 1) * (X ^ 2 + 1) = 0) ∧
    (X ^ 4 = 1 → X ^ 5 = X) ∧
    (z ^ 5 = z → z = 0 ∨ z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I) :=
  grand_fourier_z4_slicing_synthesis X z

end InfoGeometry.Canonical
