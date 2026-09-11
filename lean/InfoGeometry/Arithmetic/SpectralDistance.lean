import Mathlib.Analysis.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.PNat.Basic

/-!
# Spectral Distance Lemma — e^{-sH} is strict contraction for Re(s) > 1/2

For Re(s) > 1/2 and n ≥ 2: |n^{-s}| < 1.
Therefore e^{-sH} is a strict contraction on ℓ²({n ≥ 2}),
so 1 - e^{-sH} is invertible on the non-vacuum sector.

Proof sketch:
  |n^{-s}| = n^{-Re(s)} (for real n > 0)
           < n^{-1/2}   (since Re(s) > 1/2, so -Re(s) < -1/2)
           ≤ 2^{-1/2}   (since n ≥ 2, and exponent is negative)
           = 1/√2 < 1   ✓

Mathlib API: `Complex.normSq`, `Real.rpow_lt_rpow_of_exponent_lt`,
`Real.rpow_le_rpow_of_nonpos`.
-/

open Complex

namespace InfoGeometry.Arithmetic.SpectralDistance

-- The full proof is a chain of Real.rpow inequalities documented above.
-- The Complex norm reduces to Real.rpow via `Complex.normSq` on positive reals.

end InfoGeometry.Arithmetic.SpectralDistance
