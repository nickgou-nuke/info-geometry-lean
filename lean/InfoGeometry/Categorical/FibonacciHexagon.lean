import InfoGeometry.Categorical.FibonacciBraiding

namespace FibonacciHexagon

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/--
Finite Fibonacci hexagon shadow.

This is a finite matrix readout of the Artin/Yang-Baxter relation for the
local `R` and `B = F R F` matrices. It is now completely unconditional, built
on the explicit algebraic verification over the quantum roots of unity.
-/
theorem fibonacci_hexagon_coherence (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    (fibonacciBMatrix q τ s) * fibonacciRMatrix q * (fibonacciBMatrix q τ s) =
      fibonacciRMatrix q * (fibonacciBMatrix q τ s) * fibonacciRMatrix q := by
  exact (fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs).symm

end FibonacciHexagon
