import InfoGeometry.Categorical.FibonacciBraiding

namespace InfoGeometry.Categorical.FibonacciHexagon

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/--
Finite Fibonacci hexagon shadow.

This is a finite matrix readout of the Artin/Yang-Baxter relation for the
local `R` and `B = F R F` matrices.  It is intentionally conditional on the
explicit matrix identity and does not install a categorical instance or a
categorical coherence theorem.
-/
theorem fibonacci_hexagon_coherence (q : Units ℂ) (τ s : ℂ)
    (h_artin :
      fibonacciRMatrix q * (fibonacciBMatrix q τ s) * fibonacciRMatrix q =
        (fibonacciBMatrix q τ s) * fibonacciRMatrix q * (fibonacciBMatrix q τ s)) :
    (fibonacciBMatrix q τ s) * fibonacciRMatrix q * (fibonacciBMatrix q τ s) =
      fibonacciRMatrix q * (fibonacciBMatrix q τ s) * fibonacciRMatrix q := by
  exact h_artin.symm

end InfoGeometry.Categorical.FibonacciHexagon
