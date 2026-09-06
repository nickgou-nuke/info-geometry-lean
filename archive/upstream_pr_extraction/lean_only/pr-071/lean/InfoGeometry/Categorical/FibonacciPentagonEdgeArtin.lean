import InfoGeometry.Categorical.FibonacciPentagonPathCarrier
import InfoGeometry.Categorical.FibonacciSixAnyonMatrixArtin

/-!
# Adjacent Artin relations on the pentagon edge carrier

The five edge labels are path data.  This owner transports the four already
proved six-anyon Artin relations to that edge API; it does not identify braid
generators with categorical associators.
-/

namespace InfoGeometry.Categorical.FibonacciPentagonEdgeArtin

open InfoGeometry.Canonical.FiniteFibonacciLowAnyonMatrices
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
open InfoGeometry.Categorical.FibonacciPentagonPathCarrier
open InfoGeometry.Categorical.FibonacciSixAnyonMatrixArtin
open InfoGeometry.Categorical.FibonacciFourAnyonCarrier

theorem pentagonEdge_adjacent_artin_packet
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 -
      (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    (edgeMatrix .edge₁ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₁ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) =
      edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₁ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s)) ∧
    (edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) =
      edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₂ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s)) ∧
    (edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) =
      edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₃ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s)) ∧
    (edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₅ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) =
      edgeMatrix .edge₅ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₄ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s) *
        edgeMatrix .edge₅ (-(q : ℂ)) ((q : ℂ) ^ 3)
        (fibonacciBBlockEntries q τ s)) := by
  simpa [edgeMatrix] using
    (sixAnyon_adjacent_artin_packet q τ s hq_inv hq_pow3 hq5 h_poly hτ hs)

end InfoGeometry.Categorical.FibonacciPentagonEdgeArtin
