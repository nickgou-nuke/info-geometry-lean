import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Categorical.FibonacciBraiding

Theorem-safe categorical surface for finite Fibonacci fusion/matrix data, stated
directly with the canonical matrices from `FiniteFibonacciFusionMatrix`.

This file does not package parameters or witnesses.  It does not claim a full
braid-group representation theorem, analytic continuation, conformal-block
construction, or universal topological quantum-computing theorem.
-/

namespace InfoGeometry.Categorical.FibonacciBraiding

open Matrix
open InfoGeometry.Canonical.FiniteFibonacciFusionMatrix

/-- The finite Fibonacci fusion matrix is involutive under the explicit scalar relations. -/
theorem F_sq (τ s : ℂ) (s_sq : s ^ 2 = τ) (tau_sq_add_tau : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 := by
  simpa using (fibonacciFusionMatrix_sq s_sq tau_sq_add_tau)

/-- The finite Fibonacci fusion matrix has determinant `-1` under the explicit scalar relations. -/
theorem det_F (τ s : ℂ) (s_sq : s ^ 2 = τ) (tau_sq_add_tau : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrix τ s).det = -1 := by
  simpa using (det_fibonacciFusionMatrix s_sq tau_sq_add_tau)

/-- The finite middle generator is definitionally `F R F`. -/
theorem B_eq_FRF (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s =
      fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s := by
  change fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s =
      fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s
  rfl

/-- The explicit unconditionally verified Artin matrix identity. -/
theorem artin_relation
    (q : Units ℂ) (τ s : ℂ)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3)
    (hs : s ^ 2 = τ) :
    fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
      fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s :=
  fibonacci_fourAnyon_artin q τ s hq_inv hq_pow3 hq5 h_poly hτ hs

/--
Finite matrix shadow of the Fibonacci hexagon data.

This theorem intentionally packages only kernel-checked finite matrix facts:
`F² = 1`, `det F = -1`, `B = F R F`, and the explicitly verified Artin/Yang-Baxter
matrix identity. It is not a `BraidedCategory` instance; a real instance still
requires categorical objects, tensor product, associator, braiding natural
isomorphisms, and pentagon/hexagon coherence proofs.
-/
theorem finite_hexagon_shadow
    (q : Units ℂ) (τ s : ℂ)
    (s_sq : s ^ 2 = τ)
    (tau_sq_add_tau : τ ^ 2 + τ = 1)
    (hq_inv : (q ^ (-4 : ℤ) : ℂ) = - (q : ℂ))
    (hq_pow3 : (q ^ (3 : ℤ) : ℂ) = (q : ℂ) ^ 3)
    (hq5 : (q : ℂ) ^ 5 = -1)
    (h_poly : (q : ℂ) ^ 4 - (q : ℂ) ^ 3 + (q : ℂ) ^ 2 - (q : ℂ) + 1 = 0)
    (hτ : τ = (q : ℂ) ^ 2 - (q : ℂ) ^ 3) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1 ∧
      (fibonacciFusionMatrix τ s).det = -1 ∧
      fibonacciBMatrix q τ s =
        fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s ∧
      fibonacciRMatrix q * fibonacciBMatrix q τ s * fibonacciRMatrix q =
        fibonacciBMatrix q τ s * fibonacciRMatrix q * fibonacciBMatrix q τ s := by
  exact ⟨
    F_sq τ s s_sq tau_sq_add_tau,
    det_F τ s s_sq tau_sq_add_tau,
    B_eq_FRF q τ s,
    artin_relation q τ s hq_inv hq_pow3 hq5 h_poly hτ s_sq⟩

end InfoGeometry.Categorical.FibonacciBraiding
