import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

namespace Omega.SyncKernelWeighted

/-- Laurent evaluation of a finitely supported coefficient field at `τ`. -/
def evalAt (tau : ℝ) (f : ℕ →₀ ℝ) : ℝ :=
  f.sum fun i a => a * tau ^ i

/-- The weighted value after one zero-injection step, written after exchanging the finite sums. -/
def updatedWeightedValue (tau : ℝ) (coeff z q : ℕ →₀ ℝ) : ℝ :=
  evalAt tau z - evalAt tau coeff * evalAt tau q

/-- After the finite-support reindexing, the correction term is exactly `Z(τ) * Q(τ)`, so
`Z(τ) = 0` cancels it.
    prop:zero-injection-value-preserving -/
theorem paper_zero_injection_value_preserving
    (tau : ℝ) (coeff z q : ℕ →₀ ℝ)
    (hzero : coeff.sum (fun i bi => bi * tau ^ i) = 0) :
    updatedWeightedValue tau coeff z q = evalAt tau z := by
  simp [updatedWeightedValue, evalAt, hzero]

end Omega.SyncKernelWeighted
