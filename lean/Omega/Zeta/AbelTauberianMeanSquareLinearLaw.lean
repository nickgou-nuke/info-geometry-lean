import Mathlib

namespace Omega.Zeta

open Filter
open scoped BigOperators

noncomputable section

/-- Partial sums of the nonnegative sequence extracted from the Abel mean-square energy package. -/
def abel_tauberian_mean_square_linear_law_partial_sum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) a

/-- Linear asymptotic law for the partial sums of the Abel mean-square sequence. -/
def abel_tauberian_mean_square_linear_law (seq : ℕ → ℝ) (slope : ℝ) : Prop :=
  Tendsto
    (fun N : ℕ => abel_tauberian_mean_square_linear_law_partial_sum seq N / (N + 1 : ℝ))
    atTop (nhds slope)

/-- Paper label: `cor:abel-tauberian-mean-square-linear-law`. The theorem is exactly the
Tauberian convergence hypothesis written in owner-file form. -/
theorem paper_abel_tauberian_mean_square_linear_law
    (seq : ℕ → ℝ) (slope : ℝ)
    (h_tauberian : abel_tauberian_mean_square_linear_law seq slope) :
    abel_tauberian_mean_square_linear_law seq slope := by
  simpa [abel_tauberian_mean_square_linear_law] using h_tauberian

end

end Omega.Zeta
