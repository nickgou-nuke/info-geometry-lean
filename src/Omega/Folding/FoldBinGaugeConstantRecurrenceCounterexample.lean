import Mathlib.Algebra.LinearRecurrence
import Omega.Folding.FoldBinGaugeConstantNotCFinite

namespace Omega.Folding

/-- The exponential scale `2^n` has a genuine order-one linear recurrence. -/
def foldBinGaugeScaleRecurrence : LinearRecurrence ℝ where
  order := 1
  coeffs := fun _ => 2

theorem foldBinGaugeScale_is_linearRecurrence_solution :
    foldBinGaugeScaleRecurrence.IsSolution
      fold_bin_gauge_constant_not_c_finite_exponentialScale := by
  intro n
  change (2 : ℝ) ^ (n + 1) =
    ∑ i : Fin 1, (2 : ℝ) * (2 : ℝ) ^ (n + (i : ℕ))
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.add_zero]
  rw [pow_succ]
  ring

/-- The sequence used by the finite-range surrogate is linearly recurrent even
though its value set is infinite. Thus finite range is not a C-finite criterion. -/
theorem exponentialScale_recurrence_refutes_finiteRange_surrogate :
    (∃ E : LinearRecurrence ℝ,
      E.IsSolution fold_bin_gauge_constant_not_c_finite_exponentialScale) ∧
      ¬ fold_bin_gauge_constant_not_c_finite_isCFinite := by
  refine ⟨⟨foldBinGaugeScaleRecurrence,
    foldBinGaugeScale_is_linearRecurrence_solution⟩, ?_⟩
  exact fold_bin_gauge_constant_not_c_finite_not_isCFinite
    fold_bin_gauge_constant_not_c_finite_infiniteExponentialScaleFamily_true

end Omega.Folding
