import Mathlib.Algebra.LinearRecurrence
import Omega.Zeta.XiTimePart60abGaugeConstantNonCfiniteOgfObstruction

namespace Omega.Zeta.XiTimePart60abOddModesRecurrenceCounterexample

/-- The constant-one sequence has nonzero coefficients at every odd index. -/
def constantOneSequence : ℕ → ℝ := fun _ => 1

/-- The order-one recurrence `a (n + 1) = a n`. -/
def constantOneRecurrence : LinearRecurrence ℝ where
  order := 1
  coeffs := fun _ => 1

/-- Constant one is a genuine Mathlib linear-recurrence solution. -/
theorem constantOneRecurrence_solution :
    constantOneRecurrence.IsSolution constantOneSequence := by
  intro n
  change 1 = ∑ i : Fin 1, (1 : ℝ) * 1
  rw [Fin.sum_univ_one]
  norm_num

theorem constantOne_odd_coefficients_nonzero :
    ∀ r : ℕ, constantOneSequence (2 * r + 1) ≠ 0 := by
  intro r
  simp [constantOneSequence]

/-- The local odd-mode predicate from the Xi owner rejects a sequence that
does satisfy an ordinary constant-coefficient linear recurrence. This shows
that eventual vanishing of odd coefficients is not a characterization of
linear-recurrence sequences. -/
theorem recurrence_not_implying_local_odd_mode_cfinite :
    (∃ E : LinearRecurrence ℝ, E.IsSolution constantOneSequence) ∧
      (∀ r : ℕ, constantOneSequence (2 * r + 1) ≠ 0) ∧
      ¬ Omega.Zeta.paper_xi_time_part60ab_gauge_constant_non_cfinite_ogf_obstruction_local_cfinite
        constantOneSequence := by
  refine ⟨⟨constantOneRecurrence, constantOneRecurrence_solution⟩,
    constantOne_odd_coefficients_nonzero, ?_⟩
  rintro ⟨N, hN⟩
  have hzero := hN N le_rfl
  norm_num [constantOneSequence] at hzero

end Omega.Zeta.XiTimePart60abOddModesRecurrenceCounterexample
