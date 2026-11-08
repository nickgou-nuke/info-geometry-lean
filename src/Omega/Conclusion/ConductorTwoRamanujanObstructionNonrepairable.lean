import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The fixed base coefficient `2` used by this abstract parity-channel model.
No arithmetic sequence or Ramanujan coefficient interpretation is defined in
this file. -/
noncomputable def conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one :
    ℝ :=
  2

/-- The logarithmic ratio `log 2 / log(φ²)` for the chosen model constant. -/
noncomputable def conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par : ℝ :=
  Real.log conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one /
    Real.log (Real.goldenRatio ^ 2)

/-- The model sequence `2^n`. -/
noncomputable def conclusion_conductor_two_ramanujan_obstruction_nonrepairable_base_coeff
    (n : ℕ) : ℝ :=
  conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one ^ n

/-- A finitely supported coefficient change, represented by a polynomial. -/
noncomputable def conclusion_conductor_two_ramanujan_obstruction_nonrepairable_surgery_coeff
    (R : Polynomial ℝ) (n : ℕ) : ℝ :=
  conclusion_conductor_two_ramanujan_obstruction_nonrepairable_base_coeff n + R.coeff n

lemma conclusion_conductor_two_ramanujan_obstruction_nonrepairable_eventually_eq
    (R : Polynomial ℝ) :
    ∃ N : ℕ,
      ∀ n ≥ N,
        conclusion_conductor_two_ramanujan_obstruction_nonrepairable_surgery_coeff R n =
          conclusion_conductor_two_ramanujan_obstruction_nonrepairable_base_coeff n := by
  refine ⟨R.natDegree + 1, ?_⟩
  intro n hn
  have hdeg : R.natDegree < n := by omega
  unfold conclusion_conductor_two_ramanujan_obstruction_nonrepairable_surgery_coeff
    conclusion_conductor_two_ramanujan_obstruction_nonrepairable_base_coeff
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, add_zero]

lemma conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par_gt_half :
    1 / 2 <
      conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par := by
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
  have hlog_phi_pos : 0 < Real.log Real.goldenRatio := Real.log_pos Real.one_lt_goldenRatio
  have hlog_phi_lt_log_two : Real.log Real.goldenRatio < Real.log 2 := by
    exact Real.log_lt_log hphi_pos hphi_lt_two
  have hlog_sq :
      Real.log (Real.goldenRatio ^ 2) = 2 * Real.log Real.goldenRatio := by
    rw [pow_two, Real.log_mul (ne_of_gt hphi_pos) (ne_of_gt hphi_pos)]
    ring
  have hden_pos :
      0 < Real.log (Real.goldenRatio ^ 2) := by
    rw [hlog_sq]
    positivity
  unfold conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par
    conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one
  rw [hlog_sq]
  have hhalf :
      (1 / 2 : ℝ) = Real.log Real.goldenRatio / (2 * Real.log Real.goldenRatio) := by
    field_simp [hlog_phi_pos.ne', show (2 : ℝ) ≠ 0 by norm_num]
  rw [hhalf]
  have hrecip_pos : 0 < (2 * Real.log Real.goldenRatio)⁻¹ := by
    positivity
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_lt_mul_of_pos_right hlog_phi_lt_log_two hrecip_pos

/-- In the abstract sequence `2^n`, adding any polynomial coefficient correction
leaves the sequence unchanged eventually, and the fixed logarithmic ratio is
greater than `1/2`. This does not identify the model sequence with Ramanujan
coefficients or prove an arithmetic nonrepairability result. -/
theorem paper_conclusion_conductor_two_ramanujan_obstruction_nonrepairable :
    conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one >
        Real.goldenRatio ∧
      1 / 2 < conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par ∧
      ∀ R : Polynomial ℝ,
        ∃ N : ℕ,
          ∀ n ≥ N,
            conclusion_conductor_two_ramanujan_obstruction_nonrepairable_surgery_coeff R n =
              conclusion_conductor_two_ramanujan_obstruction_nonrepairable_base_coeff n := by
  refine ⟨?_, conclusion_conductor_two_ramanujan_obstruction_nonrepairable_beta_par_gt_half, ?_⟩
  · simpa [conclusion_conductor_two_ramanujan_obstruction_nonrepairable_rho_minus_one] using
      Real.goldenRatio_lt_two
  · intro R
    exact conclusion_conductor_two_ramanujan_obstruction_nonrepairable_eventually_eq R

end Omega.Conclusion
