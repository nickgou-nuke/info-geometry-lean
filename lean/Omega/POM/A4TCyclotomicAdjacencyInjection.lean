import Mathlib.Tactic

namespace Omega.POM

theorem a4t_cyclotomic_adjacency_injection_corrected_core_identity {v : Real} (hv : v ≠ 0) :
    let t : Real := -2 * v^2 + 1 / v^2 - 2 * (v^3 - 1 / v)
    1 + 2 * v - t * v^2 - 2 * v^4 - 2 * v^5 = 0 := by
  dsimp
  have hv2 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv
  field_simp [hv, hv2]
  ring

/- Exact residual of the target-sign expression at the fourth cyclotomic angle.
The corrected core expression above vanishes, while this alternate-sign expression
has the explicit nonzero defect `-3 * sqrt 2 / 2`. -/
theorem a4t_cyclotomic_adjacency_injection_target_defect_exact :
    let c : Real := 2 * Real.cos (Real.pi / (4 : Real))
    let v : Real := 1 / c
    let t : Real := -2 * v^2 + 1 / v^2 - 2 * (v^3 - 1 / v)
    1 - 2 * v - t * v^2 - 2 * v^4 + 2 * v^5 = -(3 / 2 * Real.sqrt 2) := by
  dsimp
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]
  have hsqrt2_four : (Real.sqrt 2) ^ 4 = 4 := by
    calc
      (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [hsqrt2_sq]
      _ = 4 := by norm_num
  have hsqrt2_five : (Real.sqrt 2) ^ 5 = 4 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2) ^ 5 = (Real.sqrt 2) ^ 4 * Real.sqrt 2 := by ring
      _ = 4 * Real.sqrt 2 := by rw [hsqrt2_four]
  have hsqrt2_six : (Real.sqrt 2) ^ 6 = 8 := by
    calc
      (Real.sqrt 2) ^ 6 = (Real.sqrt 2) ^ 4 * (Real.sqrt 2) ^ 2 := by ring
      _ = 4 * 2 := by rw [hsqrt2_four, hsqrt2_sq]
      _ = 8 := by norm_num
  rw [Real.cos_pi_div_four]
  field_simp [hsqrt2_ne]
  ring_nf
  nlinarith [hsqrt2_sq, hsqrt2_four, hsqrt2_five, hsqrt2_six]

theorem a4t_cyclotomic_adjacency_injection_target_counterexample :
    let c : Real := 2 * Real.cos (Real.pi / (4 : Real))
    let v : Real := 1 / c
    let t : Real := -2 * v^2 + 1 / v^2 - 2 * (v^3 - 1 / v)
    1 - 2 * v - t * v^2 - 2 * v^4 + 2 * v^5 ≠ 0 := by
  dsimp
  have h := a4t_cyclotomic_adjacency_injection_target_defect_exact
  dsimp at h
  rw [h]
  exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) (by positivity))

theorem paper_pom_a4t_cyclotomic_adjacency_injection (h : ℕ) (hh : 4 ≤ h) :
    let c : Real := 2 * Real.cos (Real.pi / (h : Real))
    let v : Real := 1 / c
    let t : Real := -2 * v^2 + 1 / v^2 - 2 * (v^3 - 1 / v)
    1 + 2 * v - t * v^2 - 2 * v^4 - 2 * v^5 = 0 := by
  dsimp
  apply a4t_cyclotomic_adjacency_injection_corrected_core_identity
  have hfour : (4 : Real) ≤ h := by exact_mod_cast hh
  have hinv : (1 : Real) / (h : Real) ≤ 1 / (4 : Real) := by
    exact one_div_le_one_div_of_le (show (0 : Real) < 4 by norm_num) hfour
  have hquarter : Real.pi / (h : Real) ≤ Real.pi / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
    simpa [div_eq_mul_inv, one_div] using hmul
  have hhalf : Real.pi / (4 : Real) < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hcos_pos : 0 < Real.cos (Real.pi / (h : Real)) := by
    have hpos : 0 < Real.pi / (h : Real) := by
      exact div_pos Real.pi_pos (by positivity)
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, ?_⟩
    exact lt_of_le_of_lt hquarter hhalf
  have hcne : (2 * Real.cos (Real.pi / (h : Real))) ≠ 0 := ne_of_gt (by positivity)
  exact one_div_ne_zero hcne

end Omega.POM
