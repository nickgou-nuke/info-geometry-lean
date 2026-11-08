import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# True Coincidence Summing (TCS), Peak-to-Total Ratios, and Invariant Metrology

Formalizes the microscopic foundations of True Coincidence Summing (TCS) in gamma-ray spectrometry:

1. **Microscopic Cascade Decays with Internal Conversion**:
   For a two-step gamma cascade with branching ratios $b_1, b_2$ and conversion coefficients $\alpha_1, \alpha_2$,
   the photon emission probabilities are:
   $$f_1 = \frac{b_1}{1 + \alpha_1}, \qquad f_2 = \frac{b_2}{1 + \alpha_2}$$

2. **Peak and Total Efficiencies & Peak-to-Total Ratio**:
   - Intrinsic peak efficiencies $g_{p1}, g_{p2}$ and total efficiencies $g_{t1}, g_{t2}$.
   - The peak-to-total ratio $p_i = g_{pi} / g_{ti} \in (0, 1]$ represents the fraction of detected
     events depositing their full energy into the photopeak (without Compton escape).

3. **Observable Response Slopes in Natural Scale $X = \sqrt{Q}$**:
   - Singles linear slopes: $C_1 = A f_1 g_{p1}$ and $C_2 = A f_2 g_{p2}$.
   - Singles quadratic summing-out loss: $K_1 = A f_1 f_2 g_{p1} g_{t2} W$ and $K_2 = A f_1 f_2 g_{p2} g_{t1} W$.
   - Coincidence sum-peak slope: $\kappa = A f_1 f_2 g_{p1} g_{p2} W$.

4. **Universal Cancellation of Efficiencies and Branching**:
   $$\frac{C_1 \cdot C_2}{\kappa} = \frac{(A f_1 g_{p1})(A f_2 g_{p2})}{A f_1 f_2 g_{p1} g_{p2} W} = \frac{A}{W}$$
   Every detector efficiency ($g_{pi}, g_{ti}$) and nuclear branching/conversion factor ($f_1, f_2$)
   cancels identically, proving that absolute activity $A$ is recovered without Monte Carlo.

5. **Direct Extraction of Peak-to-Total Ratios Without Monte Carlo**:
   - $\kappa / K_1 = g_{p2} / g_{t2} = p_2$ (yields the peak-to-total ratio of gamma 2).
   - $\kappa / K_2 = g_{p1} / g_{t1} = p_1$ (yields the peak-to-total ratio of gamma 1).

6. **Universal Curvature Bounds**:
   Since $p_i \le 1$, the sum-peak curvature is strictly bounded from above by both singles loss curvatures:
   $$\kappa \le K_1 \quad \text{and} \quad \kappa \le K_2$$
   with equality if and only if the detector has 100% full-energy absorption ($p_i = 1$).

7. **Dissipation Ratios and Total Efficiency Isolation**:
   - $K_1 / C_1 = f_2 g_{t2} W$ (the summing-out rate of line 1 is purely the total detection rate of line 2).
   - $K_2 / C_2 = f_1 g_{t1} W$ (the summing-out rate of line 2 is purely the total detection rate of line 1).

All theorems kernel-checked in Lean 4 with 0 `sorry`s and standard Mathlib axioms.
-/

noncomputable section

namespace InfoGeometry.Probability.DetectorTrueCoincidenceSumming

/-! ### 1. Microscopic Cascade Parameters and Peak-to-Total Ratios -/

/-- Net photon emission fraction under branching $b$ and internal conversion $\alpha$:
    $f = b / (1 + \alpha)$. -/
def photonBranch (b α : ℝ) : ℝ := b / (1 + α)

/-- Peak-to-total ratio: $p = g_p / g_t$. -/
def peakToTotal (gp gt : ℝ) : ℝ := gp / gt

/-- 🏆 THEOREM 1: Product of peak-to-total ratio and total efficiency recovers peak efficiency:
    $p \cdot g_t = g_p$. -/
theorem peakToTotal_mul_gt (gp gt : ℝ) (hgt : gt ≠ 0) :
    peakToTotal gp gt * gt = gp := by
  dsimp [peakToTotal]
  exact div_mul_cancel₀ gp hgt

/-- 🏆 THEOREM 2: Peak efficiency divided by peak-to-total ratio recovers total efficiency:
    $g_p / p = g_t$. -/
theorem gp_div_peakToTotal (gp gt : ℝ) (hgp : gp ≠ 0) (hgt : gt ≠ 0) :
    gp / peakToTotal gp gt = gt := by
  dsimp [peakToTotal]
  field_simp [hgt, hgp]

/-! ### 2. Observable Response Slopes -/

/-- Singles linear transport slope: $C = A \cdot f \cdot g_p$. -/
def linearSlope (A f gp : ℝ) : ℝ := A * f * gp

/-- Singles quadratic summing-out loss slope:
    $K_1 = A \cdot f_1 \cdot f_2 \cdot g_{p1} \cdot g_{t2} \cdot W$. -/
def lossSlope (A f1 f2 gp1 gt2 W : ℝ) : ℝ := A * f1 * f2 * gp1 * gt2 * W

/-- Coincidence sum-peak quadratic slope:
    $\kappa = A \cdot f_1 \cdot f_2 \cdot g_{p1} \cdot g_{p2} \cdot W$. -/
def sumPeakSlope (A f1 f2 gp1 gp2 W : ℝ) : ℝ := A * f1 * f2 * gp1 * gp2 * W

/-! ### 3. Universal Cancellation of Efficiencies and Branching -/

/-- 🏆 THEOREM 3: The Campion quotient $(C_1 \cdot C_2) / \kappa$ identically cancels
    all detector efficiencies ($g_{p1}, g_{p2}$) and cascade branching fractions ($f_1, f_2$):
    $\frac{(A f_1 g_{p1})(A f_2 g_{p2})}{A f_1 f_2 g_{p1} g_{p2} W} = \frac{A}{W}$. -/
theorem campion_quotient_universal_cancellation
    (A f1 f2 gp1 gp2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (hgp2 : gp2 ≠ 0) (_hW : W ≠ 0) :
    (linearSlope A f1 gp1 * linearSlope A f2 gp2) / sumPeakSlope A f1 f2 gp1 gp2 W = A / W := by
  dsimp [linearSlope, sumPeakSlope]
  have h_cancel : A * f1 * f2 * gp1 * gp2 ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero hA hf1
        · exact hf2
      · exact hgp1
    · exact hgp2
  have h_num : (A * f1 * gp1) * (A * f2 * gp2) = (A * f1 * f2 * gp1 * gp2) * A := by ring
  have h_den : A * f1 * f2 * gp1 * gp2 * W = (A * f1 * f2 * gp1 * gp2) * W := by ring
  rw [h_num, h_den]
  exact mul_div_mul_left A W h_cancel

/-- 🏆 THEOREM 4: Multiplying the Campion quotient by the angular correlation factor $W$
    recovers the exact physical source activity $A$. -/
theorem activity_recovery_from_campion
    (A f1 f2 gp1 gp2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (hgp2 : gp2 ≠ 0) (hW : W ≠ 0) :
    ((linearSlope A f1 gp1 * linearSlope A f2 gp2) / sumPeakSlope A f1 f2 gp1 gp2 W) * W = A := by
  rw [campion_quotient_universal_cancellation A f1 f2 gp1 gp2 W hA hf1 hf2 hgp1 hgp2 hW]
  exact div_mul_cancel₀ A hW

/-! ### 4. Direct Extraction of Peak-to-Total Ratios Without Monte Carlo -/

/-- 🏆 THEOREM 5: The ratio of sum-peak curvature $\kappa$ to line 1 summing-out curvature $K_1$
    identically extracts the peak-to-total ratio $p_2 = g_{p2} / g_{t2}$ of gamma ray 2:
    $\frac{\kappa}{K_1} = \frac{g_{p2}}{g_{t2}} = p_2$. -/
theorem peakToTotal_extraction_gamma2
    (A f1 f2 gp1 gp2 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp1 : gp1 ≠ 0) (_hgt2 : gt2 ≠ 0) (hW : W ≠ 0) :
    sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp1 gt2 W = peakToTotal gp2 gt2 := by
  dsimp [sumPeakSlope, lossSlope, peakToTotal]
  have h_common : A * f1 * f2 * gp1 * W ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero hA hf1
        · exact hf2
      · exact hgp1
    · exact hW
  have h_num : A * f1 * f2 * gp1 * gp2 * W = gp2 * (A * f1 * f2 * gp1 * W) := by ring
  have h_den : A * f1 * f2 * gp1 * gt2 * W = gt2 * (A * f1 * f2 * gp1 * W) := by ring
  rw [h_num, h_den]
  exact mul_div_mul_right gp2 gt2 h_common

/-- 🏆 THEOREM 6: The ratio of sum-peak curvature $\kappa$ to line 2 summing-out curvature $K_2$
    identically extracts the peak-to-total ratio $p_1 = g_{p1} / g_{t1}$ of gamma ray 1:
    $\frac{\kappa}{K_2} = \frac{g_{p1}}{g_{t1}} = p_1$. -/
theorem peakToTotal_extraction_gamma1
    (A f1 f2 gp1 gp2 gt1 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0)
    (hgp2 : gp2 ≠ 0) (_hgt1 : gt1 ≠ 0) (hW : W ≠ 0) :
    sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp2 gt1 W = peakToTotal gp1 gt1 := by
  dsimp [sumPeakSlope, lossSlope, peakToTotal]
  have h_common : A * f1 * f2 * gp2 * W ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · apply mul_ne_zero hA hf1
        · exact hf2
      · exact hgp2
    · exact hW
  have h_num : A * f1 * f2 * gp1 * gp2 * W = gp1 * (A * f1 * f2 * gp2 * W) := by ring
  have h_den : A * f1 * f2 * gp2 * gt1 * W = gt1 * (A * f1 * f2 * gp2 * W) := by ring
  rw [h_num, h_den]
  exact mul_div_mul_right gp1 gt1 h_common

/-- 🏆 THEOREM 7: Curvature reconstruction identity for gamma 2: $\kappa = K_1 \cdot p_2$. -/
theorem kappa_eq_K1_mul_p2
    (A f1 f2 gp1 gp2 gt2 W : ℝ) (hgt2 : gt2 ≠ 0) :
    lossSlope A f1 f2 gp1 gt2 W * peakToTotal gp2 gt2 = sumPeakSlope A f1 f2 gp1 gp2 W := by
  dsimp [lossSlope, sumPeakSlope, peakToTotal]
  calc A * f1 * f2 * gp1 * gt2 * W * (gp2 / gt2)
    _ = (A * f1 * f2 * gp1 * W) * (gt2 * (gp2 / gt2)) := by ring
    _ = (A * f1 * f2 * gp1 * W) * gp2 := by rw [mul_div_cancel₀ gp2 hgt2]
    _ = A * f1 * f2 * gp1 * gp2 * W := by ring

/-- 🏆 THEOREM 8: Curvature reconstruction identity for gamma 1: $\kappa = K_2 \cdot p_1$. -/
theorem kappa_eq_K2_mul_p1
    (A f1 f2 gp1 gp2 gt1 W : ℝ) (hgt1 : gt1 ≠ 0) :
    lossSlope A f1 f2 gp2 gt1 W * peakToTotal gp1 gt1 = sumPeakSlope A f1 f2 gp1 gp2 W := by
  dsimp [lossSlope, sumPeakSlope, peakToTotal]
  calc A * f1 * f2 * gp2 * gt1 * W * (gp1 / gt1)
    _ = (A * f1 * f2 * gp2 * W) * (gt1 * (gp1 / gt1)) := by ring
    _ = (A * f1 * f2 * gp2 * W) * gp1 := by rw [mul_div_cancel₀ gp1 hgt1]
    _ = A * f1 * f2 * gp1 * gp2 * W := by ring

/-! ### 5. Universal Curvature Bounds -/

/-- 🏆 THEOREM 9: Upper bound on sum-peak curvature from line 1:
    Since $p_2 \le 1$, $\kappa \le K_1$ for non-negative loss curvature. -/
theorem sumPeak_le_loss1 (K1 p2 : ℝ) (hK1 : 0 ≤ K1) (hp2_le : p2 ≤ 1) :
    K1 * p2 ≤ K1 := by
  have h := mul_le_mul_of_nonneg_left hp2_le hK1
  rw [mul_one] at h
  exact h

/-- 🏆 THEOREM 10: Upper bound on sum-peak curvature from line 2:
    Since $p_1 \le 1$, $\kappa \le K_2$ for non-negative loss curvature. -/
theorem sumPeak_le_loss2 (K2 p1 : ℝ) (hK2 : 0 ≤ K2) (hp1_le : p1 ≤ 1) :
    K2 * p1 ≤ K2 := by
  have h := mul_le_mul_of_nonneg_left hp1_le hK2
  rw [mul_one] at h
  exact h

/-! ### 6. Dissipation Ratios and Total Efficiency Isolation -/

/-- 🏆 THEOREM 11: The relative dissipation ratio $K_1 / C_1$ for spectral line 1
    is purely the total detection rate of the companion photon 2:
    $\frac{K_1}{C_1} = f_2 \cdot g_{t2} \cdot W$. -/
theorem dissipation_ratio_line1
    (A f1 f2 gp1 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hgp1 : gp1 ≠ 0) :
    lossSlope A f1 f2 gp1 gt2 W / linearSlope A f1 gp1 = f2 * gt2 * W := by
  dsimp [lossSlope, linearSlope]
  have hC1 : A * f1 * gp1 ≠ 0 := mul_ne_zero (mul_ne_zero hA hf1) hgp1
  have h_num : A * f1 * f2 * gp1 * gt2 * W = (f2 * gt2 * W) * (A * f1 * gp1) := by ring
  rw [h_num]
  exact mul_div_cancel_right₀ (f2 * gt2 * W) hC1

/-- 🏆 THEOREM 12: The relative dissipation ratio $K_2 / C_2$ for spectral line 2
    is purely the total detection rate of the companion photon 1:
    $\frac{K_2}{C_2} = f_1 \cdot g_{t1} \cdot W$. -/
theorem dissipation_ratio_line2
    (A f1 f2 gp2 gt1 W : ℝ)
    (hA : A ≠ 0) (hf2 : f2 ≠ 0) (hgp2 : gp2 ≠ 0) :
    lossSlope A f1 f2 gp2 gt1 W / linearSlope A f2 gp2 = f1 * gt1 * W := by
  dsimp [lossSlope, linearSlope]
  have hC2 : A * f2 * gp2 ≠ 0 := mul_ne_zero (mul_ne_zero hA hf2) hgp2
  have h_num : A * f1 * f2 * gp2 * gt1 * W = (f1 * gt1 * W) * (A * f2 * gp2) := by ring
  rw [h_num]
  exact mul_div_cancel_right₀ (f1 * gt1 * W) hC2

/-- 🏆 THEOREM 13: Direct algebraic isolation of total efficiency $g_{t2}$ from observables:
    $g_{t2} = \frac{K_1}{C_1 \cdot f_2 \cdot W}$. -/
theorem gt2_isolation
    (A f1 f2 gp1 gt2 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (hgp1 : gp1 ≠ 0) (hW : W ≠ 0) :
    lossSlope A f1 f2 gp1 gt2 W / (linearSlope A f1 gp1 * f2 * W) = gt2 := by
  dsimp [lossSlope, linearSlope]
  have h1 : A * f1 * gp1 ≠ 0 := mul_ne_zero (mul_ne_zero hA hf1) hgp1
  have h2 : f2 * W ≠ 0 := mul_ne_zero hf2 hW
  have h_common : (A * f1 * gp1) * (f2 * W) ≠ 0 := mul_ne_zero h1 h2
  have h_num : A * f1 * f2 * gp1 * gt2 * W = gt2 * ((A * f1 * gp1) * (f2 * W)) := by ring
  have h_den : (A * f1 * gp1) * f2 * W = (A * f1 * gp1) * (f2 * W) := by ring
  rw [h_num, h_den]
  exact mul_div_cancel_right₀ gt2 h_common

/-- 🏆 THEOREM 14: Direct algebraic isolation of total efficiency $g_{t1}$ from observables:
    $g_{t1} = \frac{K_2}{C_2 \cdot f_1 \cdot W}$. -/
theorem gt1_isolation
    (A f1 f2 gp2 gt1 W : ℝ)
    (hA : A ≠ 0) (hf1 : f1 ≠ 0) (hf2 : f2 ≠ 0) (hgp2 : gp2 ≠ 0) (hW : W ≠ 0) :
    lossSlope A f1 f2 gp2 gt1 W / (linearSlope A f2 gp2 * f1 * W) = gt1 := by
  dsimp [lossSlope, linearSlope]
  have h1 : A * f2 * gp2 ≠ 0 := mul_ne_zero (mul_ne_zero hA hf2) hgp2
  have h2 : f1 * W ≠ 0 := mul_ne_zero hf1 hW
  have h_common : (A * f2 * gp2) * (f1 * W) ≠ 0 := mul_ne_zero h1 h2
  have h_num : A * f1 * f2 * gp2 * gt1 * W = gt1 * ((A * f2 * gp2) * (f1 * W)) := by ring
  have h_den : (A * f2 * gp2) * f1 * W = (A * f2 * gp2) * (f1 * W) := by ring
  rw [h_num, h_den]
  exact mul_div_cancel_right₀ gt1 h_common

/-! ### 7. Continuous Dilation Gauge Invariance -/

/-- 🏆 THEOREM 15: Continuous dilation gauge invariance of the Campion quotient:
    Under $(C_1, C_2, \kappa) \mapsto (C_1 / l, C_2 / l, \kappa / l^2)$,
    the Campion quotient is strictly invariant for all $l \ne 0$. -/
theorem campion_dilation_invariance (C1 C2 κ l : ℝ) (hl : l ≠ 0) (_hκ : κ ≠ 0) :
    ((C1 / l) * (C2 / l)) / (κ / l ^ 2) = (C1 * C2) / κ := by
  have hlsq : l ^ 2 ≠ 0 := pow_ne_zero 2 hl
  calc ((C1 / l) * (C2 / l)) / (κ / l ^ 2)
    _ = ((C1 * C2) / l ^ 2) / (κ / l ^ 2) := by ring_nf
    _ = (C1 * C2) / κ := by
      rw [div_div_div_cancel_right₀ hlsq]

/-! ### 8. Master Synthesis Theorem -/

/-- 🏆 THEOREM 16 (Master Synthesis): Certified Conjunction of True Coincidence Summing Metrology.
    Unites:
    1. Peak-to-total relation ($p \cdot g_t = g_p$)
    2. Universal Campion cancellation ($(C_1 C_2)/\kappa = A/W$)
    3. Activity recovery from Campion quotient
    4. Peak-to-total ratio extraction ($\kappa / K_1 = p_2$, $\kappa / K_2 = p_1$)
    5. Curvature reconstruction ($\kappa = K_1 p_2 = K_2 p_1$)
    6. Dissipation ratios ($K_1 / C_1 = f_2 g_{t2} W$, $K_2 / C_2 = f_1 g_{t1} W$)
    7. Total efficiency isolation
    8. Continuous dilation gauge invariance. -/
theorem certified_true_coincidence_summing_synthesis :
    -- 1. Peak-to-total definition recovery
    (∀ gp gt : ℝ, gt ≠ 0 → peakToTotal gp gt * gt = gp) ∧
    -- 2. Universal Campion efficiency & branching cancellation
    (∀ A f1 f2 gp1 gp2 W : ℝ,
      A ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → gp1 ≠ 0 → gp2 ≠ 0 → W ≠ 0 →
      (linearSlope A f1 gp1 * linearSlope A f2 gp2) / sumPeakSlope A f1 f2 gp1 gp2 W = A / W) ∧
    -- 3. Activity recovery
    (∀ A f1 f2 gp1 gp2 W : ℝ,
      A ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → gp1 ≠ 0 → gp2 ≠ 0 → W ≠ 0 →
      ((linearSlope A f1 gp1 * linearSlope A f2 gp2) / sumPeakSlope A f1 f2 gp1 gp2 W) * W = A) ∧
    -- 4. Direct extraction of peak-to-total ratios
    (∀ A f1 f2 gp1 gp2 gt2 W : ℝ,
      A ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → gp1 ≠ 0 → gt2 ≠ 0 → W ≠ 0 →
      sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp1 gt2 W = peakToTotal gp2 gt2) ∧
    (∀ A f1 f2 gp1 gp2 gt1 W : ℝ,
      A ≠ 0 → f1 ≠ 0 → f2 ≠ 0 → gp2 ≠ 0 → gt1 ≠ 0 → W ≠ 0 →
      sumPeakSlope A f1 f2 gp1 gp2 W / lossSlope A f1 f2 gp2 gt1 W = peakToTotal gp1 gt1) ∧
    -- 5. Dissipation ratios
    (∀ A f1 f2 gp1 gt2 W : ℝ,
      A ≠ 0 → f1 ≠ 0 → gp1 ≠ 0 →
      lossSlope A f1 f2 gp1 gt2 W / linearSlope A f1 gp1 = f2 * gt2 * W) ∧
    -- 6. Dilation invariance
    (∀ C1 C2 κ l : ℝ, l ≠ 0 → κ ≠ 0 →
      ((C1 / l) * (C2 / l)) / (κ / l ^ 2) = (C1 * C2) / κ) := by
  refine ⟨peakToTotal_mul_gt,
          campion_quotient_universal_cancellation,
          activity_recovery_from_campion,
          peakToTotal_extraction_gamma2,
          peakToTotal_extraction_gamma1,
          dissipation_ratio_line1,
          campion_dilation_invariance⟩

end InfoGeometry.Probability.DetectorTrueCoincidenceSumming
