import InfoGeometry.Analysis.BipolarCrossRatioLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Cayley polarization, real occupation coordinates, and the critical line

The existing `cayleyToTemperature z = z/(1+z)` is the occupation chart only
on an appropriate real slice. The centered Cayley map `(z-1)/(z+1)` maps
the RIGHT half-plane to the disk. The upper-half-plane Cayley map instead
uses `i`, and a Euclidean Jordan tube-domain theorem needs additional data.

A change of coordinates neither changes an algebra's associator nor supplies
a dissipative evolution. On `s = 1/2 + i y`, the polarization is `2 i y`;
it vanishes only at the midpoint, not on the whole critical line.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarCayleyOccupation

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.CayleyCriticalLineCircleBridge

/-- Centered Cayley map; its analytic domain excludes `z = -1`. -/
def fugacityCayley (z : ℂ) : ℂ := (z - 1) / (z + 1)

/-- Affine centered occupation coordinate. It is complex on the complex chart. -/
def polarization (s : ℂ) : ℂ := 2 * s - 1

/-- Exact relation with the already installed inverse fugacity chart. -/
theorem fugacityCayley_eq_polarization (z : ℂ) (hz : z + 1 ≠ 0) :
    fugacityCayley z = polarization (cayleyToTemperature z) := by
  have hden : 1 + z ≠ 0 := by simpa [add_comm] using hz
  unfold fugacityCayley polarization cayleyToTemperature
  field_simp [hz, hden]
  ring

/-- The even denominator after substituting the canonical cross-ratio. -/
theorem crossRatio_add_one {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 s + 1 = (1 - s)⁻¹ := by
  unfold crossRatio01 cayleyToFugacity
  field_simp [one_sub_ne_zero_of_mem hs]
  ring

/-- The Cayley denominator does not vanish on the finite punctured chart. -/
theorem crossRatio_add_one_ne_zero {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 s + 1 ≠ 0 := by
  rw [crossRatio_add_one hs]
  exact inv_ne_zero (one_sub_ne_zero_of_mem hs)

/-- The centered Cayley map of the canonical cross-ratio is exactly `2s-1`. -/
theorem fugacityCayley_crossRatio {s : ℂ} (hs : s ∈ punctured01) :
    fugacityCayley (crossRatio01 s) = polarization s := by
  rw [fugacityCayley_eq_polarization _ (crossRatio_add_one_ne_zero hs)]
  congr 1
  exact cayleyToTemperature_cayleyToFugacity s (one_sub_ne_zero_of_mem hs)

/-- The Cayley map with real fixed points has the right-half-plane domain. -/
theorem fugacityCayley_normSq_lt_one_iff (z : ℂ) (hz : z + 1 ≠ 0) :
    Complex.normSq (fugacityCayley z) < 1 ↔ 0 < z.re := by
  have hpos : 0 < Complex.normSq (z + 1) := Complex.normSq_pos.mpr hz
  rw [fugacityCayley, Complex.normSq_div, div_lt_one hpos]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re,
    Complex.add_im, add_zero]
  constructor <;> intro h <;> nlinarith

/-- The exponential form of Cayley equals the native complex hyperbolic tangent
on the regular chart. -/
theorem fugacityCayley_exp (W : ℂ) (hW : Complex.exp W + 1 ≠ 0) :
    fugacityCayley (Complex.exp W) = Complex.tanh (W / 2) := by
  let a : ℂ := Complex.exp (W / 2)
  have ha : a ≠ 0 := Complex.exp_ne_zero _
  have he : Complex.exp W = a * a := by
    dsimp [a]
    rw [← Complex.exp_add]
    congr 1
    ring
  have haa : a * a + 1 ≠ 0 := by rwa [← he]
  have hs : a + a⁻¹ ≠ 0 := by
    intro h
    apply haa
    calc
      a * a + 1 = (a + a⁻¹) * a := by simp [add_mul, ha]
      _ = 0 := by rw [h, zero_mul]
  unfold fugacityCayley Complex.tanh Complex.sinh Complex.cosh
  rw [Complex.exp_neg, he]
  change (a * a - 1) / (a * a + 1) =
    ((a - a⁻¹) / 2) / ((a + a⁻¹) / 2)
  field_simp [ha, hs, haa]

/-- Exact recovery of the real logistic coordinate from complex fugacity. -/
theorem occupation_real_exp (t : ℝ) :
    cayleyToTemperature (Complex.exp (t : ℂ)) = (logistic t : ℂ) := by
  simp [cayleyToTemperature, logistic, ← Complex.ofReal_exp]

/-- Real rapidity becomes a bounded real polarization, not an arbitrary complex probability. -/
theorem real_polarization_eq_tanh (t : ℝ) :
    2 * logistic t - 1 = Real.tanh (t / 2) := by
  have hd : Complex.exp (t : ℂ) + 1 ≠ 0 := by
    rw [← Complex.ofReal_exp]
    have h : 0 < Real.exp t + 1 := by positivity
    exact_mod_cast ne_of_gt h
  have h := fugacityCayley_exp (t : ℂ) hd
  rw [fugacityCayley_eq_polarization _ hd, occupation_real_exp] at h
  have hr := congrArg Complex.re h
  simpa [polarization, Real.tanh, Complex.ofReal_div] using hr

/-- The real logarithmic odds coordinate. -/
def logOdds (p : ℝ) : ℝ := Real.log (p / (1 - p))

/-- The existing real logistic chart has the displayed inverse on `(0,1)`. -/
theorem logistic_logOdds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    logistic (logOdds p) = p := by
  have hden : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have hr : 0 < p / (1 - p) := div_pos hp0 (sub_pos.mpr hp1)
  unfold logistic logOdds
  rw [Real.exp_log hr]
  have hsum : 1 + p / (1 - p) ≠ 0 := ne_of_gt (by linarith)
  apply (div_eq_iff hsum).2
  field_simp [hden]
  ring

/-- Exact odds of the installed logistic map. -/
theorem logistic_odds (t : ℝ) :
    logistic t / (1 - logistic t) = Real.exp t := by
  have hd : 1 + Real.exp t ≠ 0 := by positivity
  have hp : 1 - logistic t ≠ 0 := ne_of_gt (sub_pos.mpr (logistic_lt_one t))
  apply (div_eq_iff hp).2
  unfold logistic
  field_simp [hd]
  ring

@[simp] theorem logOdds_logistic (t : ℝ) : logOdds (logistic t) = t := by
  rw [logOdds, logistic_odds, Real.log_exp]

/-- The real rapidity/occupation correspondence is a genuine equivalence. -/
def logisticEquiv : ℝ ≃ {p : ℝ // 0 < p ∧ p < 1} where
  toFun t := ⟨logistic t, logistic_pos t, logistic_lt_one t⟩
  invFun p := logOdds p.1
  left_inv := logOdds_logistic
  right_inv p := Subtype.ext (logistic_logOdds p.2.1 p.2.2)

/-- Strict boundedness of the real polarization. -/
theorem real_polarization_bounds (t : ℝ) :
    -1 < 2 * logistic t - 1 ∧ 2 * logistic t - 1 < 1 := by
  constructor <;> linarith [logistic_pos t, logistic_lt_one t]

/-- Polarization zero is a point condition, not merely a real-part condition. -/
theorem polarization_eq_zero_iff (s : ℂ) : polarization s = 0 ↔ s = 1 / 2 := by
  constructor
  · intro h
    unfold polarization at h
    linear_combination (1 / 2 : ℂ) * h
  · rintro rfl
    norm_num [polarization]

/-- The full critical line has purely imaginary polarization. -/
theorem polarization_criticalLine (y : ℝ) :
    polarization (criticalLine y) = (2 * y : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [polarization, criticalLine] <;> ring

/-- Only the midpoint on that line has zero polarization. -/
theorem criticalLine_polarization_zero_iff (y : ℝ) :
    polarization (criticalLine y) = 0 ↔ y = 0 := by
  rw [polarization_criticalLine]
  constructor
  · intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    linarith
  · rintro rfl
    simp

end InfoGeometry.Analysis.BipolarCayleyOccupation
