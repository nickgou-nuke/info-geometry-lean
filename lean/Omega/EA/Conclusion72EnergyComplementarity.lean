import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- The strict Perron-gap hypothesis on the joint synchronous collision graph converts directly into
the logarithmic energy-complementarity inequality after taking logs of the compiled growth rates.
    thm:conclusion72-energy-complementarity -/
theorem paper_conclusion72_energy_complementarity
    (alpha betaAdd betaMul kappa : ℝ)
    (alpha_pos : 0 < alpha) (betaAdd_pos : 0 < betaAdd)
    (betaMul_pos : 0 < betaMul)
    (jointGap : betaAdd * betaMul ≤ alpha ^ (6 : ℕ) * Real.exp (-kappa)) :
    Real.log betaAdd + Real.log betaMul ≤ 6 * Real.log alpha - kappa := by
  have hprod_pos : 0 < betaAdd * betaMul := mul_pos betaAdd_pos betaMul_pos
  have hlog :
      Real.log (betaAdd * betaMul) ≤ Real.log (alpha ^ (6 : ℕ) * Real.exp (-kappa)) := by
    exact Real.log_le_log hprod_pos jointGap
  rw [Real.log_mul betaAdd_pos.ne' betaMul_pos.ne'] at hlog
  rw [Real.log_mul (pow_ne_zero _ alpha_pos.ne') (Real.exp_ne_zero _)] at hlog
  have hpowlog : Real.log (alpha ^ (6 : ℕ)) = 6 * Real.log alpha := by
    simpa using (Real.log_rpow alpha_pos (6 : ℝ))
  calc
    Real.log betaAdd + Real.log betaMul
        ≤ Real.log (alpha ^ (6 : ℕ)) + Real.log (Real.exp (-kappa)) := hlog
    _ = 6 * Real.log alpha - kappa := by rw [hpowlog, Real.log_exp]; ring

end Omega.EA
