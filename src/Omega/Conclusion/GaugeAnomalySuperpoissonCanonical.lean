/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Omega.Conclusion.GaugeAnomalySuperpoissonFano

namespace Omega.Conclusion

open Filter

/-- The eventual nonvanishing hypothesis is unnecessary when the normalized mean converges
to the nonzero limit `4/9`. The ratio limit follows from the two normalized limits alone. -/
theorem gaugeAnomaly_ratio_limit_of_normalized_limits
    (mean variance : ℕ → ℝ)
    (hmean : Tendsto (fun m : ℕ => mean m / (m : ℝ)) atTop (nhds ((4 : ℝ) / 9)))
    (hvar : Tendsto (fun m : ℕ => variance m / (m : ℝ)) atTop
      (nhds ((118 : ℝ) / 243))) :
    Tendsto (fun m : ℕ => variance m / mean m) atTop (nhds ((59 : ℝ) / 54)) := by
  have hden_ne : ((4 : ℝ) / 9) ≠ 0 := by norm_num
  have hmean_ne : ∀ᶠ m : ℕ in atTop, mean m ≠ 0 := by
    filter_upwards [hmean.eventually (eventually_ne_nhds hden_ne),
      Filter.eventually_ge_atTop 1] with m hnorm hm
    have hm_ne : (m : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (show (0 : ℕ) < m by omega))
    have hparts := (div_ne_zero_iff).mp hnorm
    exact hparts.1
  exact (paper_conclusion_gauge_anomaly_superpoisson_fano mean variance hmean hvar hmean_ne).1

end Omega.Conclusion
