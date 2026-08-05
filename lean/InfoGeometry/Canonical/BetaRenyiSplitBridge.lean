import Mathlib
import InfoGeometry.Canonical.QExponential
import InfoGeometry.Canonical.GeneralizedGibbsEvidence
import InfoGeometry.Canonical.BayesianMoebius

namespace InfoGeometry.Canonical

open Real

/-- The generalized Fermi-Möbius admission rule. -/
noncomputable def generalizedMoebiusAdmission (α q d ε : ℝ) : ℝ :=
  bayesUpdate (generalizedEvidence q d ε) α

/-- The non-linear translation theorem for Rényi-deformed flow. -/
theorem logit_generalizedMoebiusAdmission {α q d ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (h_dom : 1 - (1 - q) * (d / ε) > 0) :
    logit (generalizedMoebiusAdmission α q d ε) =
      logit α + Real.log (qExp q (-(d / ε))) := by
  dsimp [generalizedMoebiusAdmission, generalizedEvidence]
  have h_exp_pos : 0 < qExp q (-(d / ε)) := by
    dsimp [qExp]
    by_cases hq : q = 1
    · rw [if_pos hq]
      exact Real.exp_pos _
    · rw [if_neg hq]
      have h_dom2 : 1 + (1 - q) * (-(d / ε)) > 0 := by
        have h_sub : (1 - q) * (-(d / ε)) = - ((1 - q) * (d / ε)) := by ring
        rw [h_sub]
        exact h_dom
      have h_max : max (1 + (1 - q) * (-(d / ε))) 0 = 1 + (1 - q) * (-(d / ε)) := max_eq_left (le_of_lt h_dom2)
      rw [h_max]
      exact Real.rpow_pos_of_pos h_dom2 _
  exact logit_bayesUpdate (qExp q (-(d / ε))) α h_exp_pos hα0 hα1

end InfoGeometry.Canonical
