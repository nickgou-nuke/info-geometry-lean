import Mathlib
import InfoGeometry.Canonical.QExponential
import InfoGeometry.Canonical.BayesianMoebius

namespace InfoGeometry.Canonical

open Real

/-- The generalized Gibbs-Boltzmann evidence factor for q-deformed noise models.
    b_{β,q} = exp_q ( - d_β / ε ) -/
noncomputable def generalizedEvidence (q d ε : ℝ) : ℝ :=
  qExp q (-(d / ε))

/-- The domain-qualified identity for the energy-to-flow log-map. -/
theorem qLog_generalizedEvidence {q d ε : ℝ} (hq : q ≠ 1)
    (h_dom : 1 - (1 - q) * (d / ε) > 0) :
    qLog q (generalizedEvidence q d ε) = - (d / ε) := by
  dsimp [generalizedEvidence]
  have h_dom2 : 1 + (1 - q) * (-(d / ε)) > 0 := by
    have h_sub : (1 - q) * (-(d / ε)) = - ((1 - q) * (d / ε)) := by ring
    rw [h_sub]
    exact h_dom
  exact qLog_qExp_self hq h_dom2

end InfoGeometry.Canonical
