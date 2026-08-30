import InfoGeometry.SymmetricDomains.DikinMetriplectic

namespace InfoGeometry.Canonical.DikinMetriplecticCapstone

open InfoGeometry.SymmetricDomains.DikinMetriplectic

set_option linter.unusedVariables false

theorem verification_capstone
    (Y : TubeCoordinate) (v1 v2 r : ℝ) (hr_nonneg : 0 ≤ r) (hr_lt : r < 1)
    (h_in : dikinQuadraticForm Y v1 v2 ≤ r ^ 2)
    (x : ℝ) (st : MetriplecticState) :
    (universalLogBarrier Y = - Real.log (coneCharacteristicPoly Y)) ∧
      ((coneHessianMetric Y).det = 1 / (coneCharacteristicPoly Y) ^ 2) ∧
      (0 < Y.y1 + v1 ∧ 0 < Y.y2 + v2) ∧
      (0 ≤ Real.exp (-x) - 1 + x) ∧
      (0 ≤ st.dissipation_rate) := by
  exact grand_dikin_metriplectic_tube_synthesis Y v1 v2 r hr_nonneg hr_lt h_in x st

end InfoGeometry.Canonical.DikinMetriplecticCapstone
