import Mathlib

namespace InfoGeometry.Canonical.HagedornKMSBoundary

variable (β : ℝ)
variable (chiral_anomaly : ℝ → ℝ)

/-- Explicit scaling law for a concrete anomaly model.  This is a hypothesis,
not a kernel axiom: arbitrary functions `ℝ → ℝ` need not satisfy it. -/
def ModularAnomalyScaling (c : ℝ) : Prop :=
  ∀ b, chiral_anomaly b = c * (b - 1)

/-- If a concrete anomaly model scales by `(β - 1)`, then it vanishes at
`β = 1`.  This is the theorem-safe algebraic core only; no KMS/orientifold
classification theorem is asserted. -/
theorem hagedorn_anomaly_cancellation (c : ℝ)
    (h_scaling : ModularAnomalyScaling chiral_anomaly c)
    (h_hagedorn : β = 1) :
    chiral_anomaly β = 0 := by
  rw [h_scaling β, h_hagedorn]
  ring

end InfoGeometry.Canonical.HagedornKMSBoundary
