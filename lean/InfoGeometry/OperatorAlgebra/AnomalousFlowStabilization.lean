import Mathlib.Tactic

namespace InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization

theorem additive_flow_zero
    {State : Type*}
    (flow : ℝ → State → State)
    (hadd : ∀ s t x, flow (s + t) x = flow s (flow t x))
    (hzero : ∀ x, flow 0 x = x)
    (x : State) :
    flow 0 x = x := by
  calc
    flow 0 x = flow (0 + 0) x := by rw [zero_add]
    _ = flow 0 (flow 0 x) := hadd 0 0 x
    _ = flow 0 x := by rw [hzero]
    _ = x := hzero x

end InfoGeometry.OperatorAlgebra.AnomalousFlowStabilization
