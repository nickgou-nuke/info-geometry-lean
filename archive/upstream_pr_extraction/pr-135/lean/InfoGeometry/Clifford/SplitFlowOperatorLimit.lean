import Mathlib
import InfoGeometry.Clifford.Cl55SplitRoutingWeights

open Filter Topology

namespace InfoGeometry.Clifford.SplitFlowOperatorLimit

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E]
  [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

noncomputable def normalizedTwoLaneFlow (P Q : E) (t : ℝ) : E :=
  Cl55SplitRoutingWeights.normalizedPlus t • P +
    Cl55SplitRoutingWeights.normalizedMinus t • Q

/-!
This is the operator-valued continuity interface for a two-lane split flow.
It deliberately assumes only the scalar coefficient limits; no projector or
routing interpretation is built into the statement.
-/
theorem tendsto_two_lane_smul_add
    {a b : ℝ → ℝ} {P Q : E}
    (ha : Tendsto a atTop (𝓝 (1 : ℝ)))
    (hb : Tendsto b atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun t => a t • P + b t • Q) atTop (𝓝 P) := by
  have hP : Tendsto (fun t => a t • P) atTop (𝓝 ((1 : ℝ) • P)) :=
    ha.smul_const P
  have hQ : Tendsto (fun t => b t • Q) atTop (𝓝 ((0 : ℝ) • Q)) :=
    hb.smul_const Q
  simpa using hP.add hQ

theorem tendsto_two_lane_smul_add_atBot
    {a b : ℝ → ℝ} {P Q : E}
    (ha : Tendsto a atBot (𝓝 (0 : ℝ)))
    (hb : Tendsto b atBot (𝓝 (1 : ℝ))) :
    Tendsto (fun t => a t • P + b t • Q) atBot (𝓝 Q) := by
  have hP : Tendsto (fun t => a t • P) atBot (𝓝 ((0 : ℝ) • P)) :=
    ha.smul_const P
  have hQ : Tendsto (fun t => b t • Q) atBot (𝓝 ((1 : ℝ) • Q)) :=
    hb.smul_const Q
  simpa using hP.add hQ

theorem normalizedTwoLaneFlow_tendsto_atTop (P Q : E) :
    Tendsto (normalizedTwoLaneFlow P Q) atTop (𝓝 P) := by
  exact tendsto_two_lane_smul_add
    Cl55SplitRoutingWeights.normalizedPlus_tendsto_atTop
    Cl55SplitRoutingWeights.normalizedMinus_tendsto_atTop

theorem normalizedTwoLaneFlow_tendsto_atBot (P Q : E) :
    Tendsto (normalizedTwoLaneFlow P Q) atBot (𝓝 Q) := by
  have hP : Tendsto Cl55SplitRoutingWeights.normalizedPlus atBot (𝓝 (0 : ℝ)) :=
    Cl55SplitRoutingWeights.normalizedPlus_tendsto_atBot
  have hQ : Tendsto Cl55SplitRoutingWeights.normalizedMinus atBot (𝓝 (1 : ℝ)) :=
    Cl55SplitRoutingWeights.normalizedMinus_tendsto_atBot
  exact tendsto_two_lane_smul_add_atBot hP hQ

end InfoGeometry.Clifford.SplitFlowOperatorLimit
