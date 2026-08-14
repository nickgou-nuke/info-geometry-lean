import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge

/-- Cross-ratio coordinate for four real points. -/
def crossRatio (z z1 z2 z3 : ℝ) : ℝ :=
  ((z - z1) * (z2 - z3)) / ((z - z3) * (z2 - z1))

/-- The cross-ratio vanishes at its first marked point. -/
theorem crossRatio_eval_z1 (z1 z2 z3 : ℝ) :
    crossRatio z1 z1 z2 z3 = 0 := by
  dsimp [crossRatio]
  rw [sub_self, zero_mul, zero_div]


end InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge
