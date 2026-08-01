import Mathlib

noncomputable section

namespace InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge

/-- **Definition**: Cross-Ratio of 4 Points (z, z1, z2, z3) in ℝ or ℂ.
    (z - z1)(z2 - z3) / ((z - z3)(z2 - z1)).
    Uniquely maps z1 ↦ 0, z2 ↦ 1, z3 ↦ ∞. -/
def crossRatio (z z1 z2 z3 : ℝ) : ℝ :=
  ((z - z1) * (z2 - z3)) / ((z - z3) * (z2 - z1))

/-- **Theorem**: Evaluation at z = z1 yields 0.
    crossRatio(z1, z1, z2, z3) = 0. -/
theorem crossRatio_eval_z1 (z1 z2 z3 : ℝ) :
    crossRatio z1 z1 z2 z3 = 0 := by
  dsimp [crossRatio]
  rw [sub_self, zero_mul, zero_div]


end InfoGeometry.Canonical.ThreePointMoebiusCrossRatioBridge
