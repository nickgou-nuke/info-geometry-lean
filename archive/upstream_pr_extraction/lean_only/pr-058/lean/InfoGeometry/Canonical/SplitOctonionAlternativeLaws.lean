import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionRegularOperators

noncomputable section

namespace SplitOctonion

open scoped Quaternion

set_option maxHeartbeats 1000000 in
theorem left_alternative (x y : SplitOctonion) :
    (x * x) * y = x * (x * y) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply SplitOctonion.ext <;>
    ext <;>
    simp [mul_a, mul_b, Quaternion.normSq] <;>
    ring

set_option maxHeartbeats 1000000 in
theorem right_alternative (x y : SplitOctonion) :
    (y * x) * x = y * (x * x) := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply SplitOctonion.ext <;>
    ext <;>
    simp [mul_a, mul_b, Quaternion.normSq] <;>
    ring

end SplitOctonion
