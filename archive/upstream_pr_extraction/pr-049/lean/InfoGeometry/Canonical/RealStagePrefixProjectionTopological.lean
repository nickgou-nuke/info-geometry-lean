import InfoGeometry.Canonical.RealStagePrefixProjection
import InfoGeometry.Canonical.RealUHFProjectionRankTailTopological

namespace InfoGeometry.Canonical

open InfoGeometry.Canonical.RealUHFProjectionRankRealCompletionTopological
open RealUHFProjectionRankTailSystem

/-!
# Real topological readout of arbitrary finite-rank prefix seeds
-/

theorem prefixTailSystem_realReadout_value
    (n r : ℕ) (hr : r ≤ 2 ^ n) (k : ℕ) :
    ((prefixTailSystem n r hr).realReadout k : ℝ) =
      (((r : ℚ) / (2 : ℚ) ^ n : ℚ) : ℝ) := by
  unfold RealUHFProjectionRankTailSystem.realReadout
  change (((prefixTailSystem n r hr).normalizedReadout k : ℚ) : ℝ) = _
  rw [prefixTailSystem_readout_value n r hr k]

end InfoGeometry.Canonical
