/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity

/-! Nonzero same-polarity composition in the associative endomorphism
algebra of the actual split-Zorn carrier. -/

namespace InfoGeometry.Canonical.ZornRightRegularSamePolarityWitness

open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCircularSamePolarity
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionEllCrossChannel

theorem same_polarity_right_regular_composition_ne_zero :
    rightRegular (rootPlus 1) * rightRegular (rootPlus 0) ≠ 0 := by
  intro h
  have heval := congrArg (fun T : InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge.EndCZ => T uPlus) h
  have hroot : rootPlus 0 * rootPlus 1 = 0 := by
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, rightRegular_rootPlus_uPlus,
      rightRegular_apply, uPlus_mul_rootPlus] using heval
  exact rootPlus_zero_mul_rootPlus_one_ne_zero hroot

end InfoGeometry.Canonical.ZornRightRegularSamePolarityWitness
