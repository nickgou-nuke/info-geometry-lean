/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Omega.Conclusion.FoldZeroDivisorLatticeInvolution

namespace Omega.Conclusion

open Omega.Folding

/-- At `m = 0`, the owner definition has no zero modes, even though the
separately defined Bool flip is still a fixed-point-free involution. Thus the
global Bool fact alone does not witness or imply the existence of a zero mode. -/
theorem fold_zero_mode_flip_does_not_certify_nonempty_spectrum :
    foldFiberConvolutionKernelZeroSet (Nat.fib (0 + 2)) (Finset.range 0) = ∅ ∧
      Function.Involutive foldZeroModeCoordinateFlip ∧
      ∀ b : Bool, foldZeroModeCoordinateFlip b ≠ b := by
  refine ⟨?_, foldZeroModeCoordinateFlip_involutive, foldZeroModeCoordinateFlip_fixedpoint_free⟩
  change (Finset.range 0).biUnion (foldFiberSingletonZeroSet 1) = ∅
  rw [Finset.range_zero, Finset.biUnion_empty]

end Omega.Conclusion
