/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
import InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

/-!
# Fixed-head compatibility of the split Clifford tower

This bridge combines the finite head--tail Clifford factorization with the
existing canonical direct-limit stage transition. Its generator theorem records
how one recursive tower step is represented in the fixed head and enlarged
tail coordinates.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitCliffordHeadTailTower

open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordFiniteHeadTail
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- After fixed-head factorization, the actual split-tower transition sends
each Clifford generator to its unchanged head component and its one-coordinate
tail inclusion. -/
theorem splitCliffordHeadTail_transition_generator (k n : ℕ)
    (x : SplitSpace (k + n)) :
    splitCliffordFiniteHeadTailEquiv k (n + 1)
        (splitCliffordStep (k + n)
          (CliffordAlgebra.ι (Qsplit (k + n)) x)) =
      (CliffordAlgebra.ι (Qsplit k)
        (splitSpaceAppendEquiv k n x).1)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit (n + 1))) +
        (1 : CliffordAlgebra (Qsplit k)) ᵍ⊗ₜ
          CliffordAlgebra.ι (Qsplit (n + 1))
            (0, (splitSpaceAppendEquiv k n x).2) := by
  rw [InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation.splitCliffordStep_eq_splitStageCliffordMap]
  rw [InfoGeometry.Clifford.ClNNSuperGrassmannianBridge.splitStageCliffordMap_generator_eq_gammaTail]
  rw [gammaTail]
  have htail : tailLift (k + n) x = (0, x) := by
    simp [tailLift]
  rw [htail]
  exact splitCliffordFiniteHeadTailEquiv_inr k n x

end InfoGeometry.Canonical.SplitCliffordHeadTailTower

end
