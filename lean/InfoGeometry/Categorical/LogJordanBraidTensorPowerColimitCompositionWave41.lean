/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

open CategoryTheory
open CategoryTheory.Limits

/-- Sequential colimit transport preserves the composition of compatible
stage endomorphisms at every canonical stage.  This is the concrete
stage-readback law needed to compare finite braid operators after passage to
the existing module colimit.
-/
theorem colimitEndomorphism_comp_stage
    (A B : CompatibleStageEndomorphism) (n : ℕ) :
    stageInclusion n ≫ colimitEndomorphism A ≫ colimitEndomorphism B =
      (A.map n ≫ B.map n) ≫ stageInclusion n := by
  calc
    stageInclusion n ≫ colimitEndomorphism A ≫ colimitEndomorphism B =
        (A.map n ≫ stageInclusion n) ≫ colimitEndomorphism B := by
      rw [← Category.assoc, colimitEndomorphism_stage A]
    _ = A.map n ≫ (stageInclusion n ≫ colimitEndomorphism B) := by
      rw [Category.assoc]
    _ = (A.map n ≫ B.map n) ≫ stageInclusion n := by
      rw [colimitEndomorphism_stage B]
      simp only [Category.assoc]

end InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
