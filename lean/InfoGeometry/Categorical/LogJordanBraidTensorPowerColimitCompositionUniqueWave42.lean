/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.LogJordanBraidTensorPowerColimitCompositionWave41

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

open CategoryTheory
open CategoryTheory.Limits

/-- The colimit endomorphism obtained by composing two compatible stage
endomorphisms is the unique colimit morphism with the corresponding composed
stage readbacks. -/
theorem colimitEndomorphism_comp_unique
    (A B : CompatibleStageEndomorphism)
    (f : StandardTensorPowerColimit ⟶ StandardTensorPowerColimit)
    (hf : ∀ n : ℕ,
      stageInclusion n ≫ f = (A.map n ≫ B.map n) ≫ stageInclusion n) :
    f = colimitEndomorphism A ≫ colimitEndomorphism B := by
  apply colimit.hom_ext
  intro n
  calc
    stageInclusion n ≫ f =
        (A.map n ≫ B.map n) ≫ stageInclusion n := hf n
    _ = stageInclusion n ≫ colimitEndomorphism A ≫ colimitEndomorphism B :=
      (colimitEndomorphism_comp_stage A B n).symm

end InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
