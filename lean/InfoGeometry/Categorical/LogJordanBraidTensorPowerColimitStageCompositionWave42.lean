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

/-- Composition of two compatible stage endomorphisms is compatible with
 every bonding morphism of the tensor-power sequence. -/
theorem compatibleStageEndomorphism_composed_naturality
    (A B : CompatibleStageEndomorphism) {m n : ℕ} (h : m ≤ n) :
    standardTensorPowerModuleDiagram.map (homOfLE h) ≫
        (A.map n ≫ B.map n) =
      (A.map m ≫ B.map m) ≫
        standardTensorPowerModuleDiagram.map (homOfLE h) := by
  calc
    standardTensorPowerModuleDiagram.map (homOfLE h) ≫
          (A.map n ≫ B.map n) =
        (standardTensorPowerModuleDiagram.map (homOfLE h) ≫ A.map n) ≫
          B.map n := by rw [Category.assoc]
    _ = (A.map m ≫ standardTensorPowerModuleDiagram.map (homOfLE h)) ≫
          B.map n := by rw [A.naturality h]
    _ = A.map m ≫
          (standardTensorPowerModuleDiagram.map (homOfLE h) ≫ B.map n) := by
      rw [Category.assoc]
    _ = A.map m ≫
          (B.map m ≫ standardTensorPowerModuleDiagram.map (homOfLE h)) := by
      rw [B.naturality h]
    _ = (A.map m ≫ B.map m) ≫
          standardTensorPowerModuleDiagram.map (homOfLE h) := by
      rw [Category.assoc]

end InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
