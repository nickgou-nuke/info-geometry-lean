/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Multiplicative transport of the stagewise involution readout

The tensor-tower owner defines `stageStarMap` as an additive map into the
algebraic direct limit and proves its compatibility with every bonding map.
This closure supplies the missing anti-multiplicative law on the existing
carrier, using the native limit multiplication and star instances.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTowerLimit

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

/-- The stagewise involution readout reverses products after passage to the
algebraic direct limit. -/
theorem stageStarMap_mul (n : ℕ) (A B : Stage n) :
    stageStarMap n (A * B) = stageStarMap n B * stageStarMap n A := by
  change ofStage n (star (A * B)) = ofStage n (star B) * ofStage n (star A)
  rw [star_mul, ofStage_mul]

/-- The preceding anti-multiplicativity is stable under any later-stage
representative of the same finite product. -/
theorem stageStarMap_compat_mul
    (i j : ℕ) (h : i ≤ j) (A B : Stage i) :
    stageStarMap j (bondMap stageBond i j h (A * B)) =
      stageStarMap i B * stageStarMap i A := by
  rw [stageStarMap_compat i j h (A * B)]
  exact stageStarMap_mul i A B

end InfoGeometry.Clifford.Cl11TensorTowerLimit
