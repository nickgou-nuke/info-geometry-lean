/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTower

set_option autoImplicit false
noncomputable section

namespace InfoGeometry.Clifford.Cl11TensorTower

open scoped Matrix Kronecker

/-- The global chirality at the successor stage factors into the embedded
previous chirality and the local chiral generator. -/
theorem globalChirality_succ_factorization (n : ℕ) :
    (globalChirality n ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℝ)) *
        ((1 : MatStage n) ⊗ₖ gamma_chiral_base) =
      globalChirality (Nat.succ n) := by
  rw [← Matrix.mul_kronecker_mul]
  simp [globalChirality, InfoGeometry.Clifford.TowerMatrix.kronPow]

end InfoGeometry.Clifford.Cl11TensorTower
