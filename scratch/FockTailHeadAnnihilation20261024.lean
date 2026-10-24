/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-!
# New-head contraction on the native algebraic Fock inclusion

Uncompiled sandbox. The existing zero-head inclusion has no occupation in the
new head mode. These are algebraic action identities, not Hilbert-space claims.
-/
noncomputable section

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

/-- Contraction by the new-head coordinate kills every embedded old spinor. -/
theorem contractLeft_head_fockTailMap (n : ℕ)
    (ψ : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Vector (n + 1))))
      (LinearMap.proj (0 : Fin (n + 1)) : Module.Dual ℝ (Vector (n + 1)))
      (fockTailMap n ψ) = 0 := by
  induction ψ using CliffordAlgebra.left_induction with
  | algebraMap r => simp [fockTailMap]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | ι_mul v x hx =>
      simp [map_mul, fockTailMap_generator, CliffordAlgebra.contractLeft_ι_mul,
        LinearMap.proj_apply, vectorHeadZero_coordinate_zero, hx]

/-- The new-head number action, creation after contraction, also annihilates
all old spinors under the native Fock inclusion. -/
theorem head_number_fockTailMap (n : ℕ)
    (ψ : InfoGeometry.Clifford.SpinorSpace (Vector n)) :
    CliffordAlgebra.ι (0 : QuadraticForm ℝ (Vector (n + 1)))
        (Pi.single (0 : Fin (n + 1)) (1 : ℝ)) *
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Vector (n + 1))))
        (LinearMap.proj (0 : Fin (n + 1)) : Module.Dual ℝ (Vector (n + 1)))
        (fockTailMap n ψ) = 0 := by
  rw [contractLeft_head_fockTailMap, mul_zero]

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
