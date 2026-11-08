/-
InfoGeometry/Canonical/DrazinCliffordMatrixUnitBridge.lean

Drazin light-cone / split-Clifford matrix-unit bridge.

`DrazinLightConeDictionary` owns the universal Peirce skeleton:

  u⁺(X) = P X P₀,   u⁻(X) = P₀ X P.

This file adds the extra matrix-unit witnesses needed to read that skeleton as
the local split Clifford cell `Cl(1,1) ≃ M₂(ℝ)`.  The stronger mixed-product
laws are not universal for arbitrary projected channels; they are explicit
fields of the matrix-unit datum.
-/

import InfoGeometry.Canonical.DrazinLightConeDictionary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture
import Mathlib.Tactic

namespace InfoGeometry.Canonical.DrazinCliffordMatrixUnitBridge

open InfoGeometry.Canonical.DrazinLightConeDictionary

/--
A Drazin projector split upgraded to a matrix-unit light-cone cell.

The fields `uPlus` and `uMinus` are chosen arrows between the `P₀` and `P`
sectors.  The support laws say they are the `(P,P₀)` and `(P₀,P)` Peirce
blocks.  The mixed-product laws say they are actual matrix units, not just
arbitrary off-diagonal channels.
-/
@[rep_depth operator]
structure DrazinCliffordMatrixUnitCell (A : Type*) [Ring A] extends ProjectorSplit A where
  uPlus : A
  uMinus : A

  P_mul_uPlus : P * uPlus = uPlus
  uPlus_mul_P0 : uPlus * P0 = uPlus
  uPlus_mul_P : uPlus * P = 0
  P0_mul_uPlus : P0 * uPlus = 0

  P0_mul_uMinus : P0 * uMinus = uMinus
  uMinus_mul_P : uMinus * P = uMinus
  uMinus_mul_P0 : uMinus * P0 = 0
  P_mul_uMinus : P * uMinus = 0

  uPlus_sq : uPlus * uPlus = 0
  uMinus_sq : uMinus * uMinus = 0
  uPlus_mul_uMinus : uPlus * uMinus = P
  uMinus_mul_uPlus : uMinus * uPlus = P0

namespace DrazinCliffordMatrixUnitCell

variable {A : Type*} [Ring A]
variable (C : DrazinCliffordMatrixUnitCell A)

/-- Split Clifford grading `ε = P - P₀`. -/
@[rep_depth operator]
def eps : A :=
  C.P - C.P0

/-- Split Clifford reflection `J = u⁺ + u⁻`. -/
@[rep_depth operator]
def J : A :=
  C.uPlus + C.uMinus

/-- Hestenes phase axis `K = Jε`. -/
@[rep_depth operator]
def K : A :=
  C.J * C.eps

/-- The chosen `u⁺` is the universal Peirce arrow applied to itself. -/
@[rep_depth operator]
theorem split_uPlus_apply_uPlus :
    C.toProjectorSplit.uPlus C.uPlus = C.uPlus := by
  unfold ProjectorSplit.uPlus
  rw [C.P_mul_uPlus, C.uPlus_mul_P0]

/-- The chosen `u⁻` is the universal Peirce arrow applied to itself. -/
@[rep_depth operator]
theorem split_uMinus_apply_uMinus :
    C.toProjectorSplit.uMinus C.uMinus = C.uMinus := by
  unfold ProjectorSplit.uMinus
  rw [C.P0_mul_uMinus, C.uMinus_mul_P]

/-- The matrix-unit arrows satisfy the CAR-style mixed anticommutator law. -/
@[rep_depth operator]
theorem uPlus_uMinus_anticommutator_eq_one :
    C.uPlus * C.uMinus + C.uMinus * C.uPlus = 1 := by
  rw [C.uPlus_mul_uMinus, C.uMinus_mul_uPlus, C.P_add_P0]

/-- The split grading squares to `1`. -/
@[rep_depth operator]
theorem eps_sq :
    C.eps * C.eps = 1 := by
  unfold eps
  calc
    (C.P - C.P0) * (C.P - C.P0)
        = C.P * C.P - C.P * C.P0 - C.P0 * C.P + C.P0 * C.P0 := by
            noncomm_ring
    _ = C.P + C.P0 := by
            rw [C.P_idem, C.P_mul_P0, C.P0_mul_P, C.P0_idem]
            simp
    _ = 1 := C.P_add_P0

/-- The matrix-unit reflection squares to `1`. -/
@[rep_depth operator]
theorem J_sq :
    C.J * C.J = 1 := by
  unfold J
  calc
    (C.uPlus + C.uMinus) * (C.uPlus + C.uMinus)
        = C.uPlus * C.uPlus + C.uPlus * C.uMinus
          + C.uMinus * C.uPlus + C.uMinus * C.uMinus := by
            noncomm_ring
    _ = C.P + C.P0 := by
            rw [C.uPlus_sq, C.uPlus_mul_uMinus, C.uMinus_mul_uPlus, C.uMinus_sq]
            simp [add_assoc]
    _ = 1 := C.P_add_P0

/-- Right multiplication by the grading sends `J` to `u⁻ - u⁺`. -/
@[rep_depth operator]
theorem J_mul_eps_eq_uMinus_sub_uPlus :
    C.J * C.eps = C.uMinus - C.uPlus := by
  unfold J eps
  calc
    (C.uPlus + C.uMinus) * (C.P - C.P0)
        = C.uPlus * C.P - C.uPlus * C.P0
          + C.uMinus * C.P - C.uMinus * C.P0 := by
            noncomm_ring
    _ = C.uMinus - C.uPlus := by
            rw [C.uPlus_mul_P, C.uPlus_mul_P0, C.uMinus_mul_P, C.uMinus_mul_P0]
            abel

/-- Left multiplication by the grading sends `J` to `u⁺ - u⁻`. -/
@[rep_depth operator]
theorem eps_mul_J_eq_uPlus_sub_uMinus :
    C.eps * C.J = C.uPlus - C.uMinus := by
  unfold J eps
  calc
    (C.P - C.P0) * (C.uPlus + C.uMinus)
        = C.P * C.uPlus + C.P * C.uMinus
          - C.P0 * C.uPlus - C.P0 * C.uMinus := by
            noncomm_ring
    _ = C.uPlus - C.uMinus := by
            rw [C.P_mul_uPlus, C.P_mul_uMinus, C.P0_mul_uPlus, C.P0_mul_uMinus]
            abel

/-- The split Clifford generators anticommute. -/
@[rep_depth operator]
theorem J_eps_anticommute :
    C.J * C.eps = -(C.eps * C.J) := by
  rw [C.J_mul_eps_eq_uMinus_sub_uPlus, C.eps_mul_J_eq_uPlus_sub_uMinus]
  abel

/-- Equivalent zero-sum anticommutation form. -/
@[rep_depth operator]
theorem J_mul_eps_add_eps_mul_J_eq_zero :
    C.J * C.eps + C.eps * C.J = 0 := by
  rw [C.J_mul_eps_eq_uMinus_sub_uPlus, C.eps_mul_J_eq_uPlus_sub_uMinus]
  abel

/-- The Hestenes phase axis is `u⁻ - u⁺`. -/
@[rep_depth operator]
theorem K_eq_uMinus_sub_uPlus :
    C.K = C.uMinus - C.uPlus := by
  unfold K
  exact C.J_mul_eps_eq_uMinus_sub_uPlus

/-- The Hestenes phase axis squares to `-1`. -/
@[rep_depth operator]
theorem K_sq :
    C.K * C.K = -1 := by
  rw [C.K_eq_uMinus_sub_uPlus]
  calc
    (C.uMinus - C.uPlus) * (C.uMinus - C.uPlus)
        = C.uMinus * C.uMinus - C.uMinus * C.uPlus
          - C.uPlus * C.uMinus + C.uPlus * C.uPlus := by
            noncomm_ring
    _ = -(C.P + C.P0) := by
            rw [C.uMinus_sq, C.uMinus_mul_uPlus, C.uPlus_mul_uMinus, C.uPlus_sq]
            abel
    _ = -1 := by
            rw [C.P_add_P0]

/--
The matrix-unit Drazin cell realizes the local split Clifford packet
`J² = 1`, `ε² = 1`, `Jε = -εJ`, and `(Jε)² = -1`.
-/
@[rep_depth operator]
theorem split_clifford_relations :
    C.J * C.J = 1 ∧
      C.eps * C.eps = 1 ∧
      C.J * C.eps = -(C.eps * C.J) ∧
      C.K * C.K = -1 :=
  ⟨C.J_sq, C.eps_sq, C.J_eps_anticommute, C.K_sq⟩

end DrazinCliffordMatrixUnitCell

end InfoGeometry.Canonical.DrazinCliffordMatrixUnitBridge
