/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornVectorMatrix

namespace InfoGeometry.Lie.FirstQuantizedSplitOctonions

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornVectorMatrix

variable {R : Type*} [CommRing R]

abbrev Carrier (R : Type*) [CommRing R] := ZornVectorMatrix R

/-- Left regular multiplication action on the one-particle state space $\\mathcal{H}_1$: $L_x(z) = x * z$. -/
def leftMul (x z : Carrier R) : Carrier R :=
  ZornVectorMatrix.mul x z

/-- Associator defect operator $\\mathcal{A}_{x,y}(z) = x * (y * z) - (x * y) * z$. -/
def associatorDefect (x y z : Carrier R) : Carrier R :=
  ZornVectorMatrix.sub (leftMul x (leftMul y z)) (leftMul (ZornVectorMatrix.mul x y) z)

/-- The positive chiral projector $\\Pi_+(z) = L_{u_+}(z)$. -/
def projPlus (z : Carrier R) : Carrier R :=
  leftMul E11 z

/-- The negative chiral projector $\\Pi_-(z) = L_{u_-}(z)$. -/
def projMinus (z : Carrier R) : Carrier R :=
  leftMul E22 z

/-- Positive chiral ladder operator $Q_+^a = L_{\\sigma_+^a}$. -/
def ladderPlus (i : Fin 3) (z : Carrier R) : Carrier R :=
  leftMul (U i) z

/-- Negative chiral ladder operator $Q_-^a = L_{\\sigma_-^a}$. -/
def ladderMinus (i : Fin 3) (z : Carrier R) : Carrier R :=
  leftMul (V i) z

/-- 🏆 THEOREM 1: Exact composition law with associator defect: $L_x(L_y(z)) = L_{xy}(z) + \\mathcal{A}_{x,y}(z)$. -/
theorem leftMul_comp_defect (x y z : Carrier R) :
    leftMul x (leftMul y z) = ZornVectorMatrix.add (leftMul (ZornVectorMatrix.mul x y) z) (associatorDefect x y z) := by
  dsimp [leftMul, associatorDefect]
  ext i
  · simp [ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg]
  · fin_cases i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg]
  · fin_cases i <;> simp [ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg]
  · simp [ZornVectorMatrix.add, ZornVectorMatrix.sub, ZornVectorMatrix.neg]

/-- 🏆 THEOREM 2: Upper chiral ladders square to their associator defect: $(Q_+^a)^2(z) = \\mathcal{A}_{\\sigma_+^a, \\sigma_+^a}(z)$. -/
theorem ladderPlus_sq (i : Fin 3) (z : Carrier R) :
    ladderPlus i (ladderPlus i z) =
      ZornVectorMatrix.add (leftMul ZornVectorMatrix.zero z) (associatorDefect (U i) (U i) z) := by
  have h_comp := leftMul_comp_defect (U i) (U i) z
  rw [U_mul_self_zero i] at h_comp
  exact h_comp

/-- 🏆 THEOREM 3: Lower chiral ladders square to their associator defect: $(Q_-^a)^2(z) = \\mathcal{A}_{\\sigma_-^a, \\sigma_-^a}(z)$. -/
theorem ladderMinus_sq (i : Fin 3) (z : Carrier R) :
    ladderMinus i (ladderMinus i z) =
      ZornVectorMatrix.add (leftMul ZornVectorMatrix.zero z) (associatorDefect (V i) (V i) z) := by
  have h_comp := leftMul_comp_defect (V i) (V i) z
  rw [V_mul_self_zero i] at h_comp
  exact h_comp

/-- 🏆 THEOREM 4: Positive chiral projector idempotency modulo associator defect. -/
theorem projPlus_sq (z : Carrier R) :
    projPlus (projPlus z) =
      ZornVectorMatrix.add (projPlus z) (associatorDefect E11 E11 z) := by
  have h_comp := leftMul_comp_defect E11 E11 z
  rw [E11_mul_E11] at h_comp
  exact h_comp

/-- 🏆 THEOREM 5: Negative chiral projector idempotency modulo associator defect. -/
theorem projMinus_sq (z : Carrier R) :
    projMinus (projMinus z) =
      ZornVectorMatrix.add (projMinus z) (associatorDefect E22 E22 z) := by
  have h_comp := leftMul_comp_defect E22 E22 z
  rw [E22_mul_E22] at h_comp
  exact h_comp

/-- 🏆 THEOREM 6: Exact associator-corrected Canonical Anticommutation Relation (CAR):
    $\\{Q_+^a, Q_-^a\\}(z) = L_1(z) + \\mathcal{A}_{\\sigma_+^a, \\sigma_-^a}(z) + \\mathcal{A}_{\\sigma_-^a, \\sigma_+^a}(z)$. -/
theorem ladder_car_associator_corrected (i : Fin 3) (z : Carrier R) :
    ZornVectorMatrix.add (ladderPlus i (ladderMinus i z)) (ladderMinus i (ladderPlus i z)) =
      ZornVectorMatrix.add (leftMul ZornVectorMatrix.one z)
        (ZornVectorMatrix.add (associatorDefect (U i) (V i) z) (associatorDefect (V i) (U i) z)) := by
  have h_comp1 := leftMul_comp_defect (U i) (V i) z
  have h_comp2 := leftMul_comp_defect (V i) (U i) z
  rw [U_mul_V_self i] at h_comp1
  rw [V_mul_U_self i] at h_comp2
  dsimp [ladderPlus, ladderMinus]
  rw [h_comp1, h_comp2]
  have h_sum : ZornVectorMatrix.add (leftMul E11 z) (leftMul E22 z) = leftMul ZornVectorMatrix.one z := by
    dsimp [leftMul]
    ext k
    · simp [ZornVectorMatrix.add, ZornVectorMatrix.mul, E11, E22, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
    · fin_cases k <;>
        simp [ZornVectorMatrix.add, ZornVectorMatrix.mul, E11, E22, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
    · fin_cases k <;>
        simp [ZornVectorMatrix.add, ZornVectorMatrix.mul, E11, E22, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
    · simp [ZornVectorMatrix.add, ZornVectorMatrix.mul, E11, E22, ZornVectorMatrix.one, ZornVec3.dot, ZornVec3.cross]
  ext k
  · have h_a := congr_arg ZornVectorMatrix.a h_sum
    simp [ZornVectorMatrix.add] at h_a ⊢
    rw [← h_a]
    ring
  · fin_cases k
    · have h_v0 := congr_fun (congr_arg ZornVectorMatrix.v h_sum) 0
      simp [ZornVectorMatrix.add] at h_v0 ⊢
      rw [← h_v0]
      ring
    · have h_v1 := congr_fun (congr_arg ZornVectorMatrix.v h_sum) 1
      simp [ZornVectorMatrix.add] at h_v1 ⊢
      rw [← h_v1]
      ring
    · have h_v2 := congr_fun (congr_arg ZornVectorMatrix.v h_sum) 2
      simp [ZornVectorMatrix.add] at h_v2 ⊢
      rw [← h_v2]
      ring
  · fin_cases k
    · have h_w0 := congr_fun (congr_arg ZornVectorMatrix.w h_sum) 0
      simp [ZornVectorMatrix.add] at h_w0 ⊢
      rw [← h_w0]
      ring
    · have h_w1 := congr_fun (congr_arg ZornVectorMatrix.w h_sum) 1
      simp [ZornVectorMatrix.add] at h_w1 ⊢
      rw [← h_w1]
      ring
    · have h_w2 := congr_fun (congr_arg ZornVectorMatrix.w h_sum) 2
      simp [ZornVectorMatrix.add] at h_w2 ⊢
      rw [← h_w2]
      ring
  · have h_b := congr_arg ZornVectorMatrix.b h_sum
    simp [ZornVectorMatrix.add] at h_b ⊢
    rw [← h_b]
    ring

end InfoGeometry.Lie.FirstQuantizedSplitOctonions
