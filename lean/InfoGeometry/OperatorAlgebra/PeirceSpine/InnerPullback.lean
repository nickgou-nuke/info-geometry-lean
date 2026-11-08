/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Core.IdempotentGraphGrassmannian

/-!
# Inner-derivation pullback and the idempotent equation

Contract: in an arbitrary ring, use a genuine unit g and the ordinary inner
derivation [P,-]. The pullback is a difference of conjugate idempotents.
Its quadratic equation is {P,w}+w²=w, not ordinary differential flatness.
Dependency order: inverse identities → conjugation formula → defect covariance
→ quadratic equation. The final corner identities specialize the raw words
from the intake without introducing a second vocabulary of group elements.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

def innerPullback (P : B) (g : Bˣ) : B :=
  (↑g⁻¹ : B) * comm P (↑g : B)

theorem innerPullback_eq_conjugate_sub (P : B) (g : Bˣ) :
    innerPullback P g = (↑g⁻¹ : B) * P * (↑g : B) - P := by
  simp [innerPullback, comm, mul_sub, ← mul_assoc]

theorem add_innerPullback (P : B) (g : Bˣ) :
    P + innerPullback P g = (↑g⁻¹ : B) * P * (↑g : B) := by
  rw [innerPullback_eq_conjugate_sub]
  abel

theorem innerPullback_quadratic {P : B} (hP : P * P = P) (g : Bˣ) :
    anticomm P (innerPullback P g) + innerPullback P g * innerPullback P g =
      innerPullback P g := by
  have hz : idempotencyDefect (P + innerPullback P g) = 0 := by
    rw [add_innerPullback, idempotencyDefect_conj]
    · simp [idempotencyDefect, hP]
    · simp
  have he : idempotencyDefect (P + innerPullback P g) =
      anticomm P (innerPullback P g) + innerPullback P g * innerPullback P g -
        innerPullback P g := by
    simp only [idempotencyDefect, anticomm, add_mul, mul_add, hP]
    abel
  exact sub_eq_zero.mp (he.symm.trans hz)

/-- Exact residual for the proposed ordinary Maurer--Cartan equation. -/
theorem innerPullback_comm_residual {P : B} (hP : P * P = P) (g : Bˣ) :
    comm P (innerPullback P g) + innerPullback P g * innerPullback P g =
      innerPullback P g - (2 : ℤ) • (innerPullback P g * P) := by
  have h := innerPullback_quadratic hP g
  unfold comm anticomm at *
  rw [two_zsmul]
  calc
    _ = (P * innerPullback P g + innerPullback P g * P +
        innerPullback P g * innerPullback P g) -
        (innerPullback P g * P + innerPullback P g * P) := by abel
    _ = _ := by rw [h]

theorem innerPullback_flat_iff {P : B} (hP : P * P = P) (g : Bˣ) :
    comm P (innerPullback P g) + innerPullback P g * innerPullback P g = 0 ↔
      innerPullback P g = (2 : ℤ) • (innerPullback P g * P) := by
  rw [innerPullback_comm_residual hP, sub_eq_zero]

variable {P : B} (hP : P * P = P) (A C : B)
include hP

theorem comm_two_cone_product :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) = genPhi P A C := by
  peirce_nf hP

theorem two_cone_left_pullback :
    ((1 + coneMinus P C) * (1 - conePlus P A)) *
      comm P ((1 + conePlus P A) * (1 - coneMinus P C)) =
      genPhi P A C - genSig P A C - genV P A C * coneMinus P C := by
  peirce_nf hP

theorem two_cone_right_pullback :
    comm P ((1 + conePlus P A) * (1 - coneMinus P C)) *
      ((1 + coneMinus P C) * (1 - conePlus P A)) =
      genPhi P A C + genSig P A C - genV P A C * conePlus P A := by
  peirce_nf hP

end InfoGeometry.OperatorAlgebra.PeirceSpine
