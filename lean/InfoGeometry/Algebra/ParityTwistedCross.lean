/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Parity-twisted axial cross channel

This is the primitive three-direction channel used by a chiral/Zorn layer.
The parity scalar is explicit; quaternionic or matrix commutator readouts are
downstream representation adapters and are intentionally not part of this
owner.
-/

namespace InfoGeometry.Algebra.ZornVec3

variable {R : Type*} [Ring R]

/-- Multiplicative commutator `x * y - y * x` in any ring `[Ring R]`. -/
def opComm (x y : R) : R := x * y - y * x

def parityTwistedCross (χ : R) (u v : ZornVec3 R) : ZornVec3 R :=
  fun k => χ * cross u v k

def parityTwist (χ : R) (u : ZornVec3 R) : ZornVec3 R :=
  fun k => χ * u k

/-- Noncommutative coordinate commutator anomaly of `cross u v + cross v u`. -/
def crossSwapAnomaly (u v : ZornVec3 R) : ZornVec3 R := fun i =>
  if i = (0 : Fin 3) then opComm (u 1) (v 2) - opComm (u 2) (v 1)
  else if i = (1 : Fin 3) then opComm (u 2) (v 0) - opComm (u 0) (v 2)
  else opComm (u 0) (v 1) - opComm (u 1) (v 0)

/-- Noncommutative self-cross commutator vector `[u_i, u_j]`. -/
def crossSelfAnomaly (u : ZornVec3 R) : ZornVec3 R := fun i =>
  if i = (0 : Fin 3) then opComm (u 1) (u 2)
  else if i = (1 : Fin 3) then opComm (u 2) (u 0)
  else opComm (u 0) (u 1)

theorem parityTwistedCross_apply (χ : R) (u v : ZornVec3 R) (k : Fin 3) :
    parityTwistedCross χ u v k = χ * cross u v k := rfl

theorem parityTwistedCross_eq_smul (χ : R) (u v : ZornVec3 R) :
    parityTwistedCross χ u v = parityTwist χ (cross u v) := rfl

theorem parityTwistedCross_add_left (χ : R) (u v w : ZornVec3 R) :
    parityTwistedCross χ (fun k => u k + v k) w =
      (fun k => parityTwistedCross χ u w k + parityTwistedCross χ v w k) := by
  funext k
  fin_cases k <;> simp [parityTwistedCross, cross] <;> noncomm_ring

theorem parityTwistedCross_add_right (χ : R) (u v w : ZornVec3 R) :
    parityTwistedCross χ u (fun k => v k + w k) =
      (fun k => parityTwistedCross χ u v k + parityTwistedCross χ u w k) := by
  funext k
  fin_cases k <;> simp [parityTwistedCross, cross] <;> noncomm_ring

theorem parityTwistedCross_swap (χ : R) (u v : ZornVec3 R) :
    parityTwistedCross χ u v =
      (fun k => -(parityTwistedCross χ v u k) + χ * crossSwapAnomaly u v k) := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, cross, crossSwapAnomaly, opComm] <;>
    noncomm_ring

theorem parityTwistedCross_self (χ : R) (u : ZornVec3 R) :
    parityTwistedCross χ u u = (fun k => χ * crossSelfAnomaly u k) := by
  funext k
  fin_cases k <;>
    simp [parityTwistedCross, cross, crossSelfAnomaly, opComm]

theorem parityTwistedCross_basis (χ : R) (i j k : Fin 3) :
    parityTwistedCross χ (basis i) (basis j) k =
      χ * cross (basis i) (basis j) k := rfl

theorem parityTwistedCross_twist_involutive
    (χ : R) (hχ : χ * χ = 1) (u : ZornVec3 R) :
    parityTwist χ (parityTwist χ u) = u := by
  funext k
  calc
    parityTwist χ (parityTwist χ u) k = (χ * χ) * u k := by
      simp [parityTwist, mul_assoc]
    _ = 1 * u k := by rw [hχ]
    _ = u k := one_mul _

end InfoGeometry.Algebra.ZornVec3
