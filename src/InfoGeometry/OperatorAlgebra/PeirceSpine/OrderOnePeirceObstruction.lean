/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.CayleyDicksonHopfPoset
import Mathlib.Tactic.NoncommRing

/-!
# Peirce corner order-zero and order-one identities

This file isolates associative-ring consequences of the order-one archetype. With
`comm x y = x*y - y*x`, the mixed-corner formula has a negative sign.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Causal stages for the algebraic order-zero/order-one spine. -/
inductive OrderOneStage : Type
  | peirceCut
  | cornerOrderZero
  | mixedCornerObstruction
  | jacobiSymmetry
  | rightCommutantCriterion
  | sectorApplications
  deriving DecidableEq, Repr

namespace OrderOneStage

def rank : OrderOneStage → ℕ
  | peirceCut => 0
  | cornerOrderZero => 1
  | mixedCornerObstruction => 2
  | jacobiSymmetry => 3
  | rightCommutantCriterion => 4
  | sectorApplications => 5

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp [rank] at h ⊢


def causalEdge : OrderOneStage → OrderOneStage → Prop
  | peirceCut, cornerOrderZero => True
  | peirceCut, mixedCornerObstruction => True
  | cornerOrderZero, jacobiSymmetry => True
  | jacobiSymmetry, rightCommutantCriterion => True
  | rightCommutantCriterion, sectorApplications => True
  | mixedCornerObstruction, sectorApplications => True
  | _, _ => False

theorem causalEdge_rank_strict {a b : OrderOneStage} (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

end OrderOneStage

variable {B : Type*} [Ring B]

/-- Two-sector off-diagonal operator used for the algebraic charge action. -/
def electroweakDirac (P₁ P₂ H₁ H₂ : B) : B :=
  P₁ * H₁ * P₂ + P₂ * H₂ * P₁

/-- Equal sector weights make the pre-breaking charge commute with both
orientations of the two-sector transition. This reuses the proved charge action
on each Peirce corner. -/
theorem hypercharge_commutes_electroweak_operator
    {P₀ P₁ P₂ P₃ H₁ H₂ : B}
    (h11 : P₁ * P₁ = P₁) (h22 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (h01 : P₀ * P₁ = 0) (h10 : P₁ * P₀ = 0)
    (h02 : P₀ * P₂ = 0) (h20 : P₂ * P₀ = 0)
    (h31 : P₃ * P₁ = 0) (h13 : P₁ * P₃ = 0)
    (h32 : P₃ * P₂ = 0) (h23 : P₂ * P₃ = 0) :
    comm (chargeY6 P₀ P₁ P₂ P₃) (electroweakDirac P₁ P₂ H₁ H₂) = 0 := by
  have hf := quaternionic_symmetry_breaking_and_charge_operators
    h11 h22 h12 h21 h01 h20 h31 h23 H₁
  have hb := quaternionic_symmetry_breaking_and_charge_operators
    h22 h11 h21 h12 h02 h10 h32 h13 H₂
  have hCharge : chargeY6 P₀ P₂ P₁ P₃ = chargeY6 P₀ P₁ P₂ P₃ := by
    unfold chargeY6
    abel
  have hForward := hf.2.2.1
  have hBackward := hb.2.2.1
  rw [hCharge] at hBackward
  change comm (chargeY6 P₀ P₁ P₂ P₃)
      (P₁ * H₁ * P₂ + P₂ * H₂ * P₁) = 0
  calc
    comm (chargeY6 P₀ P₁ P₂ P₃) (P₁ * H₁ * P₂ + P₂ * H₂ * P₁) =
        comm (chargeY6 P₀ P₁ P₂ P₃) (P₁ * H₁ * P₂) +
          comm (chargeY6 P₀ P₁ P₂ P₃) (P₂ * H₂ * P₁) := by
      unfold comm
      noncomm_ring
    _ = 0 := by rw [hForward, hBackward]; simp

/-- Diagonal Peirce corners commute because their products vanish. -/
theorem peirce_diagonal_corners_commute {P X Y : B} (hP : P * P = P) :
    comm (P * X * P) ((1 - P) * Y * (1 - P)) = 0 := by
  have hPcomp : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hcompP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hxy : (P * X * P) * ((1 - P) * Y * (1 - P)) = 0 := by
    calc
      _ = (P * X) * (P * (1 - P)) * (Y * (1 - P)) := by noncomm_ring
      _ = 0 := by rw [hPcomp]; simp
  have hyx : ((1 - P) * Y * (1 - P)) * (P * X * P) = 0 := by
    calc
      _ = ((1 - P) * Y) * ((1 - P) * P) * (X * P) := by noncomm_ring
      _ = 0 := by rw [hcompP]; simp
  unfold comm
  rw [hxy, hyx]
  simp

/-- For commuting observables, the order-one double commutator is symmetric. -/
theorem order_one_commuting_swap {D a b : B}
    (hab : comm a b = 0) :
    comm (comm D a) b = comm (comm D b) a := by
  have hab' : a * b = b * a := sub_eq_zero.mp hab
  have hfirst : D * (a * b) = D * (b * a) := by rw [hab']
  have hlast : b * (a * D) = a * (b * D) := by
    calc
      b * (a * D) = (b * a) * D := by rw [mul_assoc]
      _ = (a * b) * D := by rw [hab']
      _ = a * (b * D) := by rw [mul_assoc]
  unfold comm
  noncomm_ring [hfirst, hlast]

/-- Abstract mixed-corner expansion. The four hypotheses state the annihilations
that remove the other terms in the expanded double commutator. -/
theorem mixed_corner_order_one_formula {a b u v : B}
    (hUa : u * a = 0) (hAv : a * v = 0)
    (hVab : v * a * b = 0) (hBaU : b * a * u = 0) :
    comm (comm (u + v) a) b = -(a * u * b + b * v * a) := by
  have hBaU' : b * (a * u) = 0 := by rw [← mul_assoc, hBaU]
  unfold comm
  noncomm_ring [hUa, hAv, hVab, hBaU']

/-- The exact order-one bracket for the two opposite Peirce transitions and
opposite diagonal corners. Its sign follows from `comm x y = x*y - y*x`. -/
theorem peirce_two_wave_order_one_obstruction
    {P A C X Y : B} (hP : P * P = P) :
    comm (comm (conePlus P A + coneMinus P C) (P * X * P))
        ((1 - P) * Y * (1 - P)) =
      -((P * X * P) * conePlus P A * ((1 - P) * Y * (1 - P)) +
        ((1 - P) * Y * (1 - P)) * coneMinus P C * (P * X * P)) := by
  let u := conePlus P A
  let v := coneMinus P C
  let a := P * X * P
  let b := (1 - P) * Y * (1 - P)
  have hPcomp : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hcompP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hab : a * b = 0 := by
    dsimp [a, b]
    calc
      _ = (P * X) * (P * (1 - P)) * (Y * (1 - P)) := by noncomm_ring
      _ = 0 := by rw [hPcomp]; simp
  have hba : b * a = 0 := by
    dsimp [a, b]
    calc
      _ = ((1 - P) * Y) * ((1 - P) * P) * (X * P) := by noncomm_ring
      _ = 0 := by rw [hcompP]; simp
  have hua : u * a = 0 := by
    dsimp [u, a]
    simpa [mul_assoc] using conePlus_mul_P' hP A (X * P)
  have hav : a * v = 0 := by
    dsimp [a, v]
    calc
      P * X * P * coneMinus P C = P * X * (P * coneMinus P C) := by noncomm_ring
      _ = 0 := by rw [P_mul_coneMinus hP]; simp
  have hvab : v * a * b = 0 := by
    calc
      v * a * b = v * (a * b) := by simp only [mul_assoc]
      _ = 0 := by rw [hab]; simp
  have hbau : b * a * u = 0 := by rw [hba]; simp
  change comm (comm (u + v) a) b = -(a * u * b + b * v * a)
  exact mixed_corner_order_one_formula hua hav hvab hbau

/-- The Peirce order-one bracket vanishes exactly when the sum of its two
surviving corner sandwiches vanishes.  No claim is made that the two terms
vanish separately: cancellation between them is possible in a general ring. -/
theorem peirce_two_wave_order_one_vanish_iff
    {P A C X Y : B} (hP : P * P = P) :
    comm (comm (conePlus P A + coneMinus P C) (P * X * P))
        ((1 - P) * Y * (1 - P)) = 0 ↔
      (P * X * P) * conePlus P A * ((1 - P) * Y * (1 - P)) +
        ((1 - P) * Y * (1 - P)) * coneMinus P C * (P * X * P) = 0 := by
  rw [peirce_two_wave_order_one_obstruction hP]
  exact neg_eq_zero

/-- If the two observables commute and the right one commutes with `D`, the
order-one bracket vanishes. -/
theorem order_one_vanish_of_right_commutes {D a b : B}
    (hab : comm a b = 0) (hDb : comm D b = 0) :
    comm (comm D a) b = 0 := by
  rw [order_one_commuting_swap hab, hDb]
  simp [comm]

/-- Compact synthesis of the verified order-zero and order-one algebraic core. -/
theorem order_one_causal_synthesis {P X Y D a b A C : B}
    (hP : P * P = P) (hZero : comm a b = 0) (hDb : comm D b = 0) :
    comm (P * X * P) ((1 - P) * Y * (1 - P)) = 0 ∧
    comm (comm (conePlus P A + coneMinus P C) (P * X * P))
        ((1 - P) * Y * (1 - P)) =
      -((P * X * P) * conePlus P A * ((1 - P) * Y * (1 - P)) +
        ((1 - P) * Y * (1 - P)) * coneMinus P C * (P * X * P)) ∧
    comm (comm D a) b = comm (comm D b) a ∧
    comm (comm D a) b = 0 := by
  exact ⟨peirce_diagonal_corners_commute hP,
    peirce_two_wave_order_one_obstruction hP,
    order_one_commuting_swap hZero,
    order_one_vanish_of_right_commutes hZero hDb⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
