/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Joint Witt/circular projectors

This is the operator-algebraic joint spectral layer for the two-sheet packet.
It uses two commuting involutions rather than assuming a commutative ambient
algebra: one involution represents the split/hyperbolic axis and the other the
circular/chiral axis.  The four joint projectors are products of the already
constructively derived half-projectors from `ChiralInvolution`.
-/

noncomputable section

namespace InfoGeometry.Optics.SheetWittCircularBasis

open InfoGeometry.OperatorAlgebra

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

def choose (ε : Bool) (p q : Op) : Op :=
  if ε = true then p else q

/-- Two commuting involutions in one operator algebra. -/
structure CommutingInvolutions (Op : Type*) [Ring Op] [Algebra ℝ Op] where
  hyperbolic : Op
  circular : Op
  hyperbolic_sq : hyperbolic * hyperbolic = 1
  circular_sq : circular * circular = 1
  commute : hyperbolic * circular = circular * hyperbolic
  projector_commute :
    ∀ ε σ, choose ε ((1 / 2 : ℝ) • (1 + hyperbolic))
      ((1 / 2 : ℝ) • (1 - hyperbolic)) *
      choose σ ((1 / 2 : ℝ) • (1 + circular))
      ((1 / 2 : ℝ) • (1 - circular)) =
    choose σ ((1 / 2 : ℝ) • (1 + circular))
      ((1 / 2 : ℝ) • (1 - circular)) *
      choose ε ((1 / 2 : ℝ) • (1 + hyperbolic))
      ((1 / 2 : ℝ) • (1 - hyperbolic))

namespace CommutingInvolutions

variable (S : CommutingInvolutions Op)

theorem choose_left_right_orthogonal (C : ChiralInvolution Op) :
    choose true C.Pleft C.Pright * choose false C.Pleft C.Pright = 0 := by
  simp [choose, C.Pleft_mul_Pright]

theorem choose_right_left_orthogonal (C : ChiralInvolution Op) :
    choose false C.Pleft C.Pright * choose true C.Pleft C.Pright = 0 := by
  simp [choose, C.Pright_mul_Pleft]

def hyperbolicInvolution (S : CommutingInvolutions Op) : ChiralInvolution Op where
  chi := S.hyperbolic
  chi_sq := S.hyperbolic_sq

def circularInvolution (S : CommutingInvolutions Op) : ChiralInvolution Op where
  chi := S.circular
  chi_sq := S.circular_sq

/-- Product of the selected hyperbolic and circular half-projectors. -/
def jointProjector (ε σ : Bool) : Op :=
  choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright *
    choose σ (circularInvolution S).Pleft (circularInvolution S).Pright

theorem hyperbolic_projector_commutes_circular_projector
    (ε σ : Bool) :
    choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright *
        choose σ (circularInvolution S).Pleft (circularInvolution S).Pright =
      choose σ (circularInvolution S).Pleft (circularInvolution S).Pright *
        choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright := by
  exact S.projector_commute ε σ

private theorem product_idem_of_commute
    {p q : Op} (hp : p * p = p) (hq : q * q = q)
    (hpq : p * q = q * p) : (p * q) * (p * q) = p * q := by
  calc
    (p * q) * (p * q) = p * (q * p) * q := by simp [mul_assoc]
    _ = p * (p * q) * q := by rw [hpq]
    _ = (p * p) * (q * q) := by simp [mul_assoc]
    _ = p * q := by rw [hp, hq]

private theorem product_zero_of_left_orthogonal
    {p p' q q' : Op} (hpp' : p * p' = 0)
    (hqp' : q * p' = p' * q) :
    (p * q) * (p' * q') = 0 := by
  calc
    (p * q) * (p' * q') = p * (q * p') * q' := by simp [mul_assoc]
    _ = p * (p' * q) * q' := by rw [hqp']
    _ = 0 := by rw [← mul_assoc p p' q, hpp']; simp

private theorem product_zero_of_right_orthogonal
    {p p' q q' : Op} (hqq' : q * q' = 0)
    (hp'q : p' * q = q * p') :
    (p * q) * (p' * q') = 0 := by
  calc
    (p * q) * (p' * q') = p * (q * p') * q' := by simp [mul_assoc]
    _ = p * (p' * q) * q' := by rw [hp'q]
    _ = (p * p') * (q * q') := by simp [mul_assoc]
    _ = 0 := by rw [hqq']; simp

theorem jointProjectors_hyperbolic_disjoint (σ σ' : Bool) :
    S.jointProjector true σ * S.jointProjector false σ' = 0 := by
  unfold jointProjector
  apply product_zero_of_left_orthogonal
  · exact (hyperbolicInvolution S).Pleft_mul_Pright
  · exact (hyperbolic_projector_commutes_circular_projector S false σ).symm

theorem jointProjectors_circular_disjoint (ε ε' : Bool) :
    S.jointProjector ε true * S.jointProjector ε' false = 0 := by
  unfold jointProjector
  apply product_zero_of_right_orthogonal
  · exact (circularInvolution S).Pleft_mul_Pright
  · exact hyperbolic_projector_commutes_circular_projector S ε' true

theorem jointProjectors_hyperbolic_disjoint_reverse (σ σ' : Bool) :
    S.jointProjector false σ * S.jointProjector true σ' = 0 := by
  unfold jointProjector
  apply product_zero_of_left_orthogonal
  · exact (hyperbolicInvolution S).Pright_mul_Pleft
  · exact (hyperbolic_projector_commutes_circular_projector S true σ).symm

theorem jointProjectors_circular_disjoint_reverse (ε ε' : Bool) :
    S.jointProjector ε false * S.jointProjector ε' true = 0 := by
  unfold jointProjector
  apply product_zero_of_right_orthogonal
  · exact (circularInvolution S).Pright_mul_Pleft
  · exact hyperbolic_projector_commutes_circular_projector S ε' false

theorem jointProjector_sum_circular (ε : Bool) :
    S.jointProjector ε true + S.jointProjector ε false =
      choose ε (hyperbolicInvolution S).Pleft (hyperbolicInvolution S).Pright := by
  unfold jointProjector
  cases ε <;> simp [choose]
  · rw [← mul_add, (circularInvolution S).Pleft_add_Pright, mul_one]
  · rw [← mul_add, (circularInvolution S).Pleft_add_Pright, mul_one]

theorem jointProjector_sum_hyperbolic (σ : Bool) :
    S.jointProjector true σ + S.jointProjector false σ =
      choose σ (circularInvolution S).Pleft (circularInvolution S).Pright := by
  unfold jointProjector
  cases σ <;> simp [choose]
  · rw [← add_mul, (hyperbolicInvolution S).Pleft_add_Pright, one_mul]
  · rw [← add_mul, (hyperbolicInvolution S).Pleft_add_Pright, one_mul]

theorem jointProjectors_pairwise_disjoint
    (ε σ ε' σ' : Bool)
    (h : ε ≠ ε' ∨ σ ≠ σ') :
    S.jointProjector ε σ * S.jointProjector ε' σ' = 0 := by
  rcases h with hε | hσ
  · cases ε with
    | false =>
        cases ε' with
        | false => exact False.elim (hε rfl)
        | true => exact jointProjectors_hyperbolic_disjoint_reverse S σ σ'
    | true =>
        cases ε' with
        | false => exact jointProjectors_hyperbolic_disjoint S σ σ'
        | true => exact False.elim (hε rfl)
  · cases σ with
    | false =>
        cases σ' with
        | false => exact False.elim (hσ rfl)
        | true => exact jointProjectors_circular_disjoint_reverse S ε ε'
    | true =>
        cases σ' with
        | false => exact jointProjectors_circular_disjoint S ε ε'
        | true => exact False.elim (hσ rfl)

@[simp] theorem jointProjector_idem (ε σ : Bool) :
    S.jointProjector ε σ * S.jointProjector ε σ = S.jointProjector ε σ := by
  unfold jointProjector
  apply product_idem_of_commute
  · cases ε <;> simp [choose, ChiralInvolution.Pleft_idem, ChiralInvolution.Pright_idem]
  · cases σ <;> simp [choose, ChiralInvolution.Pleft_idem, ChiralInvolution.Pright_idem]
  · exact hyperbolic_projector_commutes_circular_projector S ε σ

@[simp] theorem jointProjector_sum :
    S.jointProjector true true + S.jointProjector true false +
        S.jointProjector false true + S.jointProjector false false = 1 := by
  unfold jointProjector
  simp only [choose]
  calc
    (hyperbolicInvolution S).Pleft * (circularInvolution S).Pleft +
        (hyperbolicInvolution S).Pleft * (circularInvolution S).Pright +
        (hyperbolicInvolution S).Pright * (circularInvolution S).Pleft +
        (hyperbolicInvolution S).Pright * (circularInvolution S).Pright =
      ((hyperbolicInvolution S).Pleft + (hyperbolicInvolution S).Pright) *
        ((circularInvolution S).Pleft + (circularInvolution S).Pright) := by
          noncomm_ring
    _ = 1 := by rw [(hyperbolicInvolution S).Pleft_add_Pright,
      (circularInvolution S).Pleft_add_Pright]; simp

end CommutingInvolutions

end InfoGeometry.Optics.SheetWittCircularBasis

namespace InfoGeometry.Optics.SheetWittCircularBasis

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Commuting operators have commuting affine half-projectors; the ambient
algebra need not be commutative, and no involution equations are needed here. -/
theorem halfProjectors_commute_of_commute (h k : Op) (hc : h * k = k * h)
    (ε σ : Bool) :
    choose ε ((1 / 2 : ℝ) • (1 + h)) ((1 / 2 : ℝ) • (1 - h)) *
        choose σ ((1 / 2 : ℝ) • (1 + k)) ((1 / 2 : ℝ) • (1 - k)) =
      choose σ ((1 / 2 : ℝ) • (1 + k)) ((1 / 2 : ℝ) • (1 - k)) *
        choose ε ((1 / 2 : ℝ) • (1 + h)) ((1 / 2 : ℝ) • (1 - h)) := by
  have choose_true (p q : Op) : choose true p q = p := ite_eq_left rfl
  have choose_false (p q : Op) : choose false p q = q := ite_eq_right Bool.false_ne_true
  cases ε <;> cases σ <;> simp only [choose_true, choose_false] <;>
    rw [smul_mul_smul_comm, smul_mul_smul_comm] <;> congr 1 <;>
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hc] <;> abel

/-- Construct the existing joint-projector interface from two commuting
involutions, deriving its half-projector commutation field. -/
def CommutingInvolutions.ofCommute (h k : Op)
    (hh : h * h = 1) (hk : k * k = 1) (hc : h * k = k * h) :
    CommutingInvolutions Op where
  hyperbolic := h
  circular := k
  hyperbolic_sq := hh
  circular_sq := hk
  commute := hc
  projector_commute := halfProjectors_commute_of_commute h k hc

end InfoGeometry.Optics.SheetWittCircularBasis
