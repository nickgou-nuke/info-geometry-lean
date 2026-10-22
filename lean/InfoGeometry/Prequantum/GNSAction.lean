/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Prequantum.GNSBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# GNS Representation Action

This module defines the explicit operator representation mapping on the
GNS quotient space. It provides the genuine carrier-level action machinery
that enables annihilation/creation operators to act on cyclic states.
-/

noncomputable section

namespace InfoGeometry.Prequantum.GNSAction

open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- 
A GNS state whose null set forms a left ideal.
This is the required condition for the algebra to be represented as operators
acting on the quotient space.
-/
structure RepresentationState (A : Type*) [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A] where
  state : AbstractGNSState A
  null_left_ideal : ∀ (a x : A), x ∈ state.gnsNullSet → a * x ∈ state.gnsNullSet

namespace RepresentationState

variable (S : RepresentationState A)

/-- Pull back the state and its left-ideal GNS action along a real algebra
equivalence preserving the involution. -/
def pullback (e : A ≃ₐ[ℝ] A) (he : ∀ x, e (star x) = star (e x)) :
    RepresentationState A where
  state := ⟨RealAlgebraicState.statePullback S.state.state e he⟩
  null_left_ideal := by
    intro a x hx
    change S.state.state.eval (e (star x * x)) = 0 at hx
    have hx' : (e x) ∈ S.state.gnsNullSet := by
      change S.state.state.eval (star (e x) * e x) = 0
      simpa only [map_mul, he] using hx
    have hmul := S.null_left_ideal (e a) (e x) hx'
    change S.state.state.eval (star (e a * e x) * (e a * e x)) = 0 at hmul
    change S.state.state.eval (e (star (a * x) * (a * x))) = 0
    simpa only [map_mul, he] using hmul

/-- The GNS quotient action respects equivalence. -/
theorem gnsEquiv_mul_right (a x y : A) (h_equiv : S.state.gnsEquiv x y) :
    S.state.gnsEquiv (a * x) (a * y) := by
  change S.state.state.gnsEquiv x y at h_equiv
  change S.state.state.gnsEquiv (a * x) (a * y)
  unfold RealAlgebraicState.gnsEquiv at h_equiv ⊢
  have h_diff : a * x - a * y = a * (x - y) := by noncomm_ring
  rw [h_diff]
  exact S.null_left_ideal a (x - y) h_equiv

/-- 
The action of the algebra on the GNS quotient carrier. 
This provides the concrete operator representation on the quotient space.
-/
def act (a : A) (q : AbstractGNSState.gnsQuotient S.state) : 
    AbstractGNSState.gnsQuotient S.state :=
  Quotient.liftOn q (fun x => (Quotient.mk (AbstractGNSState.gnsSetoid S.state) (a * x) : AbstractGNSState.gnsQuotient S.state)) (by
    intro x y h_equiv
    apply Quotient.sound
    exact S.gnsEquiv_mul_right a x y h_equiv
  )

@[simp] theorem act_mk (a x : A) :
    S.act a (Quotient.mk (AbstractGNSState.gnsSetoid S.state) x) = 
      Quotient.mk (AbstractGNSState.gnsSetoid S.state) (a * x) :=
  rfl

/-- The action preserves multiplication (representation property). -/
theorem act_mul (a b : A) (q : AbstractGNSState.gnsQuotient S.state) :
    S.act (a * b) q = S.act a (S.act b q) := by
  induction q using Quotient.inductionOn
  simp [mul_assoc]

/-- The vacuum vector is the quotient of the unit element. -/
def vacuum : AbstractGNSState.gnsQuotient S.state :=
  Quotient.mk (AbstractGNSState.gnsSetoid S.state) 1

/-- Acting on the vacuum recovers the operator. -/
@[simp] theorem act_vacuum (a : A) :
    S.act a S.vacuum = Quotient.mk (AbstractGNSState.gnsSetoid S.state) a := by
  simp [vacuum, mul_one]

/-- The algebraic GNS quotient equivalence intertwines the left actions of an
algebra element and its transported image. -/
theorem gnsQuotientEquiv_intertwines
    (e : A ≃ₐ[ℝ] A) (he : ∀ x, e (star x) = star (e x)) (a : A)
    (q : AbstractGNSState.gnsQuotient (S.pullback e he).state) :
    RealAlgebraicState.gnsQuotientEquiv S.state.state e he
        ((S.pullback e he).act a q) =
      S.act (e a)
        (RealAlgebraicState.gnsQuotientEquiv S.state.state e he q) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      simp only [RepresentationState.act_mk]
      dsimp only [RealAlgebraicState.gnsQuotientEquiv]
      change Quotient.mk _ (e (a * x)) = Quotient.mk _ (e a * e x)
      rw [map_mul]

/-- The GNS vacuum is preserved by the quotient equivalence induced by the
state pullback. -/
theorem gnsQuotientEquiv_vacuum
    (e : A ≃ₐ[ℝ] A) (he : ∀ x, e (star x) = star (e x)) :
    RealAlgebraicState.gnsQuotientEquiv S.state.state e he
        ((S.pullback e he).vacuum) = S.vacuum := by
  dsimp only [RepresentationState.vacuum,
    RealAlgebraicState.gnsQuotientEquiv]
  change Quotient.mk _ (e 1) = Quotient.mk _ 1
  rw [map_one]

end RepresentationState

end InfoGeometry.Prequantum.GNSAction
