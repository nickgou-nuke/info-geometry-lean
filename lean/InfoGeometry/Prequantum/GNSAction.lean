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

end RepresentationState

end InfoGeometry.Prequantum.GNSAction
