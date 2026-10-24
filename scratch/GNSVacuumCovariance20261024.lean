/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Prequantum.GNSAction

/-!
# Algebraic GNS vacuum annihilator covariance

Two lemmas on the existing real algebraic GNS quotient. Zero is its explicit
quotient class; no additive structure or Hilbert completion is introduced.
Sandbox candidate: not compiled.
-/

namespace InfoGeometry.Prequantum.GNSAction.RepresentationState

open InfoGeometry.Prequantum.AlgebraicGNSState
open InfoGeometry.Prequantum.GNSBridge

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- An element annihilates the cyclic vacuum precisely when it is GNS-null. -/
theorem act_vacuum_eq_zero_iff_null (S : RepresentationState A) (a : A) :
    S.act a S.vacuum = Quotient.mk (AbstractGNSState.gnsSetoid S.state) 0 ↔
      a ∈ S.state.gnsNullSet := by
  rw [S.act_vacuum]
  constructor
  · intro h
    have hrel := Quotient.exact h
    change a - 0 ∈ S.state.gnsNullSet at hrel
    simpa only [sub_zero] using hrel
  · intro h
    apply Quotient.sound
    change a - 0 ∈ S.state.gnsNullSet
    simpa only [sub_zero] using h

/-- Pullback by a star-preserving algebra equivalence transports the vacuum
annihilator to the original state's vacuum annihilator under `e`. -/
theorem pullback_act_vacuum_eq_zero_iff (S : RepresentationState A)
    (e : A ≃ₐ[ℝ] A) (he : ∀ x, e (star x) = star (e x)) (a : A) :
    (S.pullback e he).act a (S.pullback e he).vacuum =
        Quotient.mk (AbstractGNSState.gnsSetoid (S.pullback e he).state) 0 ↔
      S.act (e a) S.vacuum =
        Quotient.mk (AbstractGNSState.gnsSetoid S.state) 0 := by
  rw [act_vacuum_eq_zero_iff_null, act_vacuum_eq_zero_iff_null]
  change a ∈ (RealAlgebraicState.statePullback S.state.state e he).gnsNullSet ↔
    e a ∈ S.state.state.gnsNullSet
  simpa only [RealAlgebraicState.gnsEquiv, map_zero, sub_zero] using
    (RealAlgebraicState.statePullback_gnsEquiv_iff S.state.state e he a 0)

end InfoGeometry.Prequantum.GNSAction.RepresentationState
