/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Prequantum.AlgebraicGNSState

/-!
# Strict positivity of the algebraic GNS quotient

Genuine proof supplied for the placeholder-bearing `FirthWightmanGNS` stash
lane.  That lane stated `GNS_StrictPositivity_Polymorphic` using a `repr`
operation on the quotient, which is not part of the current
`RealAlgebraicState.GNSQuotient` carrier.  Here the mathematically equivalent
representative-level statement is proved: a representative `x` is null exactly
when its quotient class equals the zero class.  This follows directly from the
owner's `gnsEquiv` definition (`x - y ∈ gnsNullSet`) and `mem_gnsNullSet_iff`.
-/

noncomputable section

namespace InfoGeometry.Prequantum.AlgebraicGNSState.GNSQuotientStrictPositivity

open InfoGeometry.Prequantum.AlgebraicGNSState

variable {A : Type*} [Ring A] [Algebra ℝ A] [StarRing A] [StarModule ℝ A]

/-- A representative is null precisely when it is GNS-equivalent to zero. -/
theorem eval_eq_zero_iff_gnsEquiv_zero (F : RealAlgebraicState A) (x : A) :
    F.eval (star x * x) = 0 ↔ F.gnsEquiv x 0 := by
  unfold RealAlgebraicState.gnsEquiv
  rw [sub_zero]
  exact F.mem_gnsNullSet_iff x

/-- Strict positivity at the quotient: the quadratic readout of a
representative vanishes iff its class is the zero class. -/
theorem gns_strict_positivity (F : RealAlgebraicState A) (x : A) :
    F.eval (star x * x) = 0 ↔
      Quotient.mk F.gnsSetoid x = Quotient.mk F.gnsSetoid (0 : A) := by
  rw [eval_eq_zero_iff_gnsEquiv_zero]
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

end InfoGeometry.Prequantum.AlgebraicGNSState.GNSQuotientStrictPositivity
