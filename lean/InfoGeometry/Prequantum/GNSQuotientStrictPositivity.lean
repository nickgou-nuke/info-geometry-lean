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

/-- The GNS quadratic pairing is well-defined on quotient classes: replacing
either representative by a GNS-equivalent one does not change
`F.eval (star x * y)`.  This is the algebraic core of the Hilbert-space
inner product on the GNS quotient, proved here without constructing that
completion. -/
theorem gns_pairing_wellDefined (F : RealAlgebraicState A) {x₁ x₂ y₁ y₂ : A}
    (hx : F.gnsEquiv x₁ x₂) (hy : F.gnsEquiv y₁ y₂) :
    F.eval (star x₁ * y₁) = F.eval (star x₂ * y₂) := by
  have ha : x₁ - x₂ ∈ F.gnsNullSet := hx
  have hb : y₁ - y₂ ∈ F.gnsNullSet := hy
  have h1 : F.eval (star (x₁ - x₂) * y₂) = 0 :=
    F.state_null_product_zero y₂ (x₁ - x₂) ha
  have hb_eval : F.eval (star (y₁ - y₂) * x₁) = 0 :=
    F.state_null_product_zero x₁ (y₁ - y₂) hb
  have h2 : F.eval (star x₁ * (y₁ - y₂)) = 0 := by
    simpa [RealAlgebraicState.eval] using (F.symmetric x₁ (y₁ - y₂)).symm.trans hb_eval
  have hdiff : star x₁ * y₁ - star x₂ * y₂ =
      star (x₁ - x₂) * y₂ + star x₁ * (y₁ - y₂) := by
    rw [star_sub]
    noncomm_ring
  have hzero : F.eval (star x₁ * y₁) - F.eval (star x₂ * y₂) = 0 := by
    change F.toLinearMap (star x₁ * y₁) - F.toLinearMap (star x₂ * y₂) = 0
    rw [← F.toLinearMap.map_sub, hdiff, F.toLinearMap.map_add]
    change F.eval (star (x₁ - x₂) * y₂) + F.eval (star x₁ * (y₁ - y₂)) = 0
    rw [h1, h2, add_zero]
  exact sub_eq_zero.mp hzero

end InfoGeometry.Prequantum.AlgebraicGNSState.GNSQuotientStrictPositivity
