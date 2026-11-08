/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing
import InfoGeometry.Canonical.CyclotomicOperatorSpine
import Mathlib.Tactic.NoncommRing

/-!
# The Nibelung Klein action inside the cyclotomic operator polynomial

An involutive endomorphism is annihilated by `T^2 - 1 = Φ₁(T) Φ₂(T)`, hence
also by the broad degree-25 expression `T (T^24 - 1)`. This records the
Nibelung Peirce-parity action as an operator solution of that polynomial.
It does not claim that the action has primitive order 24 or is a root of
`Φ₂₄`; the affine Klein glide is a separate action with its own translation
square relation.
-/

noncomputable section

namespace InfoGeometry.Canonical.NibelungKleinCyclotomicAction

variable {B : Type*} [Ring B]

abbrev RingEnd (B : Type*) [Ring B] := Module.End ℤ B

/-- Polynomial factors over the integer endomorphism ring. -/
def phi1 (T : RingEnd B) : RingEnd B := T - 1
def phi2 (T : RingEnd B) : RingEnd B := T + 1
def phi4 (T : RingEnd B) : RingEnd B := T ^ 2 + 1
def orderTwoFactor (T : RingEnd B) : RingEnd B := phi1 T * phi2 T
def nibelungMasterP25 (T : RingEnd B) : RingEnd B := T * (T ^ 24 - 1)

/-- Left regular action of a ring element on its additive group. -/
def leftMulEnd (b : B) : RingEnd B :=
  ({ toFun := fun x : B => b * x
     map_zero' := by simp
     map_add' := by intro x y; simp [mul_add] } : B →+ B).toIntLinearMap

/-- The `Φ₁ Φ₂` factor is exactly `T² - 1`, without a commutativity
assumption on the endomorphism ring. -/
theorem orderTwoFactor_eq (T : RingEnd B) :
    orderTwoFactor T = T ^ 2 - 1 := by
  unfold orderTwoFactor phi1 phi2
  noncomm_ring

/-- Any order-two additive operator solves the order-two cyclotomic factor. -/
theorem orderTwoFactor_eq_zero (T : RingEnd B) (hT : T ^ 2 = 1) :
    orderTwoFactor T = 0 := by
  rw [orderTwoFactor_eq, hT, sub_self]

/-- The order-four cyclotomic factor vanishes when the square is `-1`. -/
theorem phi4_eq_zero_of_square_eq_neg_one (T : RingEnd B) (hT : T ^ 2 = -1) :
    phi4 T = 0 := by
  simp [phi4, hT]

/-- Left multiplication represents products faithfully at the level needed
for powers: composing two left actions is left multiplication by the product. -/
theorem leftMulEnd_square (b : B) :
    leftMulEnd b ^ 2 = leftMulEnd (b * b) := by
  ext x
  change b * (b * x) = (b * b) * x
  simp [mul_assoc]

/-- The Dirac belt-twist's left-regular operator is a primitive order-four
cyclotomic solution (`Φ₄(T)=0`), using the matrix square proved by the
Nibelung stage-three owner. -/
theorem diracBeltLeftAction_phi4 :
    phi4 (leftMulEnd InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing.diracBeltTwist) = 0 := by
  have hB :
      InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing.diracBeltTwist *
        InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing.diracBeltTwist = -1 := by
    rcases InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing.stage3_double_krein_dirac_belt_and_v4_package 0 with
      ⟨_, _, _, hB, _, _, _, _, _⟩
    exact hB
  have hT :
      leftMulEnd InfoGeometry.Canonical.KMSStripMobiusKreinNibelungRing.diracBeltTwist ^ 2 = -1 := by
    rw [leftMulEnd_square, hB]
    ext X
    simp [leftMulEnd]
  exact phi4_eq_zero_of_square_eq_neg_one _ hT

/-- An order-two operator is also a solution of the degree-25 umbrella
polynomial used by the repository's cyclotomic spine. -/
theorem nibelungMasterP25_eq_zero_of_order_two (T : RingEnd B) (hT : T ^ 2 = 1) :
    nibelungMasterP25 T = 0 := by
  have h24 : T ^ 24 = 1 := by
    calc
      T ^ 24 = (T ^ 2) ^ 12 := by rw [← pow_mul]
      _ = 1 := by rw [hT]; simp
  simp [nibelungMasterP25, h24]

/-- The Peirce parity conjugation, packaged as a `ℤ`-linear endomorphism. -/
def parityConjEnd (P : B) (hP : P * P = P) : RingEnd B :=
  (InfoGeometry.OperatorAlgebra.PeirceSpine.parityConjRingEquiv hP).toAddMonoidHom.toIntLinearMap

/-- The Peirce parity endomorphism is involutive by the ring owner's action
theorem, and therefore solves both the `Φ₁ Φ₂` and master polynomials. -/
theorem parityConj_cyclotomic_solutions {P : B} (hP : P * P = P) :
    (parityConjEnd P hP) ^ 2 = 1 ∧
    orderTwoFactor (parityConjEnd P hP) = 0 ∧
    nibelungMasterP25 (parityConjEnd P hP) = 0 := by
  have hsq : (parityConjEnd P hP) ^ 2 = 1 := by
    ext X
    change InfoGeometry.OperatorAlgebra.PeirceSpine.parityConj P
      (InfoGeometry.OperatorAlgebra.PeirceSpine.parityConj P X) = X
    exact (InfoGeometry.OperatorAlgebra.PeirceSpine.parityConj_involutive_ring_action
      hP X 1).1
  exact ⟨hsq, orderTwoFactor_eq_zero _ hsq,
    nibelungMasterP25_eq_zero_of_order_two _ hsq⟩

end InfoGeometry.Canonical.NibelungKleinCyclotomicAction
