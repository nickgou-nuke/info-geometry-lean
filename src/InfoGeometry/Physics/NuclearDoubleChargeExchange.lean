/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.NuclearThoulessDensity
import Mathlib.Tactic.NoncommRing

/-!
# Double charge exchange through opposite Peirce corners

These are finite associative-ring identities for transitions through a
Majorana-labelled opposite-corner insertion. They do not formalize the
physical Schechter–Valle black-box argument or assert an empirical mass.
-/

namespace InfoGeometry.Physics.NuclearDoubleChargeExchange

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- A single-site double raising transition with a lowering-corner insertion. -/
def doubleChargeExchange (P A C : B) : B :=
  conePlus P A * coneMinus P C * conePlus P A

/-- The symmetric polarization of the inserted transition over two amplitudes. -/
def doubleChargeExchangePolarization (P A₁ A₂ C : B) : B :=
  conePlus P A₁ * coneMinus P C * conePlus P A₂ +
    conePlus P A₂ * coneMinus P C * conePlus P A₁

/-- Consecutive same-direction transitions through one Peirce cut vanish. -/
theorem bare_double_raise_zero {P : B} (hP : P * P = P) (A₁ A₂ : B) :
    conePlus P A₁ * conePlus P A₂ = 0 := by
  unfold conePlus
  peirce_nf hP

/-- The inserted transition factors on either side through the symmetric core. -/
theorem double_charge_exchange_factorization {P : B}
    (hP : P * P = P) (A C : B) :
    doubleChargeExchange P A C = genV P A C * conePlus P A ∧
    doubleChargeExchange P A C = conePlus P A * genV P A C := by
  constructor <;>
    simp [doubleChargeExchange, genV, anticomm, conePlus, coneMinus] <;>
    peirce_nf hP

/-- Nonvanishing of the inserted transition forces both algebraic factors
to be nonzero. This is only the direct factorization consequence in this ring. -/
theorem nonzero_double_exchange_factors {P : B}
    (hP : P * P = P) (A C : B)
    (hT : doubleChargeExchange P A C ≠ 0) :
    coneMinus P C ≠ 0 ∧ genV P A C ≠ 0 := by
  constructor
  · intro hM
    apply hT
    simp [doubleChargeExchange, hM]
  · intro hV
    apply hT
    rw [(double_charge_exchange_factorization hP A C).1, hV]
    simp

/-- Polarizing the amplitude gives the two diagonal transitions plus both
cross-channel insertion orders. -/
theorem double_charge_exchange_polarization {P : B}
    (A₁ A₂ C : B) :
    doubleChargeExchange P (A₁ + A₂) C =
      doubleChargeExchange P A₁ C + doubleChargeExchange P A₂ C +
        doubleChargeExchangePolarization P A₁ A₂ C := by
  simp [doubleChargeExchange, doubleChargeExchangePolarization, conePlus]
  noncomm_ring

/-- The same-direction bare product remains zero even for distinct amplitudes. -/
theorem bare_double_raise_sum_square_zero {P : B}
    (hP : P * P = P) (A₁ A₂ : B) :
    (conePlus P A₁ + conePlus P A₂) *
      (conePlus P A₁ + conePlus P A₂) = 0 := by
  have h₁₂ := bare_double_raise_zero hP A₁ A₂
  have h₂₁ := bare_double_raise_zero hP A₂ A₁
  have h₁₁ := bare_double_raise_zero hP A₁ A₁
  have h₂₂ := bare_double_raise_zero hP A₂ A₂
  noncomm_ring [h₁₂, h₂₁, h₁₁, h₂₂]

end InfoGeometry.Physics.NuclearDoubleChargeExchange
