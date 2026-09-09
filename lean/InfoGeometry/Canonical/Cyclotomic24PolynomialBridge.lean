import InfoGeometry.Canonical.CyclotomicOperatorSpine

/-!
  A small canonical bridge for the upstream 24-fold polynomial vocabulary.

  The operator-valued owner is `CyclotomicOperatorSpine`; this file only
  exposes the polynomial names used by the upstream proposal and does not
  duplicate its operator construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cyclotomic24PolynomialBridge

open Polynomial
open InfoGeometry.Canonical.CyclotomicOperatorSpine

def master25 : ℤ[X] := X * (X ^ 24 - 1)

theorem master25_factorization :
    master25 = X * (X ^ 24 - 1) := by
  rfl

theorem master25_eq_zero_of_pow24_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (hT : T ^ 24 = 1) :
    masterP25 T = 0 := by
  exact masterP25_eq_zero_of_pow24_eq_one T hT

theorem tripotent_factor_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (hT : T ^ 3 = T) :
    T * phi1Eval T * phi2Eval T = 0 := by
  exact InfoGeometry.Canonical.CyclotomicOperatorSpine.tripotent_factor_zero T hT

theorem complex_structure_factor_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (hT : T ^ 3 = -T) :
    T * phi4Eval T = 0 := by
  exact InfoGeometry.Canonical.CyclotomicOperatorSpine.complex_cubic_factor_zero T hT

theorem cyclotomic24_operator_annihilator_packet {V : Type*}
    [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) :
    (T ^ 4 = -1 → masterP25 T = 0) ∧
    (T ^ 6 = 1 → masterP25 T = 0) ∧
    (T ^ 12 = 1 → masterP25 T = 0) ∧
    (T ^ 24 = 1 → masterP25 T = 0) := by
  constructor
  · intro h
    exact masterP25_eq_zero_of_pow24_eq_one T (by
      calc T ^ 24 = (T ^ 4) ^ 6 := by rw [show (24 : ℕ) = 4 * 6 by norm_num, pow_mul]
           _ = 1 := by rw [h]; noncomm_ring)
  constructor
  · intro h
    exact masterP25_eq_zero_of_pow24_eq_one T (by
      calc T ^ 24 = (T ^ 6) ^ 4 := by rw [show (24 : ℕ) = 6 * 4 by norm_num, pow_mul]
           _ = 1 := by rw [h]; noncomm_ring)
  constructor
  · intro h
    exact masterP25_eq_zero_of_pow24_eq_one T (by
      calc T ^ 24 = (T ^ 12) ^ 2 := by rw [show (24 : ℕ) = 12 * 2 by norm_num, pow_mul]
           _ = 1 := by rw [h]; noncomm_ring)
  · intro h; exact masterP25_eq_zero_of_pow24_eq_one T h

end InfoGeometry.Canonical.Cyclotomic24PolynomialBridge
