/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib

/-!
# Canonical Drazin--Cartan anomaly identities

The identities below require only an idempotent and associative multiplication.
They are the general algebraic core of projector-mismatch counterexamples.
-/

namespace InfoGeometry.Canonical.DrazinCartanAlternatives

variable {A : Type*} [Ring A]

def lieBracket (x y : A) : A := x * y - y * x

def jordanProd (x y : A) : A := x * y + y * x

def spectralGrading (p : A) : A := 2 • p - 1

def anomaly (p q : A) : A := lieBracket p q

theorem spectralGrading_sq_eq_one {p : A} (hp : p * p = p) :
    spectralGrading p * spectralGrading p = 1 := by
  unfold spectralGrading
  rw [two_nsmul]
  calc
    (p + p - 1) * (p + p - 1) =
        4 • (p * p) - 4 • p + 1 := by noncomm_ring
    _ = 4 • p - 4 • p + 1 := by rw [hp]
    _ = 1 := by abel

theorem spectralGrading_anomaly_anticommutes {p q : A} (hp : p * p = p) :
    jordanProd (spectralGrading p) (anomaly p q) = 0 := by
  unfold jordanProd spectralGrading anomaly lieBracket
  rw [two_nsmul]
  calc
    (p + p - 1) * (p * q - q * p) +
        (p * q - q * p) * (p + p - 1) =
        2 • ((p * p) * q - p * q) +
          2 • (q * p - q * (p * p)) := by noncomm_ring
    _ = 0 := by rw [hp, sub_self, sub_self, smul_zero, add_zero]

theorem anomaly_bridge {p q r : A} :
    lieBracket p (r - q) = anomaly p r - anomaly p q := by
  change p * (r - q) - (r - q) * p =
    (p * r - r * p) - (p * q - q * p)
  noncomm_ring

theorem spectral_bridge {p q r : A} :
    lieBracket (spectralGrading p) (r - q) =
      2 • (anomaly p r - anomaly p q) := by
  change (2 • p - 1) * (r - q) - (r - q) * (2 • p - 1) =
    2 • ((p * r - r * p) - (p * q - q * p))
  rw [two_nsmul]
  noncomm_ring

theorem anomaly_eq_zero_iff_commutes {p q : A} :
    anomaly p q = 0 ↔ p * q = q * p := by
  unfold anomaly lieBracket
  exact sub_eq_zero

/-- The square of the odd commutator consists of two diagonal return products.
Oddness by itself does not make either product vanish. -/
theorem anomaly_square_eq_neg_return_products {p q : A} (hp : p * p = p) :
    anomaly p q * anomaly p q =
      -(p * q * (1 - p) * q * p + (1 - p) * q * p * q * (1 - p)) := by
  have hpp (x : A) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  unfold anomaly lieBracket
  noncomm_ring [hp, hpp]

/-- Square-zero of the commutator is exactly vanishing of both return
products. Their distinct Peirce supports prevent cancellation, in every
characteristic and without an involution or an idempotence condition on `q`. -/
theorem anomaly_square_zero_iff_return_products_zero {p q : A} (hp : p * p = p) :
    anomaly p q * anomaly p q = 0 ↔
      p * q * (1 - p) * q * p = 0 ∧ (1 - p) * q * p * q * (1 - p) = 0 := by
  have hpp (x : A) : p * (p * x) = p * x := by rw [← mul_assoc, hp]
  have hleft : p * (anomaly p q * anomaly p q) * p =
      -(p * q * (1 - p) * q * p) := by
    unfold anomaly lieBracket
    noncomm_ring [hp, hpp]
  have hright : (1 - p) * (anomaly p q * anomaly p q) * (1 - p) =
      -((1 - p) * q * p * q * (1 - p)) := by
    unfold anomaly lieBracket
    noncomm_ring [hp, hpp]
  constructor
  · intro hz
    constructor
    · rw [hz, mul_zero, zero_mul] at hleft
      exact neg_eq_zero.mp hleft.symm
    · rw [hz, mul_zero, zero_mul] at hright
      exact neg_eq_zero.mp hright.symm
  · rintro ⟨hl, hr⟩
    rw [anomaly_square_eq_neg_return_products hp, hl, hr, add_zero, neg_zero]

theorem both_anomalies_vanish_iff_joint_centralizer {p q r : A} :
    (anomaly p q = 0 ∧ anomaly p r = 0) ↔
      (p * q = q * p ∧ p * r = r * p) := by
  rw [anomaly_eq_zero_iff_commutes, anomaly_eq_zero_iff_commutes]

end InfoGeometry.Canonical.DrazinCartanAlternatives
