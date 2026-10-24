/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.PenneyOperatorEquation
import Mathlib.Tactic

/-!
# Penney: left intertwiners and the right isospin commutant

A left intertwiner transports both quaternionic component equations without
mixing their right sectors. This is a representation-independent covariance
criterion, not a construction of the Lorentz spin group action.
-/
namespace InfoGeometry.Canonical.PenneyLeftCovariance

open InfoGeometry.Canonical.PenneyOctonionIsospin

variable {A : Type*} [Ring A]

/-- The mass and both first-order operators intertwine one left action. -/
structure LeftIntertwines (s p q m p' q' m' : A) : Prop where
  p : p' * s = s * p
  q : q' * s = s * q
  mass : m' * s = s * m

/-- Coupled equations transform covariantly under an actual intertwiner. -/
theorem coupled_left_intertwines
    {s p q m p' q' m' χ φ : A}
    (h : LeftIntertwines s p q m p' q' m')
    (heq : Coupled p q m χ φ) :
    Coupled p' q' m' (s * χ) (s * φ) := by
  rcases heq with ⟨hχ, hφ⟩
  constructor
  · calc
      p' * (s * χ) = (p' * s) * χ := (mul_assoc _ _ _).symm
      _ = (s * p) * χ := by rw [h.p]
      _ = s * (p * χ) := mul_assoc _ _ _
      _ = s * (m * φ) := by rw [hχ]
      _ = (m' * s) * φ := by rw [h.mass, mul_assoc]
      _ = m' * (s * φ) := mul_assoc _ _ _
  · calc
      q' * (s * φ) = (q' * s) * φ := (mul_assoc _ _ _).symm
      _ = (s * q) * φ := by rw [h.q]
      _ = s * (q * φ) := mul_assoc _ _ _
      _ = s * (m * χ) := by rw [hφ]
      _ = (m' * s) * χ := by rw [h.mass, mul_assoc]
      _ = m' * (s * χ) := mul_assoc _ _ _

/-- Left transformations commute with all right-isospin multiplications. -/
theorem left_right_commute (s x k : A) :
    s * (x * k) = (s * x) * k := (mul_assoc _ _ _).symm

/-- Projecting onto any right idempotent can be done before or after transport. -/
theorem right_sector_transport
    {s p q m p' q' m' χ φ : A} (e : A)
    (h : LeftIntertwines s p q m p' q' m')
    (heq : Coupled p q m χ φ) :
    Coupled p' q' m' (s * (χ * e)) (s * (φ * e)) ∧
    s * (χ * e) = (s * χ) * e ∧
    s * (φ * e) = (s * φ) * e := by
  refine ⟨coupled_left_intertwines h (coupled_right_invariant heq e),
    left_right_commute s χ e, left_right_commute s φ e⟩

end InfoGeometry.Canonical.PenneyLeftCovariance
