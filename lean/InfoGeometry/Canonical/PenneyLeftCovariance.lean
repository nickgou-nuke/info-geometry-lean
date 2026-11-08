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

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion
open InfoGeometry.Canonical.PenneyOctonionIsospin

variable {A : Type*} [Ring A]

/-- The mass and both first-order operators intertwine one left action. -/
def LeftIntertwines (s p q m p' q' m' : A) : Prop :=
  p' * s = s * p ∧ q' * s = s * q ∧ m' * s = s * m

theorem LeftIntertwines.p {s p q m p' q' m' : A}
    (h : LeftIntertwines s p q m p' q' m') : p' * s = s * p := h.1

theorem LeftIntertwines.q {s p q m p' q' m' : A}
    (h : LeftIntertwines s p q m p' q' m') : q' * s = s * q := h.2.1

theorem LeftIntertwines.mass {s p q m p' q' m' : A}
    (h : LeftIntertwines s p q m p' q' m') : m' * s = s * m := h.2.2

/-- Constructive unit-similarity left conjugate `u * p * u⁻¹`. -/
def leftConjugate (u : Aˣ) (p : A) : A :=
  (u : A) * p * (↑u⁻¹ : A)

/-- Zero-hypothesis intertwining law for `leftConjugate u p`. -/
@[simp] theorem leftConjugate_intertwines (u : Aˣ) (p : A) :
    leftConjugate u p * (u : A) = (u : A) * p := by
  dsimp [leftConjugate]
  rw [mul_assoc ((u : A) * p) (↑u⁻¹ : A) (u : A), Units.inv_mul, mul_one]

/-- Zero-hypothesis construction of `LeftIntertwines` from any unit `u : Aˣ`. -/
theorem leftIntertwines_leftConjugate (u : Aˣ) (p q m : A) :
    LeftIntertwines (u : A) p q m
      (leftConjugate u p) (leftConjugate u q) (leftConjugate u m) :=
  ⟨leftConjugate_intertwines u p,
   leftConjugate_intertwines u q,
   leftConjugate_intertwines u m⟩

/-- Zero-hypothesis residual transport under `leftConjugate u`. -/
theorem leftConjugate_residual_transport (u : Aˣ) (p m χ φ : A) :
    leftConjugate u p * ((u : A) * χ) - leftConjugate u m * ((u : A) * φ) =
      (u : A) * (p * χ - m * φ) := by
  calc
    leftConjugate u p * ((u : A) * χ) - leftConjugate u m * ((u : A) * φ) =
      (leftConjugate u p * (u : A)) * χ - (leftConjugate u m * (u : A)) * φ := by
      rw [mul_assoc, mul_assoc]
    _ = ((u : A) * p) * χ - ((u : A) * m) * φ := by
      rw [leftConjugate_intertwines, leftConjugate_intertwines]
    _ = (u : A) * (p * χ - m * φ) := by
      rw [mul_assoc, mul_assoc, ← mul_sub]

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

/-- Zero-hypothesis coupled transport under `leftConjugate u`. -/
theorem coupled_leftConjugate (u : Aˣ) {p q m χ φ : A}
    (heq : Coupled p q m χ φ) :
    Coupled (leftConjugate u p) (leftConjugate u q) (leftConjugate u m)
      ((u : A) * χ) ((u : A) * φ) :=
  coupled_left_intertwines (leftIntertwines_leftConjugate u p q m) heq

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

section SplitQuaternionIntertwiner

variable {F : Type*} [CommRing F] [StarRing F]

/-- Constructive zero-hypothesis intertwining of `(peircePlus, peirceMinus, wheelJ)`
by the Tits–Bruhat element `bruhatS` on `SplitQuaternion F`. -/
theorem bruhatS_leftIntertwines_peirce :
    LeftIntertwines (bruhatS : SplitQuaternion F)
      peircePlus peirceMinus wheelJ
      peirceMinus peircePlus wheelJ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · dsimp [bruhatS]
    rw [← peircePlus_add_peirceMinus]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [peircePlus, peirceMinus, wheelJ, peirceSeedD, peirceSeedB]

end SplitQuaternionIntertwiner

end InfoGeometry.Canonical.PenneyLeftCovariance
