/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.AlbertCayleyDickson
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Penney (1971): octonions and right isospin

The doubled equation uses the existing nonassociative AlbertStep product.
The right-isospin lemmas live only in the associative component algebra.
No Lorentz covariance, PDE, or analytic positivity is asserted here.
-/

namespace InfoGeometry.Canonical.PenneyOctonionIsospin

open InfoGeometry.Canonical.AlbertCayleyDickson

section DoubledEquation

variable {F A : Type*} [CommRing F] [Ring A] [Algebra F A] [StarRing A]

/-- Exact two-component expansion of the existing Cayley–Dickson product. -/
theorem doubled_wave_zero_iff (γ : F) (p q χ φ : A) :
    AlbertStep.mul (γ := γ) (⟨p, q⟩ : AlbertStep F A γ)
        (⟨χ, φ⟩ : AlbertStep F A γ) = 0 ↔
      p * χ + γ • (star φ * q) = 0 ∧ φ * p + q * star χ = 0 := by
  constructor
  · intro h
    constructor
    · have hp := congrArg AlbertStep.p h
      simpa [AlbertStep.mul] using hp
    · have hq := congrArg AlbertStep.q h
      simpa [AlbertStep.mul] using hq
  · rintro ⟨hp, hq⟩
    apply AlbertStep.ext
    · simpa [AlbertStep.mul] using hp
    · simpa [AlbertStep.mul] using hq

end DoubledEquation

section RightIsospin

variable {A : Type*} [Ring A]

/-- Coupled equations with coefficients acting on the left. -/
def Coupled (p q m χ φ : A) : Prop :=
  p * χ = m * φ ∧ q * φ = m * χ

/-- Arbitrary right multiplication preserves the coupled left action. -/
theorem coupled_right_invariant {p q m χ φ : A}
    (h : Coupled p q m χ φ) (k : A) :
    Coupled p q m (χ * k) (φ * k) := by
  rcases h with ⟨h₁, h₂⟩
  constructor
  · calc
      p * (χ * k) = (p * χ) * k := (mul_assoc _ _ _).symm
      _ = (m * φ) * k := by rw [h₁]
      _ = m * (φ * k) := mul_assoc _ _ _
  · calc
      q * (φ * k) = (q * φ) * k := (mul_assoc _ _ _).symm
      _ = (m * χ) * k := by rw [h₂]
      _ = m * (χ * k) := mul_assoc _ _ _

/-- Each idempotent defines an invariant right sector. -/
theorem coupled_right_projected {p q m χ φ : A}
    (h : Coupled p q m χ φ) (e : A) (he : e * e = e) :
    Coupled p q m (χ * e) (φ * e) ∧
    (χ * e) * e = χ * e ∧ (φ * e) * e = φ * e := by
  refine ⟨coupled_right_invariant h e, ?_, ?_⟩
  · rw [mul_assoc, he]
  · rw [mul_assoc, he]

/-- Complementary right sectors sum to the original element. -/
theorem right_sector_decomposition (x e f : A)
    (he : e * e = e) (hf : f * f = f)
    (hef : e * f = 0) (hfe : f * e = 0) (hsum : e + f = 1) :
    x * e + x * f = x ∧
    (x * e) * f = 0 ∧ (x * f) * e = 0 ∧
    (x * e) * e = x * e ∧ (x * f) * f = x * f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_add, hsum, mul_one]
  · rw [mul_assoc, hef, mul_zero]
  · rw [mul_assoc, hfe, mul_zero]
  · rw [mul_assoc, he]
  · rw [mul_assoc, hf]

end RightIsospin

section MatrixWitness

abbrev Mat2Z := Matrix (Fin 2) (Fin 2) ℤ

def isoPlus : Mat2Z := !![1, 0; 0, 0]
def isoMinus : Mat2Z := !![0, 0; 0, 1]

theorem isoPlus_idempotent : isoPlus * isoPlus = isoPlus := by decide
theorem isoMinus_idempotent : isoMinus * isoMinus = isoMinus := by decide
theorem isoPlus_mul_isoMinus : isoPlus * isoMinus = 0 := by decide
theorem isoMinus_mul_isoPlus : isoMinus * isoPlus = 0 := by decide
theorem isoPlus_add_isoMinus : isoPlus + isoMinus = 1 := by decide

theorem matrix_isospin_decomposition (x : Mat2Z) :
    x * isoPlus + x * isoMinus = x ∧
    (x * isoPlus) * isoMinus = 0 ∧
    (x * isoMinus) * isoPlus = 0 := by
  rcases right_sector_decomposition x isoPlus isoMinus
      isoPlus_idempotent isoMinus_idempotent
      isoPlus_mul_isoMinus isoMinus_mul_isoPlus isoPlus_add_isoMinus with
    ⟨h₁, h₂, h₃, _, _⟩
  exact ⟨h₁, h₂, h₃⟩

end MatrixWitness

end InfoGeometry.Canonical.PenneyOctonionIsospin
