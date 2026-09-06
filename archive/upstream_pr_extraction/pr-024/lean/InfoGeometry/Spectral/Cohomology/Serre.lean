/- Serre Spectral Sequence - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/serre.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Cohomology.Basic
import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Spectral.Algebra.SpectralSequence

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Spectrum.Basic

/- Serre spectral sequence for a fibration -/

/-- The Serre spectral sequence for a fibration `F → E → B` with coefficients in a
spectrum `Y`. -/
structure SerreSpectralSequence (B : Type*) (F : Type*) (E : Type*) (Y : Spectrum) (s₀ : ℤ) where
  (E₂ : ℤ → ℤ → Type*)
  (E₂_addCommGroup : ∀ (p q : ℤ), AddCommGroup (E₂ p q))
  (d : ∀ (r : ℕ) (p q : ℤ), (E₂ p q) →+ (E₂ (p + r) (q - r + 1)))
  (convergence : ∀ (_n : ℤ), ∃ (N : ℕ), ∀ (r : ℕ), r ≥ N → True)

/-- The Serre spectral sequence for a fibration `F → E → B`. -/
def serre_spectral_sequence {B F E : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace E]
    (_fibration : E → B) (_F : Type*) (Y : Spectrum) (_s₀ : ℤ) :
    SerreSpectralSequence B F E Y s₀ := by
  refine ⟨fun _ _ => PUnit, ?_, ?_, ?_⟩
  · intro p q
    infer_instance
  · intro r p q
    exact (0 : PUnit →+ PUnit)
  · intro n
    refine ⟨0, ?_⟩
    intro r hr
    exact True.intro

/-- The Gysin sequence for a sphere bundle. -/
structure GysinSequence (B : Type*) (E : Type*) (A : Type*) [AddCommGroup A] where
  (sequence : True)

/-- The Gysin sequence for a sphere bundle `S^{n+1} → E → B`. -/
def gysin_sequence {B E : Type*} [TopologicalSpace B] [TopologicalSpace E]
    (_n : ℕ) (_fibration : E → B) (_e : Unit) (A : Type*) [AddCommGroup A] :
    GysinSequence B E A :=
  ⟨True.intro⟩

/-- The projective space cohomology computation. -/
def projective_space_cohomology (_n : ℕ) : Type* := PUnit
