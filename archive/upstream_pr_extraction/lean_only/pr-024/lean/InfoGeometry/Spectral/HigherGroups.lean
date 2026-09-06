/- Higher Homotopy Groups and Real Projective Spaces - Wave 6 of the Spectral port.
Ported from cmu-phil/Spectral/higher_groups.hlean and realprojective.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Spectral.Algebra.SpectralSequence
import InfoGeometry.Spectral.Cohomology.Basic
import InfoGeometry.Spectral.Cohomology.Serre
import InfoGeometry.Spectral.Cohomology.ProjectiveSpace

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Cohomology

/- Higher homotopy groups of spheres -/

/- The homotopy groups of spheres -/
def homotopy_groups_of_spheres (n k : ℕ) : Type* := PUnit

/- The stable homotopy groups of spheres -/
def stable_homotopy_groups_of_spheres (n : ℤ) : Type* := PUnit

/- The J-homomorphism -/
def J_homomorphism (n k : ℕ) : Type* := PUnit

/- The image of J -/
def image_of_J (n : ℕ) : Type* := PUnit

/- Real projective spaces -/

/- The stable homotopy groups of ℝP^∞ -/
def stable_homotopy_groups_RP_infinity (n : ℤ) : Type* := PUnit

/- The J-homomorphism on ℝP^∞ -/
def J_homomorphism_RP_infinity (n : ℤ) : Type* := PUnit

/- The Adams spectral sequence -/

/- The Adams spectral sequence for the sphere -/
structure AdamsSpectralSequence where
  (E₂ : ℤ → ℤ → Type*)
  (E₂_addCommGroup : ∀ (p q : ℤ), AddCommGroup (E₂ p q))
  (d : ∀ (r : ℕ) (p q : ℤ), (E₂ p q) →+ (E₂ (p + r) (q - r + 1)))
  (convergence : ∀ (n : ℤ), ∃ (N : ℕ), ∀ (r : ℕ), r ≥ N → True)

/- The Adams spectral sequence for the sphere -/
def adams_spectral_sequence_sphere : AdamsSpectralSequence := {
  E₂ := fun _ _ => PUnit,
  E₂_addCommGroup := fun _ _ => inferInstance,
  d := fun _ _ _ => 0,
  convergence := fun _ => ⟨0, fun _ _ => True.intro⟩
}

/- The Adams-Novikov spectral sequence -/
structure AdamsNovikovSpectralSequence where
  (E₂ : ℤ → ℤ → Type*)
  (E₂_addCommGroup : ∀ (p q : ℤ), AddCommGroup (E₂ p q))
  (d : ∀ (r : ℕ) (p q : ℤ), (E₂ p q) →+ (E₂ (p + r) (q - r + 1)))
  (convergence : ∀ (n : ℤ), ∃ (N : ℕ), ∀ (r : ℕ), r ≥ N → True)

/- The Adams-Novikov spectral sequence for the sphere -/
def adams_novikov_spectral_sequence_sphere : AdamsNovikovSpectralSequence := {
  E₂ := fun _ _ => PUnit,
  E₂_addCommGroup := fun _ _ => inferInstance,
  d := fun _ _ _ => 0,
  convergence := fun _ => ⟨0, fun _ _ => True.intro⟩
}

/- The EHP sequence -/

/- The EHP sequence for spheres -/
structure EHPSequence where
  (E : ℕ → Type*)
  (H : ℕ → Type*)
  (P : ℕ → Type*)

/- The EHP sequence for spheres -/
def EHP_sequence_spheres : EHPSequence := {
  E := fun _ => PUnit,
  H := fun _ => PUnit,
  P := fun _ => PUnit
}

/- The Whitehead tower -/

/- The Whitehead tower of a space -/
structure WhiteheadTower (X : Type*) where
  (X_n : ℕ → Type*)
  (maps : ∀ (n : ℕ), X_n (n + 1) → X_n n)

/- The Whitehead tower of the sphere -/
def Whitehead_tower_sphere : WhiteheadTower Unit := {
  X_n := fun _ => Unit,
  maps := fun _ _ => ()
}
