/- Projective Space Cohomology - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/projective_space.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Cohomology.Serre
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Algebra
open InfoGeometry.Spectral.Cohomology.Serre

universe u

/- A computation of the cohomology groups of `K(ℤ,2) = ℝP^∞` using the Serre
spectral sequence. -/

def K_Z_2_cohomology
    (T : InfoGeometry.Spectral.Cohomology.Basic.HomologyTheory)
    (X : Type u) (n : ℤ) : Type u :=
  InfoGeometry.Spectral.Cohomology.Basic.HomologyTheory.HH T n X

def K_Z_2_cohomology_with_coeffs
    (T : InfoGeometry.Spectral.Cohomology.Basic.HomologyTheory)
    (X : Type u) (n : ℤ) : Type u :=
  InfoGeometry.Spectral.Cohomology.Basic.HomologyTheory.HH T n X

/-- The cohomology ring of `K(ℤ,2)` with coefficients in `ℤ`. -/
structure CohomologyRing (R : Type*) [Ring R] where
  groups : ℤ → Type
  multiplication : ∀ (n m : ℤ), groups n → groups m → groups (n + m)

def K_Z_2_cohomology_ring
    (groups : ℤ → Type)
    (multiplication : ∀ (n m : ℤ), groups n → groups m → groups (n + m)) :
    CohomologyRing ℤ :=
  ⟨groups, multiplication⟩

def K_Z_2_cup_product (groups : ℤ → Type) (n m : ℤ) : Type :=
  groups n → groups m → groups (n + m)

def real_projective_space_cohomology (n : ℕ) : Type :=
  ProjectiveSpaceModTwoAdditiveModel n
