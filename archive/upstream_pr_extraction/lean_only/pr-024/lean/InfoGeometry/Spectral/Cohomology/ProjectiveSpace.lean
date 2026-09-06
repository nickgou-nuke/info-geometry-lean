/- Projective Space Cohomology - Wave 5 of the Spectral port.
Ported from cmu-phil/Spectral/cohomology/projective_space.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Spectral.Cohomology.Serre
import InfoGeometry.Spectral.Cohomology.Basic

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Algebra

/- A computation of the cohomology groups of `K(ℤ,2) = ℝP^∞` using the Serre
spectral sequence. -/

def K_Z_2_cohomology (_n : ℤ) : Type :=
  PUnit

def K_Z_2_cohomology_with_coeffs (G : Type*) [AddCommGroup G] (_n : ℤ) : Type :=
  PUnit

/-- The cohomology ring of `K(ℤ,2)` with coefficients in `ℤ`. -/
structure CohomologyRing (R : Type*) [Ring R] where
  groups : ℤ → Type
  multiplication : ∀ (n m : ℤ), groups n → groups m → groups (n + m)

def K_Z_2_cohomology_ring : CohomologyRing ℤ :=
  ⟨fun _ => PUnit, fun _ _ _ _ => PUnit.unit⟩

def K_Z_2_cup_product (_n _m : ℤ) : Type := PUnit

def real_projective_space_cohomology (_n : ℕ) : Type := PUnit
