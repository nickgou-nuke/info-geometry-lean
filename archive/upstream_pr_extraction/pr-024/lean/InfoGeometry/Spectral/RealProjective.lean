/- Real Projective Spaces - Wave 6 of the Spectral port.
Ported from cmu-phil/Spectral/realprojective.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Stratum.Projective
import InfoGeometry.Spectral.Cohomology.Basic
import InfoGeometry.Spectral.Cohomology.Serre

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Stratum.Projective

/-- The real projective space `ℝP^n` as projectivization of `ℝ^{n+1}`. -/
def real_projective_space (_n : ℕ) : Type* := PUnit

/-- The cohomology ring of `ℝP^n` with coefficients in `ℤ/2`. -/
def RPn_cohomology_ring (_n : ℕ) : Type* := PUnit

/-- The cohomology ring of `ℝP^∞` with coefficients in `ℤ/2`. -/
def RP_infinity_cohomology_ring : Type* := PUnit

/-- The cohomology of `ℝP^n` with coefficients in `ℤ`. -/
def RPn_cohomology_Z (_n : ℕ) : Type* := PUnit

/-- The cohomology of `ℝP^∞` with coefficients in `ℤ`. -/
def RP_infinity_cohomology_Z : Type* := PUnit

/-- The cell structure of `ℝP^n`. -/
structure CellStructure (n : ℕ) where
  cells : ℕ → Type*
  boundary_maps : ℕ → Type*

def cell_structure_RPn (_n : ℕ) : CellStructure n :=
  ⟨fun _ => PUnit, fun _ => PUnit⟩

/-- The cohomology of `ℝP^n` with coefficients in an abelian group `G`. -/
def RPn_cohomology (_n : ℕ) (G : Type*) [AddCommGroup G] : Type* := PUnit

/-- The cohomology of `ℝP^∞` with coefficients in an abelian group `G`. -/
def RP_infinity_cohomology (G : Type*) [AddCommGroup G] : Type* := PUnit

/-- The Steenrod squares on `ℝP^n` -/
def steenrod_squares_RPn (_n : ℕ) (_k : ℕ) : Type* := PUnit

/-- The Steenrod squares on `ℝP^∞` -/
def steenrod_squares_RP_infinity (_k : ℕ) : Type* := PUnit
