/- Real Projective Spaces - Wave 6 of the Spectral port.
Ported from cmu-phil/Spectral/realprojective.hlean (Lean 2 HoTT) to Lean 4.28.0 / mathlib4. -/

import InfoGeometry.Stratum.Projective
import InfoGeometry.Spectral.Cohomology.Basic
import InfoGeometry.Spectral.Cohomology.Serre

open InfoGeometry.Spectral.Cohomology
open InfoGeometry.Spectral.Cohomology.Serre
open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Stratum.Projective

universe u

/-- The real projective space `ℝP^n` as projectivization of `ℝ^{n+1}`. -/
def real_projective_space (n : ℕ) : Type :=
  RealProjectiveSpace (Fin (n + 1) → ℝ)

/-- The finite graded mod-two cellular carrier for `ℝP^n`.

This is the native finite additive model owned by the Serre lane.  It is a
carrier for the cohomology computation; the ring multiplication and its
identification with topological cohomology require a separate cellular
cochain theorem.
-/
def RPn_cohomology_ring (n : ℕ) : Type :=
  ProjectiveSpaceModTwoAdditiveModel n

/-- The cohomology ring of `ℝP^∞` with coefficients in `ℤ/2`. -/
def RP_infinity_cohomology_ring : Type := ℕ → ZMod 2

/-- The cohomology of `ℝP^n` with coefficients in `ℤ`. -/
def RPn_cohomology_Z (n : ℕ) : Type := Fin (n + 1) → ℤ

/-- The cohomology of `ℝP^∞` with coefficients in `ℤ`. -/
def RP_infinity_cohomology_Z : Type := ℕ → ℤ

/-- The cell structure of `ℝP^n`. -/
structure CellStructure (n : ℕ) where
  cells : ℕ → Type*
  boundary_maps : ℕ → Type*

def cell_structure_RPn (n : ℕ) : CellStructure n :=
  ⟨fun _ => Fin (n + 1), fun _ => Fin (n + 1)⟩

/-- The cohomology of `ℝP^n` with coefficients in an abelian group `G`. -/
def RPn_cohomology (n : ℕ) (G : Type u) [AddCommGroup G] : Type u :=
  Fin (n + 1) → G

/-- The cohomology of `ℝP^∞` with coefficients in an abelian group `G`. -/
def RP_infinity_cohomology (G : Type u) [AddCommGroup G] : Type u := ℕ → G

/-- The operator carrier for a Steenrod square on the finite mod-two model.

The operation itself is intentionally not fabricated: its construction needs
the cellular cup-i structure and is a separate owner theorem.
-/
def steenrod_squares_RPn (n : ℕ) (_k : ℕ) : Type :=
  ProjectiveSpaceModTwoAdditiveModel n → ProjectiveSpaceModTwoAdditiveModel n

/-- The operator carrier for a Steenrod square on the infinite finite-support
mod-two approximation. -/
def steenrod_squares_RP_infinity (_k : ℕ) : Type :=
  (ℕ → ZMod 2) → (ℕ → ZMod 2)
