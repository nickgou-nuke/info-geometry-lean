import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-!
# InfoGeometry.Projective.TwistorBlockGrid

This file provides a bookkeeping model for a `3 × 3` grid of `2 × 2` real
blocks. It is only a diagrammatic carrier for later incidence formulas.

It does not claim an algebra isomorphism
`J_3(\mathbb{O}_s) ≃ M_3(M_2(\mathbb{R}))`.
The split-octonion and Albert layers remain nonassociative and are handled in
their own owner files.
-/

namespace InfoGeometry.Projective

/-- 
A single block in the `3 × 3` grid, represented here by a `2 × 2` real matrix.
This is a coordinate carrier only, not an algebra identification.
-/
abbrev TwistorBlock := Matrix (Fin 2) (Fin 2) ℝ

/--
The `3 × 3` grid of `2 × 2` real blocks.
This is a diagrammatic array used to index positions in later formulas.
-/
abbrev TwistorGrid := Matrix (Fin 3) (Fin 3) TwistorBlock

/--
Extracts the Twistor Position spinor block ($\omega$) from the grid.
Corresponds to Block (1,3).
-/
def twistorPosition (G : TwistorGrid) : TwistorBlock :=
  G 0 2

/--
Extracts the Twistor Momentum spinor block ($\pi$) from the grid.
Corresponds to Block (2,3).
-/
def twistorMomentum (G : TwistorGrid) : TwistorBlock :=
  G 1 2

/--
Extracts the Spacetime Coordinate block ($x$) from the grid.
Corresponds to Block (1,2).
-/
def spacetimeCoord (G : TwistorGrid) : TwistorBlock :=
  G 0 1

/--
The twistor incidence placeholder in block form.

This is only a local compatibility condition on the chosen block carriers.
The actual twistor projective geometry lives in the dedicated twistor files,
and the split-octonion projective geometry lives in the split-octonion files.

OPEN IDENTIFICATION:
No claim here identifies this equation with a proved twistor incidence theorem.
The predicate is an explicit finite block-level condition; a later owner must
provide the projective carrier and an incidence map before any geometric
interpretation is attached to it.

-- DEBT_KIND: OPEN_IDENTIFICATION
-/
def TwistorIncidence (G : TwistorGrid) : Prop :=
  twistorPosition G = spacetimeCoord G * twistorMomentum G

/-- The finite block predicate is exactly the corresponding entrywise matrix
equation.  This is a coordinate readout only; it does not add a projective
incidence interpretation. -/
theorem twistorIncidence_iff_entrywise (G : TwistorGrid) :
    TwistorIncidence G ↔
      ∀ i j : Fin 2,
        G 0 2 i j = ∑ k : Fin 2, G 0 1 i k * G 1 2 k j := by
  constructor
  · intro h i j
    have h' := congrArg (fun B : TwistorBlock => B i j) h
    simpa [TwistorIncidence, twistorPosition, spacetimeCoord, twistorMomentum,
      Matrix.mul_apply] using h'
  · intro h
    apply Matrix.ext
    intro i j
    simpa [TwistorIncidence, twistorPosition, spacetimeCoord, twistorMomentum,
      Matrix.mul_apply] using h i j

end InfoGeometry.Projective
