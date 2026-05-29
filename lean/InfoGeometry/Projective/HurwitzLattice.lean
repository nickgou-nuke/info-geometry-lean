import InfoGeometry.Projective.SplitQuaternionMatrix
import InfoGeometry.Projective.TwistorBlockGrid

/-!
# InfoGeometry.Projective.HurwitzLattice

This file defines the restriction of the continuous split-quaternion frame
to the discrete Hurwitz integral quaternions $\mathbb{H}_\mathbb{Z}$.

The Hurwitz integers act as a quantum checkerboard overlaying the split-hyperbolic space.
They discretize the twistor coordinates, meaning that the positions and momenta are
restricted to a lattice geometry.
-/

namespace InfoGeometry.Projective

/--
A Hurwitz integer requires coordinates to be either all integers
or all half-integers.

This restricts the continuous real degrees of freedom of the $2 \times 2$ blocks
to a discrete lattice.
-/
structure HurwitzInteger where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  is_hurwitz : (a.isInt ∧ b.isInt ∧ c.isInt ∧ d.isInt) ∨
               ((a * 2).isInt ∧ (b * 2).isInt ∧ (c * 2).isInt ∧ (d * 2).isInt ∧
                ¬a.isInt ∧ ¬b.isInt ∧ ¬c.isInt ∧ ¬d.isInt)

/--
Coordinate embedding of a Hurwitz integer into the `2 × 2` real block carrier.
This is a coordinate map only, not an algebra equivalence.
-/
noncomputable def hurwitzToTwistorBlock : HurwitzInteger → TwistorBlock :=
  fun h =>
    !![(h.a : ℝ), (h.b : ℝ);
       (h.c : ℝ), (h.d : ℝ)]

end InfoGeometry.Projective
