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
abbrev HurwitzInteger :=
  {data : ℚ × (ℚ × (ℚ × ℚ)) //
    (data.1.isInt ∧ data.2.1.isInt ∧ data.2.2.1.isInt ∧ data.2.2.2.isInt) ∨
      ((data.1 * 2).isInt ∧ (data.2.1 * 2).isInt ∧
       (data.2.2.1 * 2).isInt ∧ (data.2.2.2 * 2).isInt ∧
       ¬data.1.isInt ∧ ¬data.2.1.isInt ∧
       ¬data.2.2.1.isInt ∧ ¬data.2.2.2.isInt)}

namespace HurwitzInteger

abbrev a (h : HurwitzInteger) : ℚ := h.1.1
abbrev b (h : HurwitzInteger) : ℚ := h.1.2.1
abbrev c (h : HurwitzInteger) : ℚ := h.1.2.2.1
abbrev d (h : HurwitzInteger) : ℚ := h.1.2.2.2
abbrev is_hurwitz (h : HurwitzInteger) := h.2

end HurwitzInteger

/--
HONEST THEOREM DEBT:
The exact mapping of the discrete `HurwitzInteger` lattice into the $2 \times 2$
`TwistorBlock` real matrices is deferred.

-- DEBT_KIND: SORRY
-/
noncomputable def hurwitzToTwistorBlock : HurwitzInteger → TwistorBlock :=
  fun h =>
    !![(h.a : ℝ), (h.b : ℝ);
       (h.c : ℝ), (h.d : ℝ)]

end InfoGeometry.Projective
