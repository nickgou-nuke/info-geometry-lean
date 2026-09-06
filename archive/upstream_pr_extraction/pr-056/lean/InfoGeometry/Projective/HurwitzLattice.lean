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

/-- The coordinate injection of a Hurwitz lattice point into a real twistor
    block.  The integrality predicate remains on the source subtype; this
    theorem only records that the real matrix readout loses no coordinates. -/
noncomputable def hurwitzToTwistorBlock : HurwitzInteger → TwistorBlock :=
  fun h =>
    !![(h.a : ℝ), (h.b : ℝ);
       (h.c : ℝ), (h.d : ℝ)]

theorem hurwitzToTwistorBlock_injective :
    Function.Injective hurwitzToTwistorBlock := by
  rintro ⟨⟨a, b, c, d⟩, ha⟩ ⟨⟨a', b', c', d'⟩, ha'⟩ h
  apply Subtype.ext
  have h00 := congrArg (fun M : TwistorBlock => M 0 0) h
  have h01 := congrArg (fun M : TwistorBlock => M 0 1) h
  have h10 := congrArg (fun M : TwistorBlock => M 1 0) h
  have h11 := congrArg (fun M : TwistorBlock => M 1 1) h
  norm_num [hurwitzToTwistorBlock] at h00 h01 h10 h11
  exact Prod.ext h00 (Prod.ext h01 (Prod.ext h10 h11))

end InfoGeometry.Projective
