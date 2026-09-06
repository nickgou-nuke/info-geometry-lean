/-!
# Projective compactification obstruction for the D=4 quadric arrangement

The translated affine space is `A^4_a × A^4_b`.  A natural compactification is
`P^4_A × P^4_B`, with homogeneous coordinates

`A=[A0:A1:A2:A3:A4]`, `B=[B0:B1:B2:B3:B4]`.

The affine equations homogenize to:

* `QA  = Σ Ai^2`;
* `QB  = Σ Bi^2`;
* `QAB = Σ (Ai B0 - Bi A0)^2`.

This file records the obstruction to applying Dupont's theorem directly:
these projective closures are singular, so one needs a blow-up/resolution
layer before claiming a hypersurface arrangement in Dupont's sense.
-/

noncomputable section

namespace NonIsoConf3QuadricCompactification

/-- Labels for the natural compactification hypersurfaces. -/
inductive CompactDivisor where
  | boundaryA
  | boundaryB
  | quadricA
  | quadricB
  | quadricDifference
  deriving DecidableEq, Repr, Inhabited

open CompactDivisor

/-- The natural projective closure is not directly ready for Dupont's
hypersurface-arrangement theorem. -/
def notDirectDupontReady (singular : CompactDivisor → Prop) : Prop :=
  singular quadricA ∨
  singular quadricB ∨
  singular quadricDifference

theorem compactification_obstruction_synthesis
    (singular : CompactDivisor → Prop)
    (hA : singular quadricA) :
    notDirectDupontReady singular := by
  exact Or.inl hA
end NonIsoConf3QuadricCompactification

end noncomputable section
