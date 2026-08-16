import InfoGeometry.Algebra.FiveGradedTKK
import Mathlib.Algebra.Lie.Basic

/-!
# Lie antisymmetry for a five-graded carrier

`FiveGradedTKK` currently owns the five weights and coordinate decomposition,
but not a Lie bracket.  This file adds the smallest honest socket: five named
linear submodules inside an already existing mathlib Lie algebra.  The first
required law, antisymmetry, is therefore inherited from `LieRing` rather than
reintroduced as an unverified assumption.

No bracket-closure, direct-sum, TKK, Kantor, or structurable identity is claimed
in this owner.
-/

namespace InfoGeometry.Algebra.FiveGradedLieAntisymmetry

open InfoGeometry.Algebra.FiveGradedTKK

variable (R L : Type*) [CommRing R]
variable [LieRing L] [LieAlgebra R L]

/-- Five distinguished homogeneous submodules of an ambient Lie algebra.
Further owners may add closure and decomposition contracts without changing
the ambient bracket. -/
structure FiveGradedLieData where
  component : Weight5 → Submodule R L

namespace FiveGradedLieData

variable (G : FiveGradedLieData R L)

/-- Membership in one of the five declared homogeneous components. -/
def IsHomogeneous (w : Weight5) (x : L) : Prop :=
  x ∈ G.component w

/-- The ambient bracket on a five-graded carrier is antisymmetric.  The grade
membership hypotheses record the intended typed inputs; no closure conclusion
is asserted yet. -/
theorem lie_antisymmetry
    {u v : Weight5} {x y : L}
    (_hx : G.IsHomogeneous (R := R) (L := L) u x)
    (_hy : G.IsHomogeneous (R := R) (L := L) v y) :
    ⁅x, y⁆ = -⁅y, x⁆ := by
  exact (lie_skew x y).symm

/-- Self-brackets vanish, independently of the chosen homogeneous grade. -/
theorem lie_self_eq_zero
    {u : Weight5} {x : L}
    (_hx : G.IsHomogeneous (R := R) (L := L) u x) :
    ⁅x, x⁆ = 0 := by
  exact lie_self x

end FiveGradedLieData

end InfoGeometry.Algebra.FiveGradedLieAntisymmetry
