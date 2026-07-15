import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Algebra.Grothendieck

/-!
# Bost--Connes additive Grothendieck shadow

This file maps Bost--Connes range projections into the group completion of the
underlying additive monoid of the operator ring.  This is an algebraic shadow,
not operator-algebraic `K₀`: no stable-projection monoid, Murray--von Neumann
equivalence, or C*-completion is constructed here.
-/

namespace BostConnesKTheory

open InfoGeometry.Arithmetic.BostConnesSystem
open BostConnesKMS

variable {Op : Type*} [Ring Op] [StarRing Op]
variable (C : BostConnesCuntzSystem Op)

/-- The correct KMS range projectors for the Bost-Connes system. -/
def kmsProjector (n : ℕ+) : Op :=
  S C n * star (S C n)

/-- The additive Grothendieck class of a Bost--Connes range projection. -/
def projectorGrothendieckClass (n : ℕ+) : Grothendieck Op :=
  grothendieckMap Op (kmsProjector C n)

/--
Additive inclusion--exclusion in the Grothendieck completion.

This theorem is purely additive.  In particular, it does not assert that
`eₙ + eₘ - eₙeₘ` is a projection or that these classes are topological `K₀`
classes.
-/
theorem projectorGrothendieckClass_inclusion_exclusion (n m : ℕ+) :
    projectorGrothendieckClass C n + projectorGrothendieckClass C m =
      grothendieckMap Op
          (kmsProjector C n + kmsProjector C m - kmsProjector C n * kmsProjector C m) +
        grothendieckMap Op (kmsProjector C n * kmsProjector C m) := by
  dsimp [projectorGrothendieckClass]
  rw [← map_add, ← map_add]
  congr 1
  abel

end BostConnesKTheory
