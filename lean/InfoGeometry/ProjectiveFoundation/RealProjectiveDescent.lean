/- 
InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean

Core quotient descent for the real projective geometry.
No complex imports.
-/

import Mathlib.Algebra.Group.Action.End
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.GroupTheory.QuotientGroup.Defs
import InfoGeometry.Canonical.PSLDescent
import InfoGeometry.ProjectiveFoundation
import InfoGeometry.Geometry.RealMoebiusAction

noncomputable section

open scoped MatrixGroups
open InfoGeometry.Geometry
open InfoGeometry.Canonical.PSLDescent

namespace InfoGeometry.ProjectiveFoundation

/--
The center of `G` acts trivially on `X`.

This is the exact hypothesis needed to descend a `G`-action on `X` to an
action of `G ⧸ Subgroup.center G`.
-/
class CenterActsTrivially
    (G X : Type*) [Group G] [MulAction G X] : Prop where
  center_smul_eq :
    ∀ z : G, z ∈ Subgroup.center G → ∀ x : X, z • x = x

namespace CenterActsTrivially

variable
    {G X : Type*}
    [Group G] [MulAction G X]
    [CenterActsTrivially G X]

/--
The action homomorphism `G →* Equiv.Perm X` descends through the quotient
by the center once the center acts trivially.
-/
def centerQuotientPermHom :
    G ⧸ Subgroup.center G →* Equiv.Perm X :=
  QuotientGroup.lift
    (Subgroup.center G)
    (MulAction.toPermHom G X)
    (by
      intro z hz
      ext x
      exact CenterActsTrivially.center_smul_eq z hz x)

/--
The induced action of `G ⧸ center(G)` on `X`.
-/
def centerQuotientMulAction :
    MulAction (G ⧸ Subgroup.center G) X :=
  letI : MulAction (Equiv.Perm X) X := Equiv.Perm.applyMulAction X
  MulAction.compHom X (centerQuotientPermHom (G := G) (X := X))

end CenterActsTrivially

/--
The real projective action is obtained from the real `SL(2,ℝ)` action once
its center-triviality has been proved in the real coordinate model.
-/
instance instPSL2RRealAction
    [MulAction InfoGeometry.Geometry.SL2R RealUpperHalfPlane]
    [CenterActsTrivially InfoGeometry.Geometry.SL2R RealUpperHalfPlane] :
    MulAction InfoGeometry.Canonical.PSLDescent.PSL2R RealUpperHalfPlane :=
  CenterActsTrivially.centerQuotientMulAction
    (G := InfoGeometry.Geometry.SL2R) (X := RealUpperHalfPlane)

/--
The arithmetic real projective action is the corresponding descent for
`SL(2,ℤ)`.
-/
instance instPSL2ZRealAction
    [MulAction InfoGeometry.Geometry.SL2Z RealUpperHalfPlane]
    [CenterActsTrivially InfoGeometry.Geometry.SL2Z RealUpperHalfPlane] :
    MulAction InfoGeometry.Canonical.PSLDescent.PSL2Z RealUpperHalfPlane :=
  CenterActsTrivially.centerQuotientMulAction
    (G := InfoGeometry.Geometry.SL2Z) (X := RealUpperHalfPlane)

end InfoGeometry.ProjectiveFoundation
