/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-!
# Real doubled Minkowski carrier to exterior-power Plücker coordinates

The four-real-coordinate Minkowski carrier is identified with the existing
real four-vector used by the native `Λ²`/Plücker owner. A pair of such vectors
therefore gives the owner's six Plücker coordinates and satisfies its Klein
quadric equation. This is a coordinate/exterior-power bridge; it does not
identify the Minkowski quadratic form with the Klein bilinear form.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealDoubledPluckerBridge

open InfoGeometry.Canonical.RealDoubledChiralKreinFrame
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.KleinQuadricPlucker

private def i4ToFin : I4 ≃ Fin 4 where
  toFun
    | .t => 0
    | .x => 1
    | .y => 2
    | .z => 3
  invFun
    | 0 => .t
    | 1 => .x
    | 2 => .y
    | _ => .z
  left_inv i := by cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

abbrev FierzVec4 := InfoGeometry.Canonical.FierzKleinFoundation.Vec4
abbrev KleinPlucker6 := InfoGeometry.Projective.KleinQuadricPlucker.Plucker6

/-- Real coordinate equivalence from the doubled Minkowski four-vector slot
to the `(+---)`-ordered real vector used by the Plücker owner. -/
def fourSpaceToKleinVec4 : FourSpace ≃ₗ[ℝ] FierzVec4 where
  toFun p i := p (i4ToFin i)
  invFun v := WithLp.toLp 2 (fun j => v (i4ToFin.symm j))
  left_inv p := by
    ext j
    fin_cases j <;> rfl
  right_inv v := by
    funext i
    simp
  map_add' p q := by
    funext i
    rfl
  map_smul' c p := by
    funext i
    rfl

/-- The decomposable Plücker bivector of two real doubled-Minkowski
four-vectors, in the existing six-coordinate chart. -/
def fourSpacePluckerLine (p q : FourSpace) : KleinPlucker6 ℝ :=
  InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.pluckerLine
    ⟨fourSpaceToKleinVec4 p I4.t, fourSpaceToKleinVec4 p I4.x,
      fourSpaceToKleinVec4 p I4.y, fourSpaceToKleinVec4 p I4.z⟩
    ⟨fourSpaceToKleinVec4 q I4.t, fourSpaceToKleinVec4 q I4.x,
      fourSpaceToKleinVec4 q I4.y, fourSpaceToKleinVec4 q I4.z⟩

/-- Every pair of real four-vectors maps to a decomposable bivector on the
Klein quadric. -/
theorem fourSpacePluckerLine_on_klein (p q : FourSpace) :
    InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ
      (fourSpacePluckerLine p q) = 0 := by
  exact InfoGeometry.Projective.KleinQuadricPlucker.Plucker6.kleinQ_pluckerLine _ _

/-- The real exterior-square readout of the four-space carrier into the
owner's six Plücker coordinates. -/
def fourSpaceExteriorPluckerMap :
    (⋀[ℝ]^2 FourSpace) →ₗ[ℝ] InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerExteriorMap.comp
    (exteriorPower.map 2 fourSpaceToKleinVec4.toLinearMap)

/-- On a simple exterior bivector the readout is precisely the six minors of
the corresponding real doubled-Minkowski vectors. -/
theorem fourSpaceExteriorPluckerMap_ιMulti (p q : FourSpace) :
    fourSpaceExteriorPluckerMap (exteriorPower.ιMulti ℝ 2 ![p, q]) =
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 p) (fourSpaceToKleinVec4 q) := by
  change InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerExteriorMap
      (exteriorPower.map 2 fourSpaceToKleinVec4.toLinearMap
        (exteriorPower.ιMulti ℝ 2 ![p, q])) = _
  rw [exteriorPower.map_apply_ιMulti]
  have hvec : (fourSpaceToKleinVec4.toLinearMap ∘ ![p, q]) =
      ![fourSpaceToKleinVec4 p, fourSpaceToKleinVec4 q] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec,
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerExteriorMap_ιMulti]

end InfoGeometry.Canonical.RealDoubledPluckerBridge
