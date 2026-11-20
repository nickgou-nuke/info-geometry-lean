/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RealDoubledChiralKreinFrame
import InfoGeometry.Canonical.RealSolderingWeylKreinBridge
import InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift
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
open InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift

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

/-! ### The three-mode real exterior carrier inside spatial Minkowski bivectors

The CAR/Fock carrier has three real modes, whereas the Klein chart is
`Λ² ℝ⁴`. The map below inserts those three coordinates into the spatial
`x,y,z` hyperplane of `FourSpace`. The proved coordinate identities below
cover simple mode pairs; a theorem for every element of the exterior square
is intentionally not claimed here. -/

abbrev ThreeModeSpace := InfoGeometry.Algebra.FiniteSpin.Vec3R

/-- Insert the three CAR modes into the spatial coordinates of the doubled
Minkowski four-space, with zero time coordinate. -/
def threeModeToSpatialFourSpace : ThreeModeSpace →ₗ[ℝ] FourSpace where
  toFun v := WithLp.toLp 2 (fun j : Fin 4 =>
    if j.val = 0 then 0 else v ⟨j.val - 1, by omega⟩)
  map_add' v w := by
    ext j
    fin_cases j <;> simp
  map_smul' r v := by
    ext j
    fin_cases j <;> simp

/-- The spatial insertion is injective, so it realizes the three-mode space
as an actual three-dimensional subspace of `FourSpace`. -/
theorem threeModeToSpatialFourSpace_injective :
    Function.Injective threeModeToSpatialFourSpace := by
  intro u v huv
  funext i
  have h := congrArg
    (fun p : FourSpace => (WithLp.ofLp p) i.succ) huv
  simpa [threeModeToSpatialFourSpace] using h

/-- The inserted three-mode vectors have zero time component. -/
theorem threeModeToSpatialFourSpace_time (v : ThreeModeSpace) :
    (WithLp.ofLp (threeModeToSpatialFourSpace v)) 0 = 0 := by
  simp [threeModeToSpatialFourSpace]

/-- The induced exterior-square map from the three real Fock modes into
`Λ² FourSpace`, followed by the repository's existing six-coordinate
Plücker readout. -/
def threeModeExteriorPluckerMap :
    (⋀[ℝ]^2 ThreeModeSpace) →ₗ[ℝ] InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  fourSpaceExteriorPluckerMap.comp
    (exteriorPower.map 2 threeModeToSpatialFourSpace)

/-- On simple mode bivectors, the new map is exactly the six Plücker minors
of the corresponding spatially embedded four-vectors. -/
theorem threeModeExteriorPluckerMap_ιMulti (u v : ThreeModeSpace) :
    threeModeExteriorPluckerMap (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) := by
  change fourSpaceExteriorPluckerMap
      (exteriorPower.map 2 threeModeToSpatialFourSpace
        (exteriorPower.ιMulti ℝ 2 ![u, v])) = _
  rw [exteriorPower.map_apply_ιMulti]
  exact fourSpaceExteriorPluckerMap_ιMulti
    (threeModeToSpatialFourSpace u) (threeModeToSpatialFourSpace v)

/-- Every embedded pair of CAR mode vectors satisfies the Klein equation.
The theorem is stated on coordinates, so it also covers the zero bivector. -/
theorem threeModePair_plucker_on_klein (u v : ThreeModeSpace) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 0 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 5 -
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 1 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 4 +
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 2 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
        (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v)) 3 = 0 := by
  exact InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords_on_klein _ _

/-- The simple Plücker bivectors generated by two three-mode vectors have no
time-space components. -/
theorem threeModePair_temporalPlucker_zero (u v : ThreeModeSpace) :
    (InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v))) 0 = 0 ∧
    (InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v))) 1 = 0 ∧
    (InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace u))
      (fourSpaceToKleinVec4 (threeModeToSpatialFourSpace v))) 2 = 0 := by
  simp [InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords,
    threeModeToSpatialFourSpace, fourSpaceToKleinVec4, i4ToFin]

/-- Concrete Plücker/Klein connection for the circular CAR basis modes. -/
theorem fockModePair_plucker_coordinates (i j : Fin 3) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) =
      ![0, 0, 0,
        (if i.val = 0 ∧ j.val = 1 then (1 : ℝ) else 0) -
          (if i.val = 1 ∧ j.val = 0 then (1 : ℝ) else 0),
        (if i.val = 0 ∧ j.val = 2 then (1 : ℝ) else 0) -
          (if i.val = 2 ∧ j.val = 0 then (1 : ℝ) else 0),
        (if i.val = 1 ∧ j.val = 2 then (1 : ℝ) else 0) -
          (if i.val = 2 ∧ j.val = 1 then (1 : ℝ) else 0)] := by
  funext k
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords,
      modeVector, threeModeToSpatialFourSpace, fourSpaceToKleinVec4, i4ToFin]

/-- Concrete Plücker/Klein connection for the circular CAR basis modes. -/
theorem fockModePair_plucker_on_klein (i j : Fin 3) :
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 0 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 5 -
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 1 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 4 +
    InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 2 *
      InfoGeometry.Projective.ExteriorPowerPluckerBridge.pluckerCoords
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector i)))
        (fourSpaceToKleinVec4
          (threeModeToSpatialFourSpace (modeVector j))) 3 = 0 :=
  threeModePair_plucker_on_klein (modeVector i) (modeVector j)

end InfoGeometry.Canonical.RealDoubledPluckerBridge
