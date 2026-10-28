/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealPluckerCl55Reflection
import InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-!
# The real reflection on the literal exterior square

The real twistor pair is identified with the existing four-coordinate real
module. Its actual block rotation induces a Mathlib exterior-power map.
The universal property of that exterior power proves compatibility with the
existing Plücker readout on every bivector, including nondecomposable ones.
The native `Cl55` embedding and partial reflection then commute with this
actual exterior action. Only the underlying vector space of `Vec4` is used;
no preservation of its separately defined Minkowski pairing is asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorExteriorReflection

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.KleinQuadricPlucker
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Algebra.FiniteSpin
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.RealTwistorBlockInversion
open InfoGeometry.Twistor.RealPluckerCl55Reflection

abbrev ExteriorVector := InfoGeometry.Canonical.FierzKleinFoundation.Vec4
abbrev ExteriorCarrier := ⋀[ℝ]^2 ExteriorVector

/-- The existing real spinor pair and exterior owner's vector space agree linearly. -/
def twistorVectorEquiv : TwistorSpace ≃ₗ[ℝ] ExteriorVector where
  toFun z := fun
    | I4.t => z.1 0
    | I4.x => z.1 1
    | I4.y => z.2 0
    | I4.z => z.2 1
  invFun v := (![v I4.t, v I4.x], ![v I4.y, v I4.z])
  left_inv z := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv v := by funext i; cases i <;> rfl
  map_add' z w := by funext i; cases i <;> rfl
  map_smul' a z := by funext i; cases i <;> rfl

/-- Transport of the actual real block rotation, before taking the exterior power. -/
def vectorRotation : ExteriorVector ≃ₗ[ℝ] ExteriorVector :=
  twistorVectorEquiv.symm.trans (blockRotation.trans twistorVectorEquiv)

theorem twistorVectorEquiv_blockRotation (z : TwistorSpace) :
    twistorVectorEquiv (blockRotation z) = vectorRotation (twistorVectorEquiv z) := by
  simp [vectorRotation]

def exteriorRotation : Module.End ℝ ExteriorCarrier :=
  exteriorPower.map 2 vectorRotation.toLinearMap

theorem exteriorRotation_ιMulti (u v : ExteriorVector) :
    exteriorRotation (exteriorPower.ιMulti ℝ 2 ![u, v]) =
      exteriorPower.ιMulti ℝ 2 ![vectorRotation u, vectorRotation v] := by
  rw [exteriorRotation, exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The tuple adapter only connects the two existing coordinate readouts. -/
def asPlucker (c : Vec6R) : Plucker6 ℝ :=
  ⟨c 0, c 1, c 2, c 3, c 4, c 5⟩

theorem asPlucker_injective : Function.Injective asPlucker := by
  intro c d h
  have hc := congrArg
    (fun P : Plucker6 ℝ => ![P.p01, P.p02, P.p03, P.p12, P.p13, P.p23]) h
  funext i
  have hi := congrFun hc i
  fin_cases i <;> simpa [asPlucker] using hi

def coordinateRotation : Vec6R →ₗ[ℝ] Vec6R where
  toFun c := ![c 5, c 1, c 3, c 2, c 4, c 0]
  map_add' c d := by funext i; fin_cases i <;> rfl
  map_smul' a c := by funext i; fin_cases i <;> rfl

theorem asPlucker_coordinateRotation (c : Vec6R) :
    asPlucker (coordinateRotation c) = pluckerRotation (asPlucker c) := rfl

theorem coordinateRotation_involutive (c : Vec6R) :
    coordinateRotation (coordinateRotation c) = c := by
  funext i
  fin_cases i <;> rfl

theorem asPlucker_pluckerCoords (z w : TwistorSpace) :
    asPlucker (pluckerCoords (twistorVectorEquiv z) (twistorVectorEquiv w)) =
      twistorPlucker z w := by
  apply Plucker6.ext <;> rfl

/-- Reuse the proved real twistor-minor intertwiner through the explicit adapter. -/
theorem pluckerCoords_vectorRotation (u v : ExteriorVector) :
    pluckerCoords (vectorRotation u) (vectorRotation v) =
      coordinateRotation (pluckerCoords u v) := by
  apply asPlucker_injective
  rw [asPlucker_coordinateRotation]
  have h := twistorPlucker_blockRotation
    (twistorVectorEquiv.symm u) (twistorVectorEquiv.symm v)
  simpa only [← asPlucker_pluckerCoords, twistorVectorEquiv_blockRotation,
    LinearEquiv.apply_symm_apply] using h

/-- Universal-property proof on the full exterior power, not only simple wedges. -/
theorem pluckerExteriorMap_rotation_linear :
    pluckerExteriorMap.comp exteriorRotation =
      coordinateRotation.comp pluckerExteriorMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro m
  change pluckerExteriorMap (exteriorRotation (exteriorPower.ιMulti ℝ 2 m)) =
    coordinateRotation (pluckerExteriorMap (exteriorPower.ιMulti ℝ 2 m))
  have hm : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hm, exteriorRotation_ιMulti, pluckerExteriorMap_ιMulti,
    pluckerExteriorMap_ιMulti]
  exact pluckerCoords_vectorRotation _ _

theorem pluckerExteriorMap_rotation (X : ExteriorCarrier) :
    pluckerExteriorMap (exteriorRotation X) =
      coordinateRotation (pluckerExteriorMap X) :=
  LinearMap.congr_fun pluckerExteriorMap_rotation_linear X

theorem exteriorRotation_involutive (X : ExteriorCarrier) :
    exteriorRotation (exteriorRotation X) = X := by
  apply pluckerExteriorLinearEquiv.injective
  change pluckerExteriorMap (exteriorRotation (exteriorRotation X)) = pluckerExteriorMap X
  rw [pluckerExteriorMap_rotation, pluckerExteriorMap_rotation,
    coordinateRotation_involutive]

/-- The concrete native embedding is a genuine linear map on the six-coordinate module. -/
def nativeCoordinates : Vec6R →ₗ[ℝ] V55 where
  toFun c := pluckerToV55 (asPlucker c)
  map_add' c d := by
    change pluckerToV55 (Plucker6.add (asPlucker c) (asPlucker d)) = _
    exact pluckerToV55_add _ _
  map_smul' a c := by
    change pluckerToV55 (Plucker6.scale a (asPlucker c)) = _
    exact pluckerToV55_scale _ _

theorem nativeCoordinates_injective : Function.Injective nativeCoordinates :=
  pluckerToV55_injective.comp asPlucker_injective

/-- The literal exterior-power owner maps into the existing native quadratic carrier. -/
def nativeExteriorEmbedding : ExteriorCarrier →ₗ[ℝ] V55 :=
  nativeCoordinates.comp pluckerExteriorMap

theorem nativeExteriorEmbedding_injective : Function.Injective nativeExteriorEmbedding :=
  nativeCoordinates_injective.comp pluckerExteriorLinearEquiv.injective

theorem nativeExteriorEmbedding_ιMulti (z w : TwistorSpace) :
    nativeExteriorEmbedding
        (exteriorPower.ιMulti ℝ 2 ![twistorVectorEquiv z, twistorVectorEquiv w]) =
      pluckerToV55 (twistorPlucker z w) := by
  change pluckerToV55 (asPlucker (pluckerExteriorMap _)) = _
  rw [pluckerExteriorMap_ιMulti, asPlucker_pluckerCoords]

/-- Compatibility with the already-owned quadratic form on the actual exterior square. -/
theorem nativeExteriorEmbedding_quadratic (X : ExteriorCarrier) :
    InfoGeometry.Clifford.Clifford55.Q55 (nativeExteriorEmbedding X) =
      exteriorKleinForm X := by
  change InfoGeometry.Clifford.Clifford55.Q55
    (pluckerToV55 (asPlucker (pluckerExteriorMap X))) = _
  rw [nativeQ55_pluckerToV55]
  rfl

theorem nativeCoordinates_rotation (c : Vec6R) :
    partialReflection (nativeCoordinates c) = nativeCoordinates (coordinateRotation c) := by
  change partialReflection (pluckerToV55 (asPlucker c)) =
    pluckerToV55 (asPlucker (coordinateRotation c))
  rw [partialReflection_pluckerToV55, asPlucker_coordinateRotation]

/-- The native partial reflection is intertwined on every exterior two-vector. -/
theorem nativeExteriorEmbedding_rotation (X : ExteriorCarrier) :
    partialReflection (nativeExteriorEmbedding X) =
      nativeExteriorEmbedding (exteriorRotation X) := by
  change partialReflection (nativeCoordinates (pluckerExteriorMap X)) =
    nativeCoordinates (pluckerExteriorMap (exteriorRotation X))
  rw [nativeCoordinates_rotation, pluckerExteriorMap_rotation]

def cliffordExteriorEmbedding : ExteriorCarrier →ₗ[ℝ] Cl55 :=
  ι55.comp nativeExteriorEmbedding

theorem cliffordExteriorEmbedding_injective : Function.Injective cliffordExteriorEmbedding :=
  ι55_injective.comp nativeExteriorEmbedding_injective

/-- The actual Clifford algebra automorphism commutes with the literal exterior action. -/
theorem cliffordExteriorEmbedding_rotation (X : ExteriorCarrier) :
    partialReflectionAlg (cliffordExteriorEmbedding X) =
      cliffordExteriorEmbedding (exteriorRotation X) := by
  change partialReflectionAlg (ι55 (nativeExteriorEmbedding X)) =
    ι55 (nativeExteriorEmbedding (exteriorRotation X))
  rw [partialReflectionAlg_apply_ι, nativeExteriorEmbedding_rotation]

end InfoGeometry.Twistor.RealTwistorExteriorReflection
