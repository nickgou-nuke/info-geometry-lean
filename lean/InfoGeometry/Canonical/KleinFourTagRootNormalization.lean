import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Geometry.KleinFourTag
import InfoGeometry.Topology.V4RootSystem

namespace InfoGeometry.Canonical.KleinFourTagRootNormalization

open InfoGeometry.Geometry.KleinFourTag
open InfoGeometry.Topology.V4RootSystem

abbrev V4Add := InfoGeometry.Geometry.KleinFourTag.Tag
abbrev V4 := Multiplicative V4Add

def v4RootMap (g : V4) : V4Group :=
  let tag := g.toAdd
  if tag = InfoGeometry.Geometry.KleinFourTag.id then V4Group.I
  else if tag = InfoGeometry.Geometry.KleinFourTag.P then V4Group.W1
  else if tag = InfoGeometry.Geometry.KleinFourTag.T then V4Group.W2
  else V4Group.W12

@[simp] theorem v4RootMap_id :
    v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id) =
      V4Group.I := by
  norm_num [v4RootMap, InfoGeometry.Geometry.KleinFourTag.id, toAdd_ofAdd]

@[simp] theorem v4RootMap_P :
      v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
      V4Group.W1 := by
  norm_num [v4RootMap, InfoGeometry.Geometry.KleinFourTag.id,
    InfoGeometry.Geometry.KleinFourTag.P, InfoGeometry.Geometry.KleinFourTag.T,
    toAdd_ofAdd]

@[simp] theorem v4RootMap_T :
      v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
      V4Group.W2 := by
  norm_num [v4RootMap, InfoGeometry.Geometry.KleinFourTag.id,
    InfoGeometry.Geometry.KleinFourTag.P, InfoGeometry.Geometry.KleinFourTag.T,
    toAdd_ofAdd]

@[simp] theorem v4RootMap_PT :
      v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
      V4Group.W12 := by
  norm_num [v4RootMap, InfoGeometry.Geometry.KleinFourTag.id,
    InfoGeometry.Geometry.KleinFourTag.P, InfoGeometry.Geometry.KleinFourTag.T,
    InfoGeometry.Geometry.KleinFourTag.PT, toAdd_ofAdd]

theorem v4RootMap_mul (g h : V4) :
    v4RootMap (g * h) = v4RootMap g * v4RootMap h := by
  fin_cases g <;> fin_cases h <;>
    decide

def v4RootMapInv : V4Group → V4
  | .I => Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id
  | .W1 => Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P
  | .W2 => Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T
  | .W12 => Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT

@[simp] theorem v4RootMapInv_left (g : V4) : v4RootMapInv (v4RootMap g) = g := by
  fin_cases g <;> decide

def v4RootHom : V4 →* V4Group where
  toFun := v4RootMap
  map_one' := by decide
  map_mul' := v4RootMap_mul

noncomputable def v4RootEquiv : V4 ≃* V4Group := by
  refine MulEquiv.ofBijective v4RootHom ?_
  constructor
  · intro g h hgh
    have h' := congrArg v4RootMapInv hgh
    change v4RootMapInv (v4RootMap g) = v4RootMapInv (v4RootMap h) at h'
    simpa only [v4RootMapInv_left] using h'
  · intro g
    cases g with
    | I => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id, v4RootMap_id⟩
    | W1 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P, v4RootMap_P⟩
    | W2 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T, v4RootMap_T⟩
    | W12 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT, v4RootMap_PT⟩

end InfoGeometry.Canonical.KleinFourTagRootNormalization
