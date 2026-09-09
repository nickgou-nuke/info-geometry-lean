import Mathlib
import InfoGeometry.Geometry.KleinFourTag
import InfoGeometry.Topology.V4RootSystem

namespace InfoGeometry.Canonical.KleinFourTagRootNormalization

open InfoGeometry.Geometry.KleinFourTag
open InfoGeometry.Topology.V4RootSystem

abbrev V4Add := InfoGeometry.Geometry.KleinFourTag.Tag
abbrev V4 := Multiplicative V4Add

def v4RootMap : V4 → V4Group
  | (0, 0) => V4Group.I
  | (1, 0) => V4Group.W1
  | (0, 1) => V4Group.W2
  | (1, 1) => V4Group.W12
  | _ => V4Group.I

@[simp] theorem v4RootMap_id :
    v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id) =
      V4Group.I := by
  rfl

@[simp] theorem v4RootMap_P :
    v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P) =
      V4Group.W1 := by
  rfl

@[simp] theorem v4RootMap_T :
    v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T) =
      V4Group.W2 := by
  rfl

@[simp] theorem v4RootMap_PT :
    v4RootMap (Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT) =
      V4Group.W12 := by
  rfl

theorem v4RootMap_mul (g h : V4) :
    v4RootMap (g * h) = v4RootMap g * v4RootMap h := by
  fin_cases g <;> fin_cases h <;> decide

def v4RootHom : V4 →* V4Group where
  toFun := v4RootMap
  map_one' := v4RootMap_id
  map_mul' := v4RootMap_mul

noncomputable def v4RootEquiv : V4 ≃* V4Group := by
  refine MulEquiv.ofBijective v4RootHom ?_
  constructor
  · intro g h hgh
    fin_cases g <;> fin_cases h <;>
      simp_all [v4RootHom, v4RootMap, Multiplicative.ofAdd]
  · intro g
    cases g with
    | I => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.id, v4RootMap_id⟩
    | W1 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.P, v4RootMap_P⟩
    | W2 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.T, v4RootMap_T⟩
    | W12 => exact ⟨Multiplicative.ofAdd InfoGeometry.Geometry.KleinFourTag.PT, v4RootMap_PT⟩

end InfoGeometry.Canonical.KleinFourTagRootNormalization
