/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Projective.ExteriorKleinOperatorAction

/-!
# Noncommuting exterior actions and a four-coordinate sector obstruction

The shears and spatial quarter turn act on the actual four-vector module.
Their induced actions are the native exterior-square construction. The sector
counterexample concerns `p02 = p12 = 0`, not all four-dimensional models.
-/

noncomputable section

namespace InfoGeometry.Projective.ExteriorKleinOperatorAction

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Projective.ExteriorPowerPluckerBridge

/-- The shear `I + E01` on real four-vectors. -/
def shear01 : Module.End ℝ Vec4 where
  toFun u i := match i with
    | I4.t => u I4.t + u I4.x
    | I4.x => u I4.x
    | I4.y => u I4.y
    | I4.z => u I4.z
  map_add' u v := by
    funext i
    cases i <;> simp only [Pi.add_apply] <;> ring
  map_smul' a u := by
    funext i
    cases i <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

/-- The shear `I + E12` on real four-vectors. -/
def shear12 : Module.End ℝ Vec4 where
  toFun u i := match i with
    | I4.t => u I4.t
    | I4.x => u I4.x + u I4.y
    | I4.y => u I4.y
    | I4.z => u I4.z
  map_add' u v := by
    funext i
    cases i <;> simp only [Pi.add_apply] <;> ring
  map_smul' a u := by
    funext i
    cases i <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem shears_noncommute : shear01 * shear12 ≠ shear12 * shear01 := by
  intro h
  have h' := congrArg (fun A : Module.End ℝ Vec4 => A (i4Basis I4.y) I4.t) h
  change (shear01 (shear12 (i4Basis I4.y))) I4.t =
    (shear12 (shear01 (i4Basis I4.y))) I4.t at h'
  norm_num [shear01, shear12, i4Basis] at h'

/-- A nonzero coordinate of the commutator on an explicit simple bivector. -/
theorem induced_shear_commutator_p03 :
    ((bivectorAction shear01 (bivectorAction shear12
        (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z)))) -
      (bivectorAction shear12 (bivectorAction shear01
        (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z))))).p03 = 1 := by
  rw [bivectorAction_wedge, bivectorAction_wedge,
    bivectorAction_wedge, bivectorAction_wedge]
  change (wedgeVec4 (shear01 (shear12 (i4Basis I4.y)))
      (shear01 (shear12 (i4Basis I4.z)))).p03 -
    (wedgeVec4 (shear12 (shear01 (i4Basis I4.y)))
      (shear12 (shear01 (i4Basis I4.z)))).p03 = 1
  norm_num [wedgeVec4, shear01, shear12, i4Basis]

theorem induced_shears_noncommute :
    bivectorAction shear01 * bivectorAction shear12 ≠
      bivectorAction shear12 * bivectorAction shear01 := by
  intro h
  have h' := congrArg (fun A : Module.End ℝ Bivector4 =>
    (A (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z))).p03) h
  have hw := induced_shear_commutator_p03
  change (bivectorAction shear01 (bivectorAction shear12
      (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z)))).p03 -
    (bivectorAction shear12 (bivectorAction shear01
      (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z)))).p03 = 1 at hw
  change (bivectorAction shear01 (bivectorAction shear12
      (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z)))).p03 =
    (bivectorAction shear12 (bivectorAction shear01
      (wedgeVec4 (i4Basis I4.y) (i4Basis I4.z)))).p03 at h'
  rw [h', sub_self] at hw
  norm_num at hw

/-- A test slice for the paper's four-coordinate readout; the paper leaves the
constraints on the two omitted coordinates unresolved. -/
def FourCoordinateSector (P : Bivector4) : Prop := P.p02 = 0 ∧ P.p12 = 0

theorem kleinForm_fourCoordinateSector (P : Bivector4) (hP : FourCoordinateSector P) :
    kleinForm P = P.p01 * P.p23 := by
  simp [kleinForm, hP.1, hP.2]

theorem fourCoordinateSector_null_iff (P : Bivector4) (hP : FourCoordinateSector P) :
    kleinForm P = 0 ↔ P.p01 = 0 ∨ P.p23 = 0 := by
  rw [kleinForm_fourCoordinateSector P hP, mul_eq_zero]

/-- Spatial quarter turn `(t,x,y,z) ↦ (t,x,z,-y)`. -/
def quarterTurn : Module.End ℝ Vec4 where
  toFun u i := match i with
    | I4.t => u I4.t
    | I4.x => u I4.x
    | I4.y => u I4.z
    | I4.z => -u I4.y
  map_add' u v := by
    funext i
    cases i <;> simp only [Pi.add_apply] <;> ring
  map_smul' a u := by
    funext i
    cases i <;> simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

theorem quarterTurn_preserves_minkowski (u v : Vec4) :
    minkowskiDot (quarterTurn u) (quarterTurn v) = minkowskiDot u v := by
  simp only [minkowskiDot, quarterTurn, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem wedge_tz_in_fourCoordinateSector :
    FourCoordinateSector (wedgeVec4 (i4Basis I4.t) (i4Basis I4.z)) := by
  norm_num [FourCoordinateSector, wedgeVec4, i4Basis]

theorem quarterTurn_exits_fourCoordinateSector :
    ¬ FourCoordinateSector (bivectorAction quarterTurn
      (wedgeVec4 (i4Basis I4.t) (i4Basis I4.z))) := by
  rw [bivectorAction_wedge]
  norm_num [FourCoordinateSector, wedgeVec4, quarterTurn, i4Basis]

end InfoGeometry.Projective.ExteriorKleinOperatorAction
