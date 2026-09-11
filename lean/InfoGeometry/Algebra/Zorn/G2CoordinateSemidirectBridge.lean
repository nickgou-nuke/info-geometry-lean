import InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv
import InfoGeometry.Exceptional.G2ArtinRootPermutationLift

namespace InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

@[simp] theorem dihedralParameterMap_r (k : ZMod 6) :
    dihedralParameterMap (.r k) = (k, false) := by
  rfl

@[simp] theorem dihedralParameterMap_sr (k : ZMod 6) :
    dihedralParameterMap (.sr k) = (k, true) := by
  rfl

theorem coordinateWeylAction_rot_mul (k l : ZMod 6) :
    coordinateWeylAction (weylSemidirectMul (k, false) (l, false)) =
      coordinateWeylAction (k, false) * coordinateWeylAction (l, false) := by
  simp [coordinateWeylAction, weylSemidirectMul,
    G2CoordinateCoxeterRelations.coordinate_c_pow_zmod_add]

theorem coordinateWeylAction_rot_refl_mul (k l : ZMod 6) :
    coordinateWeylAction (weylSemidirectMul (k, false) (l, true)) =
      coordinateWeylAction (k, false) * coordinateWeylAction (l, true) := by
  simp [coordinateWeylAction, weylSemidirectMul]
  rw [coordinate_c_pow_zmod_sub]
  rw [← inv_pow, coordinate_s1_mul_c_pow]
  rw [← mul_assoc]
  rw [coordinate_s1_mul_c_pow]
  rw [mul_assoc, coordinate_s1_mul_c_inv_pow]
  have hcomm : Commute (cRoot ^ k.val) (cRoot⁻¹ ^ l.val) :=
    (Commute.refl cRoot).pow_left k.val |>.inv_right |>.pow_right l.val
  rw [← mul_assoc, hcomm.eq.symm, mul_assoc]

theorem coordinateWeylAction_refl_rot_mul (k l : ZMod 6) :
    coordinateWeylAction (weylSemidirectMul (k, true) (l, false)) =
      coordinateWeylAction (k, true) * coordinateWeylAction (l, false) := by
  simp [coordinateWeylAction, weylSemidirectMul,
    G2CoordinateCoxeterRelations.coordinate_c_pow_zmod_add]
  rw [← mul_assoc]

theorem coordinateWeylAction_refl_refl_mul (k l : ZMod 6) :
    coordinateWeylAction (weylSemidirectMul (k, true) (l, true)) =
      coordinateWeylAction (k, true) * coordinateWeylAction (l, true) := by
  simp [coordinateWeylAction, weylSemidirectMul]
  rw [coordinate_c_pow_zmod_sub]
  rw [← inv_pow, coordinate_s1_mul_c_pow]
  rw [← mul_assoc]
  simp [mul_assoc]
  rw [← inv_pow]
  have hs : s1Root * (s1Root * cRoot ^ l.val) = cRoot ^ l.val := by
    rw [← mul_assoc, ← pow_two, coordinate_s1_sq, one_mul]
  rw [hs]
  have hcomm : Commute (cRoot ^ l.val) (cRoot⁻¹ ^ k.val) :=
    (Commute.refl cRoot).pow_left l.val |>.inv_right |>.pow_right k.val
  exact hcomm.eq

theorem coordinateWeylAction_mul
    (p q : InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification.WeylG2) :
    coordinateWeylAction (weylSemidirectMul p q) =
      coordinateWeylAction p * coordinateWeylAction q := by
  rcases p with ⟨k, b⟩
  rcases q with ⟨l, d⟩
  cases b <;> cases d
  · exact coordinateWeylAction_rot_mul k l
  · exact coordinateWeylAction_rot_refl_mul k l
  · exact coordinateWeylAction_refl_rot_mul k l
  · exact coordinateWeylAction_refl_refl_mul k l

/-! The finite coordinate action is a genuine representation of the native
    dihedral carrier.  The parameter map is the existing Weyl normal-form
    equivalence; no second finite group is introduced here. -/

noncomputable def dihedralCoordinateHom : DihedralGroup 6 →*
    Equiv.Perm G2CoordinateRoot where
  toFun g := coordinateWeylAction (dihedralParameterMap g)
  map_one' := by
    rw [DihedralGroup.one_def]
    exact coordinateWeylAction_one
  map_mul' g h := by
    rw [dihedralParameterMap_mul, coordinateWeylAction_mul]

theorem dihedralCoordinateHom_apply
    (g : DihedralGroup 6) (x : G2CoordinateRoot) :
    dihedralCoordinateHom g x =
      coordinateWeylAction (dihedralParameterMap g) x := by
  rfl

def dihedralIndexNeg : DihedralGroup 6 → DihedralGroup 6
  | .r k => .r (-k)
  | .sr k => .sr (-k)

noncomputable def dihedralIndexNegHom : DihedralGroup 6 →* DihedralGroup 6 where
  toFun := dihedralIndexNeg
  map_one' := by rfl
  map_mul' := by
    intro g h
    cases g <;> cases h <;>
      simp only [dihedralIndexNeg, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
        DihedralGroup.sr_mul_sr]
    all_goals (congr 1; ring)

noncomputable def calibratedDihedralCoordinateHom : DihedralGroup 6 →*
    Equiv.Perm G2CoordinateRoot :=
  dihedralCoordinateHom.comp dihedralIndexNegHom

theorem calibratedDihedralCoordinateHom_apply
    (g : DihedralGroup 6) (x : G2CoordinateRoot) :
    calibratedDihedralCoordinateHom g x =
      dihedralCoordinateHom (dihedralIndexNegHom g) x := by
  rfl

@[simp] theorem calibratedDihedralCoordinateHom_sr_zero :
    calibratedDihedralCoordinateHom (.sr 0) = s1Root := by
  rfl

@[simp] theorem calibratedDihedralCoordinateHom_sr_one :
    calibratedDihedralCoordinateHom (.sr 1) = s2Root := by
  rw [calibratedDihedralCoordinateHom, MonoidHom.comp_apply]
  change coordinateWeylAction (5, true) = s2Root
  change s1Root * cRoot ^ 5 = s2Root
  have hc : cRoot ^ 5 = cRoot⁻¹ := by
    have h : cRoot ^ 5 * cRoot = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using cRoot_pow_six
    apply mul_right_cancel (b := cRoot)
    exact h.trans (by simp)
  rw [hc, ← InfoGeometry.Exceptional.G2ArtinRootLift.generator_product_eq_cRoot_inv]
  calc
    s1Root * (s1Root * s2Root) = (s1Root * s1Root) * s2Root := by
      rw [mul_assoc]
    _ = s2Root := by
      rw [← pow_two, s1Root_sq, one_mul]

end InfoGeometry.Algebra.Zorn.G2CoordinateSemidirectBridge
