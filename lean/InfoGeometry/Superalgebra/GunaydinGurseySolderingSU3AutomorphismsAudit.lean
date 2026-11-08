/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.GunaydinGurseySolderingSU3Automorphisms

/-!
# Одит на Раздел 128: Заваръчна Форма на Гюнайдън–Гюрсей и Изплуване на SU(3)_c / sl(3)

Конкретни целочислени (`ℤ`) проверки с `decide` за заваръчната форма,
дефекта на Лайбниц при векторното произведение и безследовите глуонни деривации.
-/

namespace InfoGeometry.Superalgebra.GunaydinGurseySU3Audit

open InfoGeometry.Superalgebra.GunaydinGurseySU3

def gluonLambdaInt : Mat3 ℤ := ⟨2, 1, -1, 3, -5, 2, 0, 4, 3⟩
def vecAInt : ColorVec3 ℤ := ⟨1, -2, 3⟩
def vecBInt : ColorVec3 ℤ := ⟨4, 0, -1⟩
def vecCInt : ColorVec3 ℤ := ⟨2, 5, 1⟩

theorem audit_soldering_map_int :
    SplitOctonion.mul SplitOctonion.ggU0 (SplitOctonion.complexVecI vecAInt) =
      SplitOctonion.ggQuark vecAInt ∧
    SplitOctonion.mul SplitOctonion.ggU0Star (SplitOctonion.complexVecI vecAInt) =
      SplitOctonion.neg (SplitOctonion.ggAntiquark vecAInt) := by
  decide

theorem audit_contragredient_dot_invariance_int :
    ColorVec3.dot (Mat3.mulVec gluonLambdaInt vecAInt) vecBInt +
      ColorVec3.dot vecAInt (ColorVec3.neg (Mat3.mulVec (Mat3.transpose gluonLambdaInt) vecBInt)) = 0 := by
  decide

theorem audit_cross_product_leibniz_defect_int :
    ColorVec3.add
      (ColorVec3.add (ColorVec3.cross (Mat3.mulVec gluonLambdaInt vecAInt) vecBInt)
                     (ColorVec3.cross vecAInt (Mat3.mulVec gluonLambdaInt vecBInt)))
      (Mat3.mulVec (Mat3.transpose gluonLambdaInt) (ColorVec3.cross vecAInt vecBInt)) =
    ColorVec3.smul (Mat3.trace gluonLambdaInt) (ColorVec3.cross vecAInt vecBInt) := by
  decide

theorem audit_baryon_det3_traceless_invariance_int :
    Mat3.trace gluonLambdaInt = 0 ∧
    ColorVec3.det3 (Mat3.mulVec gluonLambdaInt vecAInt) vecBInt vecCInt +
    ColorVec3.det3 vecAInt (Mat3.mulVec gluonLambdaInt vecBInt) vecCInt +
    ColorVec3.det3 vecAInt vecBInt (Mat3.mulVec gluonLambdaInt vecCInt) = 0 := by
  decide

theorem audit_sl3_traceless_quark_derivation_int :
    SplitOctonion.colorDerivation gluonLambdaInt
        (SplitOctonion.mul (SplitOctonion.ggQuark vecAInt) (SplitOctonion.ggQuark vecBInt)) =
      SplitOctonion.add
        (SplitOctonion.mul (SplitOctonion.colorDerivation gluonLambdaInt (SplitOctonion.ggQuark vecAInt))
                           (SplitOctonion.ggQuark vecBInt))
        (SplitOctonion.mul (SplitOctonion.ggQuark vecAInt)
                           (SplitOctonion.colorDerivation gluonLambdaInt (SplitOctonion.ggQuark vecBInt))) := by
  decide

end InfoGeometry.Superalgebra.GunaydinGurseySU3Audit
