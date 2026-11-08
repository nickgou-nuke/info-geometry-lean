/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.MaurerCartanAssociatorAnomalySuperGrassmannian

/-!
# Одит на Раздел 129: Неасоциативна Кула на Маурер–Картан и Туисторен Проектор

Конкретни целочислени (`ℤ`) проверки с `decide` за вложения комутатор в кулата на Маурер–Картан,
аномалията на Акивис–Малцев и супер-Грасманиановите туисторни проектори.
-/

namespace InfoGeometry.Superalgebra.MaurerCartanSuperGrassmannianAudit

open InfoGeometry.Superalgebra.MaurerCartanSuperGrassmannian

def qAInt : ColorVec3 ℤ := ⟨1, 0, 2⟩
def qBInt : ColorVec3 ℤ := ⟨-1, 3, 1⟩
def qCInt : ColorVec3 ℤ := ⟨2, 1, 0⟩
def orthVInt : ColorVec3 ℤ := ⟨-2, 5, 1⟩

theorem audit_maurer_cartan_nested_commutator_int :
    SplitOctonion.commutator (SplitOctonion.quark qAInt) (SplitOctonion.quark qBInt) =
      SplitOctonion.scale 2 (SplitOctonion.antiquark (ColorVec3.cross qAInt qBInt)) ∧
    SplitOctonion.commutator
        (SplitOctonion.commutator (SplitOctonion.quark qAInt) (SplitOctonion.quark qBInt))
        (SplitOctonion.quark qCInt) =
      SplitOctonion.scale (- 2 * ColorVec3.det3 qAInt qBInt qCInt) SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_akivis_malcev_jacobiator_anomaly_int :
    ColorVec3.det3 qAInt qBInt qCInt = -15 ∧
    SplitOctonion.jacobiator
        (SplitOctonion.quark qAInt) (SplitOctonion.quark qBInt) (SplitOctonion.quark qCInt) =
      SplitOctonion.scale 6
        (SplitOctonion.associator
          (SplitOctonion.quark qAInt) (SplitOctonion.quark qBInt) (SplitOctonion.quark qCInt)) ∧
    SplitOctonion.jacobiator
        (SplitOctonion.quark qAInt) (SplitOctonion.quark qBInt) (SplitOctonion.quark qCInt) =
      SplitOctonion.scale 90 SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_twistor_projectors_idempotent_null_int :
    SplitOctonion.mul (SplitOctonion.twistorProjPlus qAInt) (SplitOctonion.twistorProjPlus qAInt) =
      SplitOctonion.twistorProjPlus qAInt ∧
    SplitOctonion.mul (SplitOctonion.twistorProjMinus qBInt) (SplitOctonion.twistorProjMinus qBInt) =
      SplitOctonion.twistorProjMinus qBInt ∧
    SplitOctonion.intervalNorm (SplitOctonion.twistorProjPlus qAInt) = 0 ∧
    SplitOctonion.intervalNorm (SplitOctonion.twistorProjMinus qBInt) = 0 := by
  decide

theorem audit_twistor_parallel_transport_semigroup_int :
    SplitOctonion.mul (SplitOctonion.twistorProjPlus qAInt) (SplitOctonion.twistorProjPlus qBInt) =
      SplitOctonion.add (SplitOctonion.twistorProjPlus qBInt)
        (SplitOctonion.antiquark (ColorVec3.cross qAInt qBInt)) ∧
    SplitOctonion.mul (SplitOctonion.twistorProjMinus qAInt) (SplitOctonion.twistorProjMinus qBInt) =
      SplitOctonion.sub (SplitOctonion.twistorProjMinus qBInt)
        (SplitOctonion.quark (ColorVec3.cross qAInt qBInt)) := by
  decide

theorem audit_twistor_penrose_incidence_int :
    ColorVec3.dot qAInt orthVInt = 0 ∧
    SplitOctonion.mul (SplitOctonion.twistorProjPlus qAInt) (SplitOctonion.twistorProjMinus orthVInt) =
      SplitOctonion.quark qAInt := by
  decide

end InfoGeometry.Superalgebra.MaurerCartanSuperGrassmannianAudit
