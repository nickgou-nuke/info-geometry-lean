/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.MaurerCartanBianchiTorsionSuperGrassmannian

/-!
# Одит на Раздел 130: Форма на Маурер–Картан ω = g⁻¹dg, Аномалия на Бианки и Поток

Конкретни целочислени (`ℤ`) проверки с `decide` за двулистната форма на Маурер–Картан,
нейната светлинна изотропност, аномалията на Бианки и конформната транслация с торзия.
-/

namespace InfoGeometry.Superalgebra.MaurerCartanBianchiAudit

open InfoGeometry.Superalgebra.MaurerCartanBianchi

def posUInt  : ColorVec3 ℤ := ⟨2, -1, 3⟩
def diffUInt : ColorVec3 ℤ := ⟨1, 4, -2⟩
def colAInt  : ColorVec3 ℤ := ⟨6, -3, 9⟩
def w1Int    : ColorVec3 ℤ := ⟨1, 1, 0⟩
def w2Int    : ColorVec3 ℤ := ⟨0, 1, 2⟩
def w3Int    : ColorVec3 ℤ := ⟨3, 0, 1⟩

theorem audit_maurer_cartan_left_form_decomposition_int :
    SplitOctonion.maurerCartanLeftForm posUInt diffUInt =
      SplitOctonion.sub (SplitOctonion.quark diffUInt)
                        (SplitOctonion.antiquark (ColorVec3.cross posUInt diffUInt)) := by
  decide

theorem audit_maurer_cartan_left_form_null_int :
    SplitOctonion.intervalNorm (SplitOctonion.maurerCartanLeftForm posUInt diffUInt) = 0 := by
  decide

theorem audit_nonassociative_bianchi_anomaly_int :
    ColorVec3.det3 w1Int w2Int w3Int = 7 ∧
    SplitOctonion.bianchiCovariantDerivative3Form
        (SplitOctonion.quark w1Int) (SplitOctonion.quark w2Int) (SplitOctonion.quark w3Int) =
      SplitOctonion.scale (-42) SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_coplanar_bianchi_vanishes_int :
    let wCoplanar := ColorVec3.add w1Int w2Int
    ColorVec3.det3 w1Int w2Int wCoplanar = 0 ∧
    SplitOctonion.bianchiCovariantDerivative3Form
        (SplitOctonion.quark w1Int) (SplitOctonion.quark w2Int) (SplitOctonion.quark wCoplanar) =
      SplitOctonion.zero := by
  decide

theorem audit_twistor_projector_torsion_and_collinear_shift_int :
    SplitOctonion.mul (SplitOctonion.twistorProjPlus posUInt) (SplitOctonion.gaugeGroupElem diffUInt) =
      SplitOctonion.add (SplitOctonion.twistorProjPlus (ColorVec3.add posUInt diffUInt))
                        (SplitOctonion.antiquark (ColorVec3.cross posUInt diffUInt)) ∧
    ColorVec3.cross posUInt colAInt = ColorVec3.zero ∧
    SplitOctonion.mul (SplitOctonion.twistorProjPlus posUInt) (SplitOctonion.gaugeGroupElem colAInt) =
      SplitOctonion.twistorProjPlus (ColorVec3.add posUInt colAInt) := by
  decide

end InfoGeometry.Superalgebra.MaurerCartanBianchiAudit
