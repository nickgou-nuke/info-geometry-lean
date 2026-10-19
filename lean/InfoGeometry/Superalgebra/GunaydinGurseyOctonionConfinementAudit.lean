/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.GunaydinGurseyOctonionConfinement

/-!
# Одит на Раздел 127: Кваркова Структура на Гюнайдън–Гюрсей (1973) и Конфайнмънт

Конкретни целочислени (`ℤ`) проверки с `decide` за проекторното поглъщане на Пиърс,
барионния асоциатор -K₀, централния синглет и асоциативното ядро.
-/

namespace InfoGeometry.Superalgebra.GunaydinGurseyAudit

open InfoGeometry.Superalgebra.GunaydinGursey

def q1Int : ColorVec3 ℤ := ⟨1, 2, 0⟩
def q2Int : ColorVec3 ℤ := ⟨0, 1, 3⟩
def q3Int : ColorVec3 ℤ := ⟨2, 0, 1⟩

theorem audit_peirce_quark_absorption_int :
    SplitOctonion.mul SplitOctonion.e1 (SplitOctonion.quark q1Int) = SplitOctonion.quark q1Int ∧
    SplitOctonion.mul (SplitOctonion.quark q1Int) SplitOctonion.e2 = SplitOctonion.quark q1Int ∧
    SplitOctonion.mul (SplitOctonion.quark q1Int) SplitOctonion.e1 = SplitOctonion.zero ∧
    SplitOctonion.mul SplitOctonion.e2 (SplitOctonion.quark q1Int) = SplitOctonion.zero := by
  decide

theorem audit_three_quark_parenthesization_int :
    ColorVec3.det3 q1Int q2Int q3Int = 13 ∧
    SplitOctonion.mul (SplitOctonion.mul (SplitOctonion.quark q1Int) (SplitOctonion.quark q2Int))
        (SplitOctonion.quark q3Int) = SplitOctonion.scale 13 SplitOctonion.e2 ∧
    SplitOctonion.mul (SplitOctonion.quark q1Int)
        (SplitOctonion.mul (SplitOctonion.quark q2Int) (SplitOctonion.quark q3Int)) =
      SplitOctonion.scale 13 SplitOctonion.e1 := by
  decide

theorem audit_baryon_associator_eq_neg_k0_int :
    SplitOctonion.associator (SplitOctonion.U1 (R := ℤ)) SplitOctonion.U2 SplitOctonion.U3 =
      SplitOctonion.neg SplitOctonion.paraSymplecticK0 ∧
    SplitOctonion.associator (SplitOctonion.quark q1Int) (SplitOctonion.quark q2Int)
        (SplitOctonion.quark q3Int) =
      SplitOctonion.scale (-13) SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_symmetrized_baryon_singlet_int :
    SplitOctonion.symmTriple (SplitOctonion.quark q1Int) (SplitOctonion.quark q2Int)
        (SplitOctonion.quark q3Int) =
      SplitOctonion.scale 13 SplitOctonion.one := by
  decide

theorem audit_color_singlet_associative_nucleus_int :
    let X : SplitOctonion ℤ := ⟨2, q1Int, q2Int, -3⟩
    let Y : SplitOctonion ℤ := ⟨-1, q3Int, q1Int, 4⟩
    SplitOctonion.associator (SplitOctonion.scale 7 SplitOctonion.one) X Y = SplitOctonion.zero ∧
    SplitOctonion.associator X (SplitOctonion.scale 7 SplitOctonion.one) Y = SplitOctonion.zero ∧
    SplitOctonion.associator X Y (SplitOctonion.scale 7 SplitOctonion.one) = SplitOctonion.zero := by
  decide

end InfoGeometry.Superalgebra.GunaydinGurseyAudit
