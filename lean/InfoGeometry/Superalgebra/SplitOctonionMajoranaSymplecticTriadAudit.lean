/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.SplitOctonionMajoranaSymplecticTriad

/-!
# Одит на Раздел 125: Сплит-Октониони в Базис от 6 Реални Хирални Майорана Нилпотенти

Конкретни целочислени (`ℤ`) проверки с `decide` за изотропните листи,
разлагането на Хестенес, комплексните/хиперкомплексните триади и спиновото куплиране.
-/

namespace InfoGeometry.Superalgebra.MajoranaSplitOctonionsAudit

open InfoGeometry.Superalgebra.MajoranaSplitOctonions

def vecUInt : Vec3 ℤ := ⟨2, -1, 3⟩
def vecVInt : Vec3 ℤ := ⟨4, 5, -1⟩

theorem audit_chiral_sheets_isotropic_int :
    SplitOctonion.mul (SplitOctonion.sheetPlus vecUInt) (SplitOctonion.sheetPlus vecUInt) =
      SplitOctonion.zero ∧
    SplitOctonion.mul (SplitOctonion.sheetMinus vecVInt) (SplitOctonion.sheetMinus vecVInt) =
      SplitOctonion.zero ∧
    SplitOctonion.intervalNorm (SplitOctonion.sheetPlus vecUInt) = 0 ∧
    SplitOctonion.intervalNorm (SplitOctonion.sheetMinus vecVInt) = 0 := by
  decide

theorem audit_hestenes_decomposition_int :
    SplitOctonion.anticommutator (SplitOctonion.sheetPlus vecUInt) (SplitOctonion.sheetMinus vecVInt) =
      SplitOctonion.scale 0 SplitOctonion.one ∧
    SplitOctonion.commutator (SplitOctonion.sheetPlus vecUInt) (SplitOctonion.sheetMinus vecVInt) =
      SplitOctonion.scale 0 SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_complex_hypercomplex_squares_int :
    SplitOctonion.mul (SplitOctonion.complexI1 (R := ℤ)) SplitOctonion.complexI1 =
      SplitOctonion.neg SplitOctonion.one ∧
    SplitOctonion.mul (SplitOctonion.hyperH1 (R := ℤ)) SplitOctonion.hyperH1 =
      SplitOctonion.one := by
  decide

theorem audit_parasymplectic_intertwining_int :
    SplitOctonion.mul (SplitOctonion.paraSymplecticK0 (R := ℤ)) SplitOctonion.complexI1 =
      SplitOctonion.hyperH1 ∧
    SplitOctonion.mul (SplitOctonion.complexI1 (R := ℤ)) SplitOctonion.hyperH1 =
      SplitOctonion.paraSymplecticK0 := by
  decide

theorem audit_spin_majorana_coupling_int :
    SplitOctonion.mul (SplitOctonion.complexI1 (R := ℤ)) SplitOctonion.complexI2 =
      SplitOctonion.neg SplitOctonion.complexI3 ∧
    SplitOctonion.mul (SplitOctonion.hyperH1 (R := ℤ)) SplitOctonion.hyperH2 =
      SplitOctonion.neg SplitOctonion.complexI3 ∧
    SplitOctonion.mul (SplitOctonion.U1 (R := ℤ)) SplitOctonion.U2 =
      SplitOctonion.V3 := by
  decide

end InfoGeometry.Superalgebra.MajoranaSplitOctonionsAudit
