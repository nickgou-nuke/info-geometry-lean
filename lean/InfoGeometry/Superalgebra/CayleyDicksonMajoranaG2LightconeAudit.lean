/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.CayleyDicksonMajoranaG2Lightcone

/-!
# Одит на Раздел 126: Кейли–Диксън Изоморфизъм 𝕆_s ≅ ℍ ⊕ K₀ℍ, Светлинен Конус и G₂(2)

Конкретни целочислени (`ℤ`) проверки с `decide` за диагонализацията на интервала,
светлинния конус s² = 0, преобразуването на Кейли и цветовите деривации.
-/

namespace InfoGeometry.Superalgebra.CayleyDicksonG2Audit

open InfoGeometry.Superalgebra.CayleyDicksonG2

def quatPInt : Quat4 ℤ := ⟨2, ⟨1, 2, 2⟩⟩
def quatQInt : Quat4 ℤ := ⟨3, ⟨0, 2, 0⟩⟩
def rayWInt  : Vec3 ℤ := ⟨3, -4, 1⟩

theorem audit_cayley_dickson_intertwining_int :
    SplitOctonion.fromCayleyDickson quatPInt quatQInt =
      SplitOctonion.add (SplitOctonion.embedQuat quatPInt)
        (SplitOctonion.mul SplitOctonion.paraSymplecticK0 (SplitOctonion.embedQuat quatQInt)) := by
  decide

theorem audit_cayley_dickson_diagonal_norm_int :
    Quat4.normSq quatPInt = 13 ∧
    Quat4.normSq quatQInt = 13 ∧
    SplitOctonion.intervalNorm (SplitOctonion.fromCayleyDickson quatPInt quatQInt) = 0 := by
  decide

theorem audit_chiral_sheets_equal_norm_rays_int :
    SplitOctonion.fromCayleyDickson ⟨0, rayWInt⟩ ⟨0, rayWInt⟩ =
      SplitOctonion.sheetPlus (Vec3.smul 2 rayWInt) ∧
    SplitOctonion.intervalNorm (SplitOctonion.fromCayleyDickson ⟨0, rayWInt⟩ ⟨0, rayWInt⟩) = 0 := by
  decide

theorem audit_cayley_transform_nilpotent_int :
    SplitOctonion.mul
        (SplitOctonion.sub SplitOctonion.one (SplitOctonion.sheetPlus rayWInt))
        (SplitOctonion.add SplitOctonion.one (SplitOctonion.sheetPlus rayWInt)) =
      SplitOctonion.one ∧
    SplitOctonion.intervalNorm (SplitOctonion.cayleyTransformPlus rayWInt) = 1 := by
  decide

theorem audit_sl3_derivation_interval_invariance_int :
    let X : SplitOctonion ℤ := ⟨5, ⟨1, 2, 3⟩, ⟨4, -1, 2⟩, 7⟩
    let dX := SplitOctonion.sl3ColorDerivation 2 (-5) 3 X
    Vec3.dot dX.u X.v + Vec3.dot X.u dX.v = 0 := by
  decide

end InfoGeometry.Superalgebra.CayleyDicksonG2Audit
