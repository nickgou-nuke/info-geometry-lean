/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.EinsteinDiracUnruhKMS

/-!
# Audit: Раздел 134 — Сливане на Спина и Спиновата Връзка, Айнщайн–Дирак и Унру–КМШ
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.EinsteinDiracUnruh`.
-/

namespace InfoGeometry.Superalgebra.EinsteinDiracUnruhAudit

open InfoGeometry.Superalgebra.EinsteinDiracUnruh

def sampleU : ColorVec3 ℤ := ⟨1, 2, -1⟩
def sampleDu : ColorVec3 ℤ := ⟨2, -1, 3⟩
def sampleGrad : ColorVec3 ℤ := ⟨3, 1, -2⟩

theorem audit_spin_connection_fusion_int :
    SplitOctonion.commutator (SplitOctonion.quark sampleU) (SplitOctonion.diracVecH sampleDu) =
      SplitOctonion.add
        (SplitOctonion.scale (ColorVec3.dot sampleU sampleDu) SplitOctonion.paraSymplecticK0)
        (SplitOctonion.scale 2 (SplitOctonion.antiquark (ColorVec3.cross sampleU sampleDu))) := by
  decide

theorem audit_fisher_spacetime_metric_int :
    SplitOctonion.trace
      (SplitOctonion.mul (SplitOctonion.diffProjPlus sampleU)
                         (SplitOctonion.dagger (SplitOctonion.diffProjPlus sampleDu))) =
      ColorVec3.dot sampleU sampleDu ∧
    ColorVec3.dot sampleU sampleDu = -3 := by decide

theorem audit_einstein_dirac_laplacian_int :
    SplitOctonion.mul (SplitOctonion.diracVecH sampleGrad) (SplitOctonion.diracVecH sampleGrad) =
      SplitOctonion.scale (ColorVec3.dot sampleGrad sampleGrad) SplitOctonion.one ∧
    ColorVec3.dot sampleGrad sampleGrad = 14 := by decide

theorem audit_unruh_kms_detailed_balance_int :
    let Ψ_unruh := SplitOctonion.mul (SplitOctonion.unruhModularRotor (5 : ℤ) 3)
                                     (SplitOctonion.diracVecH sampleU)
    ColorVec3.smul (5 - 3) Ψ_unruh.u = ColorVec3.smul (5 + 3) Ψ_unruh.v ∧
    Ψ_unruh.u ≠ Ψ_unruh.v := by decide

end InfoGeometry.Superalgebra.EinsteinDiracUnruhAudit
