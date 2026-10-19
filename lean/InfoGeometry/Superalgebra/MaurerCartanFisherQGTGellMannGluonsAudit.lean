/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.MaurerCartanFisherQGTGellMannGluons

/-!
# Audit: Раздел 131 — Квантов Геометричен Тензор на Маурер–Картан и 8-те Глуона на Гел-Ман
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.MaurerCartanFisherGellMann`.
-/

namespace InfoGeometry.Superalgebra.MaurerCartanFisherGellMannAudit

open InfoGeometry.Superalgebra.MaurerCartanFisherGellMann

def sampleU : ColorVec3 ℤ := ⟨1, 2, -1⟩
def sampleDu : ColorVec3 ℤ := ⟨2, -1, 3⟩

theorem audit_flat_projector_fisher_int :
    SplitOctonion.trace
      (SplitOctonion.mul (SplitOctonion.diffProjPlus sampleDu)
                         (SplitOctonion.dagger (SplitOctonion.diffProjPlus sampleDu))) =
      ColorVec3.normSq sampleDu ∧
    ColorVec3.normSq sampleDu = 14 := by decide

theorem audit_maurer_cartan_qgt_lagrange_int :
    SplitOctonion.trace (SplitOctonion.maurerCartanQGT sampleU sampleDu) =
      (1 + ColorVec3.normSq sampleU) * ColorVec3.normSq sampleDu -
        ColorVec3.dot sampleU sampleDu * ColorVec3.dot sampleU sampleDu ∧
    SplitOctonion.trace (SplitOctonion.maurerCartanQGT sampleU sampleDu) = 89 := by decide

theorem audit_berry_force_orthogonal_int :
    ColorVec3.dot sampleDu (SplitOctonion.maurerCartanQGT sampleU sampleDu).u = 0 ∧
    (SplitOctonion.maurerCartanQGT sampleU sampleDu).u ≠ ColorVec3.zero := by decide

theorem audit_gell_mann_gluon_traceless_int :
    Mat3.trace (Mat3.gluonField (1 : ℤ) 2 3 4 5 6 7 8) = 0 ∧
    Mat3.gluonField (1 : ℤ) 2 3 4 5 6 7 8 ≠ default := by decide

end InfoGeometry.Superalgebra.MaurerCartanFisherGellMannAudit
