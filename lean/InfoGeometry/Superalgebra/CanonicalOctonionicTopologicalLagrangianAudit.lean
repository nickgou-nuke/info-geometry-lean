/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.CanonicalOctonionicTopologicalLagrangian

/-!
# Audit: Раздел 136 — Каноничен Топологичен Лагранжиан и Хелмхолц–Ходж–Дирак
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.CanonicalOctonionicLagrangian`.
-/

namespace InfoGeometry.Superalgebra.CanonicalOctonionicLagrangianAudit

open InfoGeometry.Superalgebra.CanonicalOctonionicLagrangian

def sampleK : ColorVec3 ℤ := ⟨1, 2, 2⟩
def sampleU : ColorVec3 ℤ := ⟨2, -2, 1⟩
def sampleV : ColorVec3 ℤ := ⟨2, 1, -3⟩

theorem audit_dirac_action_on_full_spinor_int :
    SplitOctonion.mul (SplitOctonion.diracGradH sampleK)
                      (SplitOctonion.fullSpinorPsi sampleU sampleV) =
      ⟨ColorVec3.dot sampleK sampleV,
       ColorVec3.neg (ColorVec3.cross sampleK sampleV),
       ColorVec3.cross sampleK sampleU,
       ColorVec3.dot sampleK sampleU⟩ := by decide

theorem audit_helmholtz_hodge_lagrangian_int :
    SplitOctonion.canonicalLagrangian sampleK sampleU sampleV =
      ColorVec3.dot sampleK sampleU * ColorVec3.dot sampleK sampleV +
        ColorVec3.dot (ColorVec3.cross sampleK sampleU) (ColorVec3.cross sampleK sampleV) ∧
    SplitOctonion.canonicalLagrangian sampleK sampleU sampleV = -9 := by decide

theorem audit_binet_cauchy_propagator_int :
    SplitOctonion.canonicalLagrangian sampleK sampleU sampleV =
      ColorVec3.normSq sampleK * ColorVec3.dot sampleU sampleV ∧
    ColorVec3.normSq sampleK = 9 ∧
    ColorVec3.dot sampleU sampleV = -1 := by decide

theorem audit_transverse_coulomb_gauge_int :
    ColorVec3.dot sampleK sampleU = 0 ∧
    ColorVec3.dot (ColorVec3.cross sampleK sampleU) (ColorVec3.cross sampleK sampleV) =
      ColorVec3.normSq sampleK * ColorVec3.dot sampleU sampleV := by decide

end InfoGeometry.Superalgebra.CanonicalOctonionicLagrangianAudit
