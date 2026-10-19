/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.FaradayYangMillsMonopoleChernSimons

/-!
# Audit: Раздел 135 — Поле на Фарадей–Янг–Милс и Инвариант на Чърн–Саймънс
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.FaradayYangMillsChernSimons`.
-/

namespace InfoGeometry.Superalgebra.FaradayYangMillsChernSimonsAudit

open InfoGeometry.Superalgebra.FaradayYangMillsChernSimons

def sampleU  : ColorVec3 ℤ := ⟨1, 0, 0⟩
def sampleDa : ColorVec3 ℤ := ⟨0, 1, 0⟩
def sampleDb : ColorVec3 ℤ := ⟨0, 0, 1⟩
def sampleDcTangent : ColorVec3 ℤ := ⟨0, 2, -3⟩
def sampleDcRadial  : ColorVec3 ℤ := ⟨5, 2, -3⟩

theorem audit_hopf_double_cross_int :
    ColorVec3.cross (ColorVec3.cross sampleU sampleDa) (ColorVec3.cross sampleU sampleDb) =
      ColorVec3.smul (ColorVec3.det3 sampleU sampleDa sampleDb) sampleU ∧
    ColorVec3.det3 sampleU sampleDa sampleDb = 1 := by decide

theorem audit_faraday_yang_mills_monopole_int :
    SplitOctonion.faradayYangMillsCurvature sampleU sampleDa sampleDb =
      SplitOctonion.scale (-2 * ColorVec3.det3 sampleU sampleDa sampleDb)
        (SplitOctonion.add SplitOctonion.paraSymplecticK0 (SplitOctonion.quark sampleU)) ∧
    SplitOctonion.superTrace
      (SplitOctonion.faradayYangMillsCurvature sampleU sampleDa sampleDb) = -4 := by decide

theorem audit_chern_simons_radial_and_tangent_int :
    SplitOctonion.chernSimons3Form sampleU sampleDa sampleDb sampleDcTangent = 0 ∧
    SplitOctonion.chernSimons3Form sampleU sampleDa sampleDb sampleDcRadial = -10 := by decide

theorem audit_dual_conjugate_involutive_and_trace_int :
    let X := SplitOctonion.canonicalSplitOctonionInt
    SplitOctonion.dualConjugate (SplitOctonion.dualConjugate X) = X ∧
    SplitOctonion.trace (SplitOctonion.dualConjugate X) = SplitOctonion.trace X ∧
    SplitOctonion.dualConjugate X ≠ X := by decide

end InfoGeometry.Superalgebra.FaradayYangMillsChernSimonsAudit
