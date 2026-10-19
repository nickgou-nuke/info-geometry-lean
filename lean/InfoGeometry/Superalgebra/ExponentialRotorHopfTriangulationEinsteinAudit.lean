/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.ExponentialRotorHopfTriangulationEinstein

/-!
# Audit: Раздел 132 — Експоненциален Октонионен Ротор exp(ω_L) и Уравнение на Айнщайн–Фишер–Бери
Concrete `ℤ` checks for `InfoGeometry.Superalgebra.ExponentialRotorHopf`.
-/

namespace InfoGeometry.Superalgebra.ExponentialRotorHopfAudit

open InfoGeometry.Superalgebra.ExponentialRotorHopf

def sampleU : ColorVec3 ℤ := ⟨1, 2, -1⟩
def sampleDu : ColorVec3 ℤ := ⟨2, -1, 3⟩

theorem audit_maurer_cartan_form_sq_zero_int :
    SplitOctonion.mul (SplitOctonion.maurerCartanForm sampleU sampleDu)
                      (SplitOctonion.maurerCartanForm sampleU sampleDu) = SplitOctonion.zero ∧
    SplitOctonion.maurerCartanForm sampleU sampleDu ≠ SplitOctonion.zero := by decide

theorem audit_exp_rotor_unitarity_int :
    SplitOctonion.mul (SplitOctonion.expRotor sampleU sampleDu)
                      (SplitOctonion.expRotor sampleU (ColorVec3.neg sampleDu)) = SplitOctonion.one ∧
    SplitOctonion.intervalNorm (SplitOctonion.expRotor sampleU sampleDu) = 1 := by decide

theorem audit_hopf_triangulation_int :
    SplitOctonion.mul (SplitOctonion.twistorProjPlus sampleU)
                      (SplitOctonion.expRotor sampleU sampleDu) =
      SplitOctonion.add (SplitOctonion.twistorProjPlus (ColorVec3.add sampleU sampleDu))
                        (SplitOctonion.antiquark (ColorVec3.cross sampleU sampleDu)) := by decide

theorem audit_einstein_fisher_hopf_dispersion_int :
    let Q := SplitOctonion.maurerCartanQGT sampleU sampleDu
    SplitOctonion.intervalNorm Q = 0 ∧
    SplitOctonion.trace Q * SplitOctonion.trace Q -
      SplitOctonion.superTrace Q * SplitOctonion.superTrace Q =
      4 * ColorVec3.normSq (SplitOctonion.berryHopfForce sampleU sampleDu) ∧
    ColorVec3.normSq (SplitOctonion.berryHopfForce sampleU sampleDu) = 1050 := by decide

end InfoGeometry.Superalgebra.ExponentialRotorHopfAudit
