/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.DyonDszWittenQuantization

/-!
# Audit: DyonDszWittenQuantization
Concrete integer checks for Section 140b DSZ commutator and Witten rotor effect.
-/

namespace InfoGeometry.Superalgebra.DyonWittenQuantizationAudit

open InfoGeometry.Superalgebra.DyonWittenQuantization

theorem audit_dsz_dyon_commutator_int :
    let u : ColorVec3 ℤ := ⟨1, 2, 2⟩
    SplitOctonion.commutator (SplitOctonion.dyon 3 1 u) (SplitOctonion.dyon 2 5 u) =
      SplitOctonion.scale ((3 * 5 - 2 * 1) * ColorVec3.normSq u) SplitOctonion.paraSymplecticK0 := by decide

theorem audit_witten_effect_generation_int :
    let u : ColorVec3 ℤ := ⟨1, 0, -1⟩
    SplitOctonion.mul
      (SplitOctonion.mul (SplitOctonion.wittenRotor 2 1) (SplitOctonion.dyonMajorana 0 3 u))
      (SplitOctonion.wittenRotorAdj 2 1) =
      SplitOctonion.dyonMajorana (-12) 15 u := by decide

theorem audit_witten_shift_pairing_int :
    ((4 : ℤ) - 7 * 3) * 5 - (2 - 7 * 5) * 3 = 4 * 5 - 2 * 3 := by decide

theorem audit_dyon_interval_norm_int :
    let u : ColorVec3 ℤ := ⟨1, 2, 0⟩
    SplitOctonion.intervalNorm (SplitOctonion.dyon 3 2 u) = -30 := by decide

end InfoGeometry.Superalgebra.DyonWittenQuantizationAudit
