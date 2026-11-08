/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.DiracSchwingerZwanzigerDyonicQuantization

/-!
# Audit: DiracSchwingerZwanzigerDyonicQuantization
Concrete integer checks for Section 140a DSZ dyonic quantization and Witten shift invariance.
-/

namespace InfoGeometry.Superalgebra.DSZDyonsAudit

open InfoGeometry.Superalgebra.DSZDyons

theorem audit_dsz_bracket_antisymm_int :
    let D1 : DyonCharge ℤ := ⟨3, 2⟩
    let D2 : DyonCharge ℤ := ⟨1, 5⟩
    DyonCharge.dszBracket D1 D2 = - DyonCharge.dszBracket D2 D1 := by decide

theorem audit_witten_shift_invariance_int :
    let D1 : DyonCharge ℤ := ⟨4, 3⟩
    let D2 : DyonCharge ℤ := ⟨-2, 5⟩
    DyonCharge.dszBracket (DyonCharge.wittenShift 7 D1) (DyonCharge.wittenShift 7 D2) =
      DyonCharge.dszBracket D1 D2 := by decide

theorem audit_dirac_monopole_reduction_int :
    DyonCharge.dszBracket (DyonCharge.electron (3 : ℤ)) (DyonCharge.monopole 4) = 12 := by decide

theorem audit_baryonic_associator_flux_int :
    let u : ColorVec3 ℤ := ⟨1, 0, 0⟩
    let da : ColorVec3 ℤ := ⟨0, 1, 0⟩
    let db : ColorVec3 ℤ := ⟨0, 0, 1⟩
    SplitOctonion.associator (SplitOctonion.quark u) (SplitOctonion.quark da) (SplitOctonion.quark db) =
      SplitOctonion.scale (-ColorVec3.det3 u da db) SplitOctonion.paraSymplecticK0 := by decide

end InfoGeometry.Superalgebra.DSZDyonsAudit
