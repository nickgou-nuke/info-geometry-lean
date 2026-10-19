/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.MadelungNonassociativeVortexSmoothness

/-!
# Audit: MadelungNonassociativeVortexSmoothness
Concrete integer checks for Section 141b Madelung nonassociative vortex smoothness.
-/

namespace InfoGeometry.Superalgebra.MadelungNonassociativeVortexAudit

open InfoGeometry.Superalgebra.MadelungNonassociativeVortex

theorem audit_madelung_vortex_akivis_anomaly_int :
    let u_S : ColorVec3 ℤ := ⟨1, 0, 0⟩
    let grad_a : ColorVec3 ℤ := ⟨0, 1, 0⟩
    let grad_b : ColorVec3 ℤ := ⟨0, 0, 1⟩
    SplitOctonion.jacobiator (SplitOctonion.quark u_S)
                             (SplitOctonion.quark grad_a)
                             (SplitOctonion.quark grad_b) =
      SplitOctonion.scale (-6) SplitOctonion.paraSymplecticK0 := by decide

theorem audit_madelung_vortex_general_det3_int :
    let u_S : ColorVec3 ℤ := ⟨1, 2, 1⟩
    let grad_a : ColorVec3 ℤ := ⟨2, 1, 0⟩
    let grad_b : ColorVec3 ℤ := ⟨0, 1, 3⟩
    SplitOctonion.jacobiator (SplitOctonion.quark u_S)
                             (SplitOctonion.quark grad_a)
                             (SplitOctonion.quark grad_b) =
      SplitOctonion.scale (-6 * ColorVec3.det3 u_S grad_a grad_b) SplitOctonion.paraSymplecticK0 := by decide

theorem audit_madelung_theta_coherence_int :
    ((5 : ℤ) - 3 * 2) * 7 - (4 - 3 * 7) * 2 = 5 * 7 - 4 * 2 := by decide

theorem audit_dyon_phase_commutator_non_zero_int :
    let u_S : ColorVec3 ℤ := ⟨1, 1, 0⟩
    SplitOctonion.commutator (SplitOctonion.dyonPhase 2 1 u_S)
                             (SplitOctonion.dyonPhase 1 3 u_S) ≠ SplitOctonion.zero := by decide

end InfoGeometry.Superalgebra.MadelungNonassociativeVortexAudit
