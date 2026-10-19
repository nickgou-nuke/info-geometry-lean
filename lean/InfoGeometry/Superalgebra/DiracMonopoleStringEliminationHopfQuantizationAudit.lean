/-
Copyright (c) 2026 InfoGeometry Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Contributors
-/
import InfoGeometry.Superalgebra.DiracMonopoleStringEliminationHopfQuantization

/-!
# Audit: DiracMonopoleStringEliminationHopfQuantization
Concrete integer checks for Section 139 Dirac monopole string elimination and Hopf quantization.
-/

namespace InfoGeometry.Superalgebra.DiracMonopoleHopfAudit

open InfoGeometry.Superalgebra.DiracMonopoleHopf

theorem audit_hopf_map_norm_sq_int :
    ColorVec3.normSq (ColorVec3.hopfMap (1 : ℤ) 2 1 0) =
      (1 * 1 + 2 * 2 + 1 * 1 + 0 * 0) * (1 * 1 + 2 * 2 + 1 * 1 + 0 * 0) := by decide

theorem audit_hopf_string_denominators_int :
    let r : ℤ := 1 * 1 + 2 * 2 + 3 * 3 + 1 * 1
    let u := ColorVec3.hopfMap (1 : ℤ) 2 3 1
    r + u.c3 = 2 * (1 * 1 + 2 * 2) ∧ r - u.c3 = 2 * (3 * 3 + 1 * 1) := by decide

theorem audit_stokes_abelian_obstruction_int :
    let da : ColorVec3 ℤ := ⟨1, 2, 0⟩
    let db : ColorVec3 ℤ := ⟨0, 1, 3⟩
    SplitOctonion.trace (SplitOctonion.extDerivativeMC da db) = 0 ∧
    SplitOctonion.superTrace (SplitOctonion.extDerivativeMC da db) = 0 := by decide

theorem audit_octonionic_monopole_supertrace_int :
    let u : ColorVec3 ℤ := ⟨0, 0, 1⟩
    let da : ColorVec3 ℤ := ⟨1, 0, 0⟩
    let db : ColorVec3 ℤ := ⟨0, 1, 0⟩
    SplitOctonion.superTrace (SplitOctonion.faradayYangMills u da db) = -4 := by decide

end InfoGeometry.Superalgebra.DiracMonopoleHopfAudit
