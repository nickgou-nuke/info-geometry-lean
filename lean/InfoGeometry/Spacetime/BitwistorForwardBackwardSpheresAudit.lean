/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Spacetime.BitwistorForwardBackwardSpheres

/-!
# Concrete Integer Instantiation & Audit for Section 114: Bitwistor Forward/Backward Spheres
Target: `InfoGeometry/Spacetime/BitwistorForwardBackwardSpheresAudit.lean`

Verifies over `ℤ` (`decide`) that two massless light rays `p_fwd = (13, 3, 4, 12)` (`det = 0`)
and `p_bwd = (13, -3, -4, -12)` (`det = 0`) superpose into a massive bitwistor at rest
`p_tot = (26, 0, 0, 0)` with positive invariant mass squared `m² = 676 = 4 * 13²`.
-/

namespace InfoGeometry.Spacetime.BitwistorAudit

open InfoGeometry.Spacetime.Bitwistor

/-- Concrete verification of massless forward/backward rays generating positive rest mass `m² = 676`. -/
theorem sample_bitwistor_mass_genesis_int :
    let v_fwd : Space3D ℤ := ⟨3, 4, 12⟩
    let v_bwd : Space3D ℤ := ⟨-3, -4, -12⟩
    bispinorDet 13 v_fwd = 0 ∧
    bispinorDet 13 v_bwd = 0 ∧
    bitwistorSpace v_fwd v_bwd = ⟨0, 0, 0⟩ ∧
    bispinorDet (bitwistorTime 13 13) (bitwistorSpace v_fwd v_bwd) = 676 ∧
    2 * (13 * 13 - Space3D.dot v_fwd v_bwd) = 676 := by
  decide

end InfoGeometry.Spacetime.BitwistorAudit
