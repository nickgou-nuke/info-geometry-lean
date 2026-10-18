/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.WuYangNonAbelianDualABInterferometry

/-!
# Concrete Integer Instantiation & Audit for Section 123: Wu–Yang Non-Abelian & Dual AB Interferometry
Target: `InfoGeometry/QuantumContext/WuYangNonAbelianDualABInterferometryAudit.lean`

Verifies over `ℤ` (`decide`) that the Maxwell duality invariance of `J_dual`,
the Euler–Hurwitz four-square identity for `SU(2)` holonomy transport, and central destructive
cancellation hold on concrete non-zero configurations.
-/

namespace InfoGeometry.QuantumContext.WuYangDualABAudit

open InfoGeometry.QuantumContext.WuYangDualAB

/-- Concrete verification of Maxwell duality invariance of `J_dual = (μ × E) - (d × B)` over `ℤ`. -/
theorem sample_dual_ab_phase_maxwell_invariant_int :
    let D : DipoleDoublet ℤ := ⟨⟨1, 2, 3⟩, ⟨4, 5, 6⟩⟩
    let F : EMFieldDoublet ℤ := ⟨⟨7, 8, 9⟩, ⟨2, 1, 4⟩⟩
    dualTopologicalPhaseVec D F = ⟨-8, 4, 0⟩ ∧
    dualTopologicalPhaseVec (maxwellDipoleDual D) (maxwellFieldDual F) = ⟨-8, 4, 0⟩ := by
  decide

/-- Concrete verification of Euler–Hurwitz four-square multiplicativity `‖U · Ψ‖² = ‖U‖² · ‖Ψ‖²` over `ℤ`:
for `U = (1, 2, 3, 4)` (`‖U‖² = 30`) and `Ψ = (2, 1, 4, 3)` (`‖Ψ‖² = 30`), `‖U · Ψ‖² = 900`. -/
theorem sample_euler_hurwitz_wuyang_norm_int :
    let U : SU2QuatAmp ℤ := ⟨1, 2, 3, 4⟩
    let Ψ : SU2QuatAmp ℤ := ⟨2, 1, 4, 3⟩
    SU2QuatAmp.normSq U = 30 ∧
    SU2QuatAmp.normSq Ψ = 30 ∧
    SU2QuatAmp.normSq (SU2QuatAmp.mul U Ψ) = 900 ∧
    SU2QuatAmp.nonAbelianTransitionProb Ψ Ψ ⟨-1, 0, 0, 0⟩ = 0 := by
  decide

end InfoGeometry.QuantumContext.WuYangDualABAudit
