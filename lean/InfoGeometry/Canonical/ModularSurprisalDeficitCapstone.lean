import InfoGeometry.Quantum.ModularSurprisalDeficit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.ModularSurprisalDeficitCapstone

open Real Matrix
open InfoGeometry.Quantum.ModularSurprisalDeficit
open InfoGeometry.Canonical.YangBaxterProof

/-! A direct, owner-aligned packaging of the modular deficit and Yang--Baxter
identities. The removed upstream grand synthesis theorem is not needed. -/
theorem grand_modular_surprisal_capstone
    (x : ℝ) (deltaK deltaS : ℝ) (h_rel : 0 ≤ deltaK - deltaS) :
    (0 ≤ modularDeficit x) ∧
    (modularDeficit x = 0 ↔ x = 0) ∧
    (deltaS ≤ deltaK) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) := by
  exact ⟨modular_deficit_nonneg x,
    modular_deficit_eq_zero_iff x,
    casini_bekenstein_bound deltaK deltaS h_rel,
    F_sq,
    F_B_F_eq_R⟩

end InfoGeometry.Canonical.ModularSurprisalDeficitCapstone
