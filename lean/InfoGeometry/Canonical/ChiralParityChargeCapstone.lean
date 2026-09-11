import InfoGeometry.Quantum.ChiralParityCharge
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ChiralParityCharge

/-! A direct capstone for the parity-odd charge and its critical-line
specialization. -/
theorem chiral_parity_charge_canonical_capstone {R : Type*} [CommRing R]
    (N_L N_R : R) (σ : ℝ)
    (h_eq : N_L = N_R) (h_chiral : chiralParityCharge σ (1 / 2) = 0) :
    (chiralParityCharge N_R N_L = - chiralParityCharge N_L N_R) ∧
    (chiralParityCharge N_L N_R = 0) ∧
    (σ = 1 / 2) := by
  exact ⟨chiral_charge_parity_odd N_L N_R,
    chiral_charge_eq_zero_of_equal_modes N_L N_R h_eq,
    critical_line_from_chiral_balance σ h_chiral⟩

end InfoGeometry.Canonical
