import InfoGeometry.Quantum.FredholmDeterminantXi

namespace InfoGeometry.Canonical.FredholmDeterminantXiCapstone

open InfoGeometry.Quantum.FredholmDeterminantXi

theorem capstone_fredholm_xi_determinant_synthesis
    (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) (m : ℕ) (p : ℝ) (hm : 1 ≤ m) :
    (spectralZeroPair (1 - s) ρ = spectralZeroPair s ρ) ∧
    (fredholmHadamardFactor ρ ρ = 0) ∧
    (fredholmHadamardFactor (1 - ρ) (1 - ρ) = 0) ∧
    ((m : ℂ) ≠ 0) := by
  exact ⟨spectral_zero_pair_reflection s ρ hρ0 hρ1,
    fredholm_factor_vanishes_at_zero ρ hρ0,
    fredholm_factor_vanishes_at_dual_zero ρ hρ1,
    cumulant_trace_term_well_defined m p s hm⟩

end InfoGeometry.Canonical.FredholmDeterminantXiCapstone
