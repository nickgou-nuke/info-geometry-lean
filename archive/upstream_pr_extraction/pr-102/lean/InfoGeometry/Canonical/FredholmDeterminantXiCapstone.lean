import InfoGeometry.Quantum.FredholmDeterminantXi

namespace InfoGeometry.Canonical.FredholmDeterminantXiCapstone

open InfoGeometry.Quantum.FredholmDeterminantXi

theorem capstone_fredholm_xi_determinant_synthesis
    (s ρ : ℂ) (hρ0 : ρ ≠ 0) (hρ1 : 1 - ρ ≠ 0) (m : ℕ) (p : ℝ) (hm : 1 ≤ m) :
    (spectralZeroPair (1 - s) ρ = spectralZeroPair s ρ) ∧
    (fredholmHadamardFactor ρ ρ = 0) ∧
    (fredholmHadamardFactor (1 - ρ) (1 - ρ) = 0) ∧
    ((m : ℂ) ≠ 0) :=
  grand_fredholm_xi_determinant_synthesis s ρ hρ0 hρ1 m p hm

end InfoGeometry.Canonical.FredholmDeterminantXiCapstone
