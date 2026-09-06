import InfoGeometry.Quantum.ConnesAdeleTrace

namespace InfoGeometry.Canonical.ConnesAdeleTraceCapstone

open InfoGeometry.Quantum.ConnesAdeleTrace

theorem verification_capstone
    {N : ℕ} (zeros : RiemannZeroRegister (N + 1)) (test : AdeleTestFunction)
    (p : ℕ) (hp : 1 < p) (m : ℕ) (h_pos : ∀ x, 0 ≤ test.h x) :
    (test.h_hat ⟨1 / 2, zeros.gamma 0⟩ =
      test.h_hat (1 - ⟨1 / 2, zeros.gamma 0⟩)) ∧
      (Real.log ((p : ℝ) ^ m) = (m : ℝ) * Real.log (p : ℝ)) ∧
      (0 ≤ primeOrbitOrbitalTerm p (m + 1) test) := by
  exact ⟨spectral_zero_functional_symmetry test (zeros.gamma 0),
    prime_orbit_period_scaling p (Nat.zero_lt_of_lt hp) m,
    prime_orbit_term_nonneg p hp m test h_pos⟩

end InfoGeometry.Canonical.ConnesAdeleTraceCapstone
