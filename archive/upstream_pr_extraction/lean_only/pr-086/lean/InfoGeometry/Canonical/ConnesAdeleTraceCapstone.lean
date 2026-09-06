import InfoGeometry.Quantum.ConnesAdeleTrace

namespace InfoGeometry.Canonical.ConnesAdeleTraceCapstone

open InfoGeometry.Quantum.ConnesAdeleTrace

set_option linter.unusedVariables false

theorem verification_capstone
    {N : ℕ} (zeros : RiemannZeroRegister (N + 1)) (test : AdeleTestFunction)
    (p : ℕ) (hp : 1 < p) (m : ℕ) (h_pos : ∀ x, 0 ≤ test.h x) :
    (test.h_hat ⟨1 / 2, zeros.gamma 0⟩ =
      test.h_hat (1 - ⟨1 / 2, zeros.gamma 0⟩)) ∧
      (Real.log ((p : ℝ) ^ m) = (m : ℝ) * Real.log (p : ℝ)) ∧
      (0 ≤ primeOrbitOrbitalTerm p (m + 1) test) := by
  exact grand_connes_adele_trace_synthesis zeros test p hp m h_pos

end InfoGeometry.Canonical.ConnesAdeleTraceCapstone
