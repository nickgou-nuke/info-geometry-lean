import InfoGeometry.CFT.VirasoroAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.CFT.VirasoroAlgebra

/-- Canonical synthesis of the algebraic Witt, spectral, and prime-phase laws.
    The formerly advertised grand theorem is intentionally not required: its
    six components are assembled directly from the proved owner lemmas. -/
theorem virasoro_algebra_canonical_capstone
    (m n k : ℤ) (γ p : ℝ) (m_num n_num : ℝ) (hm : 0 < m_num) (hn : 0 < n_num) :
    (wittStructureConstant m n = - wittStructureConstant n m) ∧
    (wittStructureConstant m n * wittStructureConstant (m + n) k +
     wittStructureConstant n k * wittStructureConstant (n + k) m +
     wittStructureConstant k m * wittStructureConstant (k + m) n = 0) ∧
    (conformalHamiltonianEigenvalue γ = 0) ∧
    (conformalSpinEigenvalue γ = -γ) ∧
    (‖virasoroPrimePhase p γ‖ = 1) ∧
    (virasoroPrimePhase (m_num * n_num) γ =
     virasoroPrimePhase m_num γ * virasoroPrimePhase n_num γ) := by
  exact ⟨witt_structure_antisymmetry m n,
    witt_jacobi_identity m n k,
    conformal_hamiltonian_vanishes γ,
    conformal_spin_eq_neg_gamma γ,
    virasoro_prime_phase_unitary p γ,
    virasoro_prime_ope_mul m_num n_num γ hm hn⟩

end InfoGeometry.Canonical
