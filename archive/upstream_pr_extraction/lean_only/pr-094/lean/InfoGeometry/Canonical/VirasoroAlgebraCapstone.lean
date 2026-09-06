import InfoGeometry.CFT.VirasoroAlgebra

namespace InfoGeometry.Canonical

open InfoGeometry.CFT.VirasoroAlgebra

/-- Canonical projection capstone for Virasoro Algebra module. -/
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
     virasoroPrimePhase m_num γ * virasoroPrimePhase n_num γ) :=
  grand_virasoro_conformal_synthesis m n k γ p m_num n_num hm hn

end InfoGeometry.Canonical
