import InfoGeometry.Quantum.ChiralCantorRandomWalk
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ChiralCantorRandomWalkCapstone

open InfoGeometry.Quantum.ChiralCantorRandomWalk

/-! Direct synthesis of the finite chiral walk invariants from their owner
lemmas. -/
theorem capstone_chiral_cantor_random_walk_synthesis {n : ℕ} (state : BiCantorState n)
    (w : ChiralBitWord n n)
    (h_symm : state.left = state.right)
    (h_balanced : wordDisplacement w.1 = wordDisplacement w.2)
    (σ : ℝ) (h_balance : σ - 1 / 2 = 0) :
    (paritySwap (paritySwap state) = state) ∧
    (chiralCharge (paritySwap state) = -chiralCharge state) ∧
    (chiralCharge state = 0) ∧
    (numberL state = numberR state) ∧
    (lightConeU w * lightConeV w = (chiralScale n n) ^ 2 - (chiralRapidity w) ^ 2) ∧
    (chiralCylinderWeight n n = (1 / 2 : ℝ) ^ (n + n)) ∧
    (chiralRapidity w = 0) ∧
    (σ = 1 / 2) := by
  have h_zero := chiral_charge_symmetric_zero state h_symm
  exact ⟨parity_swap_involutive state,
    chiral_charge_parity_odd state,
    h_zero,
    equal_populations_of_zero_charge state h_zero,
    lightcone_chiral_factorization w,
    chiral_cylinder_weight_eq n n,
    chiral_parity_equilibrium w h_balanced,
    critical_line_from_chiral_walk_balance σ h_balance⟩

end InfoGeometry.Canonical.ChiralCantorRandomWalkCapstone
