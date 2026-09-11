import InfoGeometry.Canonical.IBFreeEnergyMinimization
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.IB

open InfoGeometry.Canonical.YangBaxterProof

theorem grand_canonical_ib_free_energy_minimization_synthesis
    {T : Type*} [Fintype T] [DecidableEq T] [Nonempty T]
    (d : T → ℝ) (beta : ℝ) (q : T → ℝ)
    (h_norm : ∑ t : T, q t = 1) (h_nonneg : ∀ t : T, 0 ≤ q t)
    (h_kl_nonneg : 0 ≤ klDivergence q (gibbsDistribution d beta)) :
    (∑ t : T, gibbsDistribution d beta t = 1) ∧
    (ibFreeEnergy d beta (gibbsDistribution d beta) = -Real.log (partitionFunction d beta)) ∧
    (ibFreeEnergy d beta q - ibFreeEnergy d beta (gibbsDistribution d beta) =
      klDivergence q (gibbsDistribution d beta)) ∧
    (ibFreeEnergy d beta (gibbsDistribution d beta) ≤ ibFreeEnergy d beta q) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) := by
  exact ⟨gibbsDistribution_sum_one d beta, gibbs_free_energy_value d beta,
    by rw [gibbs_free_energy_value d beta]
       have h := free_energy_sub_optimal_eq_kl d beta q h_norm h_nonneg
       linarith,
    ib_free_energy_global_minimum d beta q h_norm h_nonneg h_kl_nonneg,
    F_sq, F_B_F_eq_R⟩

end InfoGeometry.Canonical.IB
