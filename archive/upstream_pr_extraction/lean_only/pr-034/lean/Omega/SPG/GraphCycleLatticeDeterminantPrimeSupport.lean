import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Omega.SPG.GraphEnergyShellLatticeCounting

namespace Omega.SPG

/-- The Smith-normal-form decomposition packages the kernel as a finite quotient of the integer
cycle lattice: its cardinality is the determinant, and its prime support is exactly the
determinant's prime divisor set.
    cor:graph-cycle-lattice-determinant-prime-support -/
theorem paper_graph_cycle_lattice_determinant_prime_support
    (energyData : GraphEnergyShellLatticeCountingData)
    (determinantNat kernelCardinality : ℕ)
    (invariantFactors : List ℕ) (primeSupport : Finset ℕ)
    (determinantNat_eq_prod : determinantNat = invariantFactors.prod)
    (kernelCardinality_eq_prod : kernelCardinality = invariantFactors.prod)
    (determinantCast_eq_weighted :
      (determinantNat : ℝ) =
        energyData.discriminantData.edgeWeightProduct *
          energyData.discriminantData.reciprocalTreePolynomial)
    (primeSupport_mem_iff :
      ∀ p, p ∈ primeSupport ↔ Nat.Prime p ∧ p ∣ invariantFactors.prod) :
    kernelCardinality = determinantNat ∧
      ∀ p, p ∈ primeSupport ↔ Nat.Prime p ∧ p ∣ determinantNat := by
  obtain ⟨A, _, _, hWeighted⟩ := paper_graph_energy_shell_lattice_counting energyData
  have _hDeterminantWitness : (determinantNat : ℝ) = Matrix.det A := by
    calc
      (determinantNat : ℝ) =
          energyData.discriminantData.edgeWeightProduct *
            energyData.discriminantData.reciprocalTreePolynomial :=
        determinantCast_eq_weighted
      _ = Matrix.det A := by symm; exact hWeighted
  refine ⟨?_, ?_⟩
  · exact kernelCardinality_eq_prod.trans determinantNat_eq_prod.symm
  · intro p
    show p ∈ primeSupport ↔ Nat.Prime p ∧ p ∣ determinantNat
    rw [primeSupport_mem_iff p, determinantNat_eq_prod]

end Omega.SPG
