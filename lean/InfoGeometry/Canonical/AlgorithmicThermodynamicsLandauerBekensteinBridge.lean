import InfoGeometry.Canonical.MicrostateBoltzmannEntropy
import InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge

namespace InfoGeometry.Canonical.AlgorithmicThermodynamicsLandauerBekensteinBridge

open InfoGeometry.Canonical.MicrostateBoltzmannEntropy
open InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge

noncomputable def thermodynamicPartitionFunction
    {X : Type*} (K : KolmogorovComplexityData X) (S : Finset X) (β : ℝ) : ℝ :=
  ∑ x ∈ S, Real.exp (- β * (K.kolmogorovLength x : ℝ))

noncomputable def chaitinHaltingPartitionFunction
    {X : Type*} (K : KolmogorovComplexityData X) (S : Finset X) : ℝ :=
  ∑ x ∈ S, (2 : ℝ) ^ (- (K.kolmogorovLength x : ℝ))

noncomputable def logicalErasureHeat
    {X : Type*} (P : MicrostateCellPartition X) (x x_prime : X) (T : ℝ) : ℝ :=
  T * (microstateBoltzmannEntropy P x - microstateBoltzmannEntropy P x_prime)

theorem chaitin_kms_partition_duality
    {X : Type*} (K : KolmogorovComplexityData X) (S : Finset X) :
    thermodynamicPartitionFunction K S (Real.log 2) = chaitinHaltingPartitionFunction K S := by
  unfold thermodynamicPartitionFunction chaitinHaltingPartitionFunction
  apply Finset.sum_congr rfl
  intro x hx
  have h_pos : (0 : ℝ) < 2 := by norm_num
  rw [Real.rpow_def_of_pos h_pos]
  congr 1
  ring

theorem landauer_erasure_dissipation_principle
    {X : Type*} (P : MicrostateCellPartition X) (x x_prime : X) (T : ℝ) (hT : 0 < T)
    (h_erasure : microstateBoltzmannEntropy P x_prime < microstateBoltzmannEntropy P x) :
    0 < logicalErasureHeat P x x_prime T := by
  unfold logicalErasureHeat
  have h_diff : 0 < microstateBoltzmannEntropy P x - microstateBoltzmannEntropy P x_prime :=
    sub_pos.mpr h_erasure
  exact mul_pos hT h_diff

end InfoGeometry.Canonical.AlgorithmicThermodynamicsLandauerBekensteinBridge
