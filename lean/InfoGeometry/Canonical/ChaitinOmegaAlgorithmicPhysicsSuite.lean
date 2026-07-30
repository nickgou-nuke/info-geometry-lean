import InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge
import InfoGeometry.Canonical.AlgorithmicThermodynamicsLandauerBekensteinBridge

namespace InfoGeometry.Canonical.ChaitinOmegaAlgorithmicPhysicsSuite

open InfoGeometry.Canonical.MicrostateBoltzmannEntropy
open InfoGeometry.Canonical.AlgorithmicBoltzmannKolmogorovBridge
open InfoGeometry.Canonical.AlgorithmicThermodynamicsLandauerBekensteinBridge

noncomputable def ChaitinOmega {X : Type*}
    (K : KolmogorovComplexityData X) (S : Finset X) : ℝ :=
  ∑ x ∈ S, (2 : ℝ) ^ (- (K.kolmogorovLength x : ℝ))

def IsNonInvertibleErasure {X : Type*} (P : MicrostateCellPartition X) (x x_prime : X) : Prop :=
  microstateBoltzmannEntropy P x_prime < microstateBoltzmannEntropy P x

theorem chaitin_omega_kraft_le_one
    {X : Type*} (K : KolmogorovComplexityData X) (S : Finset X) :
    ChaitinOmega K S ≤ 1 :=
  kraft_mcmillan_inequality K S

theorem chaitin_kms_duality_identity
    {X : Type*} (K : KolmogorovComplexityData X) (S : Finset X) :
    thermodynamicPartitionFunction K S (Real.log 2) = ChaitinOmega K S := by
  exact chaitin_kms_partition_duality K S

theorem landauer_heat_dissipation_law
    {X : Type*} (P : MicrostateCellPartition X) (x x_prime : X) (T : ℝ) (hT : 0 < T)
    (h_erase : IsNonInvertibleErasure P x x_prime) :
    0 < logicalErasureHeat P x x_prime T := by
  exact landauer_erasure_dissipation_principle P x x_prime T hT h_erase

end InfoGeometry.Canonical.ChaitinOmegaAlgorithmicPhysicsSuite
