import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCoadjointBridge
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open SouriauCoadjoint
open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open scoped BigOperators

namespace InfoGeometry.Canonical

variable {State G : Type*} [Fintype State] [Nonempty State]
variable (D : CartanSouriauDatum State)

/-- A concrete structural realization of the coadjoint action on a finite Cartan state space.
This bundles the permutation action on states with the adjoint action on parameters,
providing the exact algebraic identities needed to prove Fisher metric covariance
without invoking analytic derivatives. -/
structure CartanStatePermutationAction where
  -- Adjoint action on temperatures/parameters
  Ad : G → (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)
  -- Permutation action on the microstates
  stateEquiv : G → State ≃ State
  -- The Souriau cocycle (anomaly)
  cocycle : G → LieDual (Fin 2 → ℝ)
  -- The fundamental algebraic covariance of the pairing energy
  pairing_cov : ∀ (g : G) (beta : Fin 2 → ℝ) (x : State),
    realPairingEnergy D (Ad g beta) (stateEquiv g x) =
      realPairingEnergy D beta x - cocycle g (Ad g beta)

variable (sys : CartanStatePermutationAction D)

theorem realGibbsKernel_covariance (g : G) (beta : Fin 2 → ℝ) (x : State) :
    realGibbsKernel D (sys.Ad g beta) (sys.stateEquiv g x) =
      realGibbsKernel D beta x * Real.exp (sys.cocycle g (sys.Ad g beta)) := by
  unfold realGibbsKernel
  rw [sys.pairing_cov g beta x]
  have h1 : -(realPairingEnergy D beta x - sys.cocycle g (sys.Ad g beta)) =
      -realPairingEnergy D beta x + sys.cocycle g (sys.Ad g beta) := by ring
  rw [h1, Real.exp_add]

theorem realGibbsPartition_covariance (g : G) (beta : Fin 2 → ℝ) :
    realGibbsPartition D (sys.Ad g beta) =
      realGibbsPartition D beta * Real.exp (sys.cocycle g (sys.Ad g beta)) := by
  unfold realGibbsPartition
  have h_sum : (∑ x : State, realGibbsKernel D (sys.Ad g beta) x) =
      ∑ x : State, realGibbsKernel D (sys.Ad g beta) (sys.stateEquiv g x) := by
    exact (Equiv.sum_comp (sys.stateEquiv g) (realGibbsKernel D (sys.Ad g beta))).symm
  rw [h_sum]
  simp_rw [realGibbsKernel_covariance D sys g beta]
  rw [← Finset.sum_mul]

theorem realGibbsWeight_invariance (g : G) (beta : Fin 2 → ℝ) (x : State) :
    realGibbsWeight D (sys.Ad g beta) (sys.stateEquiv g x) =
      realGibbsWeight D beta x := by
  unfold realGibbsWeight
  rw [realGibbsKernel_covariance D sys g beta x]
  rw [realGibbsPartition_covariance D sys g beta]
  have h_pos : 0 < Real.exp (sys.cocycle g (sys.Ad g beta)) := Real.exp_pos _
  rw [mul_div_mul_right _ _ (ne_of_gt h_pos)]

theorem souriauMassieu_covariance (g : G) (beta : Fin 2 → ℝ) :
    souriauMassieu D (sys.Ad g beta) =
      souriauMassieu D beta + sys.cocycle g (sys.Ad g beta) := by
  unfold souriauMassieu
  rw [realGibbsPartition_covariance D sys g beta]
  rw [Real.log_mul (ne_of_gt (realGibbsPartition_pos D beta)) (ne_of_gt (Real.exp_pos _))]
  rw [Real.log_exp]

/-- The concrete parameter-space action forms a valid Souriau Thermodynamic Action. -/
def toSouriauThermodynamicAction : SouriauThermodynamicAction G (Fin 2 → ℝ) where
  action := fun g => sys.Ad g
  cocycle := fun g => -sys.cocycle g
  Psi := fun beta => souriauMassieu D beta
  heatVector := fun beta => souriauChargeMeanFunctional D beta

-- Helper lemma for the transformation of the expected value of v
lemma expected_charge_transformation (g : G) (beta v : Fin 2 → ℝ) :
    (∑ i : Fin 2, (sys.Ad g v) i * souriauChargeMean D (sys.Ad g beta) i) =
      (∑ i : Fin 2, v i * souriauChargeMean D beta i) - sys.cocycle g (sys.Ad g v) := by
  have h_lhs : (∑ i : Fin 2, (sys.Ad g v) i * souriauChargeMean D (sys.Ad g beta) i) =
      ∑ x : State, realGibbsWeight D (sys.Ad g beta) x * (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap x i) := by
    unfold souriauChargeMean
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [← mul_assoc, mul_comm ((sys.Ad g v) _)]
  rw [h_lhs]
  have h_reindex : (∑ x : State, realGibbsWeight D (sys.Ad g beta) x * (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap x i)) =
      ∑ x : State, realGibbsWeight D (sys.Ad g beta) (sys.stateEquiv g x) * (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap (sys.stateEquiv g x) i) := by
    exact (Equiv.sum_comp (sys.stateEquiv g) _).symm
  rw [h_reindex]
  have h_weight : ∀ x, realGibbsWeight D (sys.Ad g beta) (sys.stateEquiv g x) = realGibbsWeight D beta x :=
    realGibbsWeight_invariance D sys g beta
  simp_rw [h_weight]
  have h_pairing : ∀ x, (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap (sys.stateEquiv g x) i) =
      (∑ i : Fin 2, v i * D.momentMap x i) - sys.cocycle g (sys.Ad g v) := by
    intro x
    exact sys.pairing_cov g v x
  simp_rw [h_pairing]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have h_one : (∑ x : State, realGibbsWeight D beta x * sys.cocycle g (sys.Ad g v)) = sys.cocycle g (sys.Ad g v) := by
    rw [← Finset.sum_mul]
    rw [realGibbsWeight_sum_eq_one D beta]
    ring
  rw [h_one]
  congr 1
  unfold souriauChargeMean
  calc
    ∑ x : State, realGibbsWeight D beta x * ∑ i : Fin 2, v i * D.momentMap x i
      = ∑ x : State, ∑ i : Fin 2, realGibbsWeight D beta x * (v i * D.momentMap x i) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
    _ = ∑ i : Fin 2, ∑ x : State, realGibbsWeight D beta x * (v i * D.momentMap x i) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin 2, v i * ∑ x : State, realGibbsWeight D beta x * D.momentMap x i := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          ∑ x : State, realGibbsWeight D beta x * (v i * D.momentMap x i)
            = ∑ x : State, v i * (realGibbsWeight D beta x * D.momentMap x i) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
          _ = v i * ∑ x : State, realGibbsWeight D beta x * D.momentMap x i := by
              rw [Finset.mul_sum]

/-- The Fisher metric (directional variance) transforms exactly tensorially under the group action,
without any anomaly, because the cocycle term cancels out of the squared difference. -/
theorem fisherSouriauQuadratic_covariance (g : G) (beta v : Fin 2 → ℝ) :
    fisherSouriauQuadratic D (sys.Ad g beta) (sys.Ad g v) = fisherSouriauQuadratic D beta v := by
  rw [fisherSouriauQuadratic_eq_directionalVariance D (sys.Ad g beta) (sys.Ad g v)]
  rw [fisherSouriauQuadratic_eq_directionalVariance D beta v]
  have h_reindex : (∑ x : State, realGibbsWeight D (sys.Ad g beta) x * (∑ i : Fin 2, (sys.Ad g v) i * (D.momentMap x i - souriauChargeMean D (sys.Ad g beta) i)) ^ 2) =
      ∑ x : State, realGibbsWeight D (sys.Ad g beta) (sys.stateEquiv g x) * (∑ i : Fin 2, (sys.Ad g v) i * (D.momentMap (sys.stateEquiv g x) i - souriauChargeMean D (sys.Ad g beta) i)) ^ 2 := by
    exact (Equiv.sum_comp (sys.stateEquiv g) _).symm
  rw [h_reindex]
  simp_rw [realGibbsWeight_invariance D sys g beta]
  apply Finset.sum_congr rfl
  intro x _
  congr 2
  have h_expand_LHS : (∑ i : Fin 2, (sys.Ad g v) i * (D.momentMap (sys.stateEquiv g x) i - souriauChargeMean D (sys.Ad g beta) i)) =
      (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap (sys.stateEquiv g x) i) - (∑ i : Fin 2, (sys.Ad g v) i * souriauChargeMean D (sys.Ad g beta) i) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [h_expand_LHS]
  have h_pair : (∑ i : Fin 2, (sys.Ad g v) i * D.momentMap (sys.stateEquiv g x) i) =
      (∑ i : Fin 2, v i * D.momentMap x i) - sys.cocycle g (sys.Ad g v) := sys.pairing_cov g v x
  rw [h_pair]
  rw [expected_charge_transformation D sys g beta v]
  have h_cancel : ((∑ i : Fin 2, v i * D.momentMap x i) - sys.cocycle g (sys.Ad g v)) -
      ((∑ i : Fin 2, v i * souriauChargeMean D beta i) - sys.cocycle g (sys.Ad g v)) =
      (∑ i : Fin 2, v i * D.momentMap x i) - (∑ i : Fin 2, v i * souriauChargeMean D beta i) := by
    ring
  rw [h_cancel]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end InfoGeometry.Canonical
