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

omit [Fintype State] [Nonempty State] in
theorem realGibbsKernel_covariance (g : G) (beta : Fin 2 → ℝ) (x : State) :
    realGibbsKernel D (sys.Ad g beta) (sys.stateEquiv g x) =
      realGibbsKernel D beta x * Real.exp (sys.cocycle g (sys.Ad g beta)) := by
  unfold realGibbsKernel
  rw [sys.pairing_cov g beta x]
  have h1 : -(realPairingEnergy D beta x - sys.cocycle g (sys.Ad g beta)) =
      -realPairingEnergy D beta x + sys.cocycle g (sys.Ad g beta) := by ring
  rw [h1, Real.exp_add]

omit [Nonempty State] in
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

omit [Nonempty State] in
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
  action := ⟨sys.Ad⟩
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

theorem heatVector_pairing_covariance (g : G) (beta v : Fin 2 → ℝ) :
    (toSouriauThermodynamicAction D sys).heatVector (sys.Ad g beta)
        (sys.Ad g v) =
      (toSouriauThermodynamicAction D sys).heatVector beta v -
        sys.cocycle g (sys.Ad g v) := by
  change souriauChargeMeanFunctional D (sys.Ad g beta) (sys.Ad g v) =
    souriauChargeMeanFunctional D beta v - sys.cocycle g (sys.Ad g v)
  rw [souriauChargeMeanFunctional_apply]
  rw [souriauChargeMeanFunctional_apply]
  calc
    (∑ i : Fin 2, souriauChargeMean D (sys.Ad g beta) i * (sys.Ad g v) i) =
        ∑ i : Fin 2, (sys.Ad g v) i * souriauChargeMean D (sys.Ad g beta) i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i : Fin 2, v i * souriauChargeMean D beta i) -
        sys.cocycle g (sys.Ad g v) := expected_charge_transformation D sys g beta v
    _ = (∑ i : Fin 2, souriauChargeMean D beta i * v i) -
        sys.cocycle g (sys.Ad g v) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

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

/-!
## Bilinear Fisher--Souriau readout

The quadratic covariance theorem above is the primary finite result.  The
bilinear form is recovered by polarization, so its covariance does not need a
second probabilistic reindexing proof.
-/

def souriauFisherBilinear (beta u v : Fin 2 → ℝ) : ℝ :=
  (fisherSouriauQuadratic D beta (u + v) -
    fisherSouriauQuadratic D beta u -
    fisherSouriauQuadratic D beta v) / 2

omit [Nonempty State] in
theorem fisherSouriauQuadratic_smul
    (beta v : Fin 2 → ℝ) (c : ℝ) :
    fisherSouriauQuadratic D beta (c • v) =
      c ^ (2 : ℕ) * fisherSouriauQuadratic D beta v := by
  unfold fisherSouriauQuadratic
  simp only [Pi.smul_apply]
  simp only [smul_eq_mul]
  calc
    (∑ x, ∑ x_1, c * v x * fisherSouriauMatrix D beta x x_1 *
        (c * v x_1)) =
        ∑ x, ∑ x_1, c ^ 2 *
          (v x * fisherSouriauMatrix D beta x x_1 * v x_1) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x_1 _
      ring
    _ = ∑ x, c ^ 2 * ∑ x_1,
        v x * fisherSouriauMatrix D beta x x_1 * v x_1 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    _ = c ^ 2 * ∑ x, ∑ x_1,
        v x * fisherSouriauMatrix D beta x x_1 * v x_1 := by
      rw [Finset.mul_sum]

omit [Nonempty State] in
theorem souriauFisherBilinear_diag (beta v : Fin 2 → ℝ) :
    souriauFisherBilinear D beta v v = fisherSouriauQuadratic D beta v := by
  unfold souriauFisherBilinear
  rw [show v + v = (2 : ℝ) • v by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  rw [fisherSouriauQuadratic_smul]
  ring

omit [Nonempty State] in
theorem souriauFisherBilinear_symmetric (beta u v : Fin 2 → ℝ) :
    souriauFisherBilinear D beta u v = souriauFisherBilinear D beta v u := by
  unfold souriauFisherBilinear
  rw [add_comm]
  ring

theorem souriauFisherBilinear_covariance
    (g : G) (beta u v : Fin 2 → ℝ) :
    souriauFisherBilinear D (sys.Ad g beta) (sys.Ad g u) (sys.Ad g v) =
      souriauFisherBilinear D beta u v := by
  unfold souriauFisherBilinear
  rw [← map_add]
  rw [fisherSouriauQuadratic_covariance D sys g beta (u + v)]
  rw [fisherSouriauQuadratic_covariance D sys g beta u]
  rw [fisherSouriauQuadratic_covariance D sys g beta v]

/-!
## Massieu/Fisher coherence

The directional Massieu Hessian is already owned by the finite Cartan
Fisher--Souriau metric layer.  This theorem packages that analytic readout
with the concrete polarized bilinear form above, without differentiating the
Weyl or state action again.
-/

theorem souriauFisher_massieu_coherence (beta v : Fin 2 → ℝ) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D (betaLine beta v t')) t) 0 =
      souriauFisherBilinear D beta v v := by
  rw [souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic]
  exact (souriauFisherBilinear_diag D beta v).symm

end InfoGeometry.Canonical
