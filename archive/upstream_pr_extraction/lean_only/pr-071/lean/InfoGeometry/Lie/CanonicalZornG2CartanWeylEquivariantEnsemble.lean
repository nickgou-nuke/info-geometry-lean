import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
import InfoGeometry.Lie.CanonicalZornG2CartanSouriauMassieu
import InfoGeometry.Lie.CanonicalZornG2CartanFisherSouriauMetric

noncomputable section

open InfoGeometry.Lie
open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open scoped BigOperators

namespace InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble

variable {State W : Type*} [Fintype State] [Nonempty State] [Group W]

class WeylEquivariantEnsembleDatum (State W : Type*) [Fintype State]
    [Nonempty State] [Group W] where
  base : CartanSouriauDatum State
  stateAction : W →* Equiv.Perm State
  chargeAction : W →* (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)
  parameterTransport : W →* (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)
  moment_equivariance (w : W) (m : State) :
    base.momentMap (stateAction w m) = chargeAction w (base.momentMap m)
  pairing_diagonal_invariant (w : W) (v : Fin 2 → ℝ) (m : State) :
    (∑ i, parameterTransport w⁻¹ v i * base.momentMap (stateAction w m) i) =
      (∑ i, v i * base.momentMap m i)

instance [D : WeylEquivariantEnsembleDatum State W] : MulAction W State where
  smul w s := D.stateAction w s
  one_smul s := by exact Equiv.ext_iff.mp (map_one D.stateAction) s
  mul_smul w₁ w₂ s := by exact Equiv.ext_iff.mp (map_mul D.stateAction w₁ w₂) s

variable [D : WeylEquivariantEnsembleDatum State W]

def parameterLeftAction (w : W) (beta : Fin 2 → ℝ) : Fin 2 → ℝ :=
  D.parameterTransport w⁻¹ beta

theorem energy_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realPairingEnergy D.base (parameterLeftAction (D := D) w beta) (w • m) =
      realPairingEnergy D.base beta m := by
  unfold realPairingEnergy parameterLeftAction
  exact D.pairing_diagonal_invariant w beta m

theorem unnormalizedWeight_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realGibbsKernel D.base (parameterLeftAction (D := D) w beta) (w • m) =
      realGibbsKernel D.base beta m := by
  unfold realGibbsKernel
  rw [energy_diagonal_invariant (D := D) w beta m]

theorem partition_invariance (w : W) (beta : Fin 2 → ℝ) :
    realGibbsPartition D.base (parameterLeftAction (D := D) w beta) =
      realGibbsPartition D.base beta := by
  unfold realGibbsPartition
  rw [← Equiv.sum_comp (D.stateAction w)]
  apply Finset.sum_congr rfl
  intro m _
  exact unnormalizedWeight_diagonal_invariant (D := D) w beta m

theorem probability_diagonal_invariant (w : W) (beta : Fin 2 → ℝ) (m : State) :
    realGibbsWeight D.base (parameterLeftAction (D := D) w beta) (w • m) =
      realGibbsWeight D.base beta m := by
  unfold realGibbsWeight
  rw [unnormalizedWeight_diagonal_invariant (D := D) w beta m,
    partition_invariance (D := D) w beta]

theorem massieu_invariance (w : W) (beta : Fin 2 → ℝ) :
    souriauMassieu D.base (parameterLeftAction (D := D) w beta) =
      souriauMassieu D.base beta := by
  unfold souriauMassieu
  rw [partition_invariance (D := D) w beta]

def expectedDirectionalCharge (beta v : Fin 2 → ℝ) : ℝ :=
  ∑ m, realGibbsWeight D.base beta m *
    (∑ i, v i * D.base.momentMap m i)

theorem expectedDirectionalCharge_covariance (w : W) (beta v : Fin 2 → ℝ) :
    expectedDirectionalCharge (D := D) (parameterLeftAction (D := D) w beta)
        (parameterLeftAction (D := D) w v) =
      expectedDirectionalCharge (D := D) beta v := by
  unfold expectedDirectionalCharge
  rw [← Equiv.sum_comp (D.stateAction w)]
  apply Finset.sum_congr rfl
  intro m _
  have hp : realGibbsWeight D.base (parameterLeftAction (D := D) w beta)
      (D.stateAction w m) = realGibbsWeight D.base beta m := by
    simpa using probability_diagonal_invariant (D := D) w beta m
  rw [hp]
  have hpair : (∑ i, parameterLeftAction (D := D) w v i *
      D.base.momentMap (D.stateAction w m) i) =
      ∑ i, v i * D.base.momentMap m i := by
    exact D.pairing_diagonal_invariant w v m
  rw [hpair]

def centeredDirectionalCharge (beta v : Fin 2 → ℝ) (m : State) : ℝ :=
  (∑ i, v i * D.base.momentMap m i) - expectedDirectionalCharge (D := D) beta v

theorem centeredDirectionalCharge_covariance (w : W) (beta v : Fin 2 → ℝ) (m : State) :
    centeredDirectionalCharge (D := D) (parameterLeftAction (D := D) w beta)
        (parameterLeftAction (D := D) w v) (w • m) =
      centeredDirectionalCharge (D := D) beta v m := by
  change (∑ i, D.parameterTransport w⁻¹ v i *
      D.base.momentMap (D.stateAction w m) i) -
        expectedDirectionalCharge (D := D)
          (parameterLeftAction (D := D) w beta)
          (parameterLeftAction (D := D) w v) =
      (∑ i, v i * D.base.momentMap m i) -
        expectedDirectionalCharge (D := D) beta v
  rw [D.pairing_diagonal_invariant w v m,
    expectedDirectionalCharge_covariance (D := D) w beta v]

def fisherSouriauBilinear (beta u v : Fin 2 → ℝ) : ℝ :=
  ∑ m, realGibbsWeight D.base beta m *
    centeredDirectionalCharge (D := D) beta u m *
    centeredDirectionalCharge (D := D) beta v m

theorem fisherSouriau_covariance (w : W) (beta u v : Fin 2 → ℝ) :
    fisherSouriauBilinear (D := D) (parameterLeftAction (D := D) w beta)
        (parameterLeftAction (D := D) w u) (parameterLeftAction (D := D) w v) =
      fisherSouriauBilinear (D := D) beta u v := by
  unfold fisherSouriauBilinear
  rw [← Equiv.sum_comp (D.stateAction w)]
  apply Finset.sum_congr rfl
  intro m _
  have hp : realGibbsWeight D.base (parameterLeftAction (D := D) w beta)
      (D.stateAction w m) = realGibbsWeight D.base beta m := by
    simpa using probability_diagonal_invariant (D := D) w beta m
  have hu : centeredDirectionalCharge (D := D)
      (parameterLeftAction (D := D) w beta)
      (parameterLeftAction (D := D) w u) (D.stateAction w m) =
      centeredDirectionalCharge (D := D) beta u m := by
    simpa using centeredDirectionalCharge_covariance (D := D) w beta u m
  have hv : centeredDirectionalCharge (D := D)
      (parameterLeftAction (D := D) w beta)
      (parameterLeftAction (D := D) w v) (D.stateAction w m) =
      centeredDirectionalCharge (D := D) beta v m := by
    simpa using centeredDirectionalCharge_covariance (D := D) w beta v m
  rw [hp, hu, hv]

theorem fisherSouriauQuadratic_covariance (w : W) (beta v : Fin 2 → ℝ) :
    fisherSouriauBilinear (D := D) (parameterLeftAction (D := D) w beta)
        (parameterLeftAction (D := D) w v) (parameterLeftAction (D := D) w v) =
      fisherSouriauBilinear (D := D) beta v v := by
  exact fisherSouriau_covariance (D := D) w beta v v

theorem fisherSouriauBilinear_diag_eq_fisherSouriauQuadratic
    (beta v : Fin 2 → ℝ) :
    fisherSouriauBilinear (D := D) beta v v =
      fisherSouriauQuadratic D.base beta v := by
  have hmean : expectedDirectionalCharge (D := D) beta v =
      ∑ i, v i * souriauChargeMean D.base beta i := by
    unfold expectedDirectionalCharge souriauChargeMean
    calc
      ∑ m, realGibbsWeight D.base beta m *
          (∑ i, v i * D.base.momentMap m i) =
        ∑ m, ∑ i, realGibbsWeight D.base beta m *
          (v i * D.base.momentMap m i) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.mul_sum]
      _ = ∑ i, ∑ m, realGibbsWeight D.base beta m *
          (v i * D.base.momentMap m i) := by
            rw [Finset.sum_comm]
      _ = ∑ i, v i * ∑ m, realGibbsWeight D.base beta m *
          D.base.momentMap m i := by
            apply Finset.sum_congr rfl
            intro i hi
            calc
              ∑ m, realGibbsWeight D.base beta m *
                  (v i * D.base.momentMap m i) =
                ∑ m, v i *
                  (realGibbsWeight D.base beta m * D.base.momentMap m i) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    ring
              _ = v i * ∑ m, realGibbsWeight D.base beta m *
                  D.base.momentMap m i := by
                    rw [Finset.mul_sum]
      _ = ∑ i, v i * souriauChargeMean D.base beta i := by
            rfl
  unfold fisherSouriauBilinear centeredDirectionalCharge
  rw [hmean, fisherSouriauQuadratic_eq_directionalVariance]
  apply Finset.sum_congr rfl
  intro m _
  have hinner :
      (∑ i, v i * D.base.momentMap m i -
          ∑ i, v i * souriauChargeMean D.base beta i) =
        ∑ i, v i *
          (D.base.momentMap m i - souriauChargeMean D.base beta i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinner]
  ring

theorem fisherSouriau_massieu_coherence (beta v : Fin 2 → ℝ) :
    deriv (fun t => deriv
      (fun t' => souriauMassieu D.base (betaLine beta v t')) t) 0 =
      fisherSouriauBilinear (D := D) beta v v := by
  rw [souriauMassieu_directionalSecondDeriv_eq_fisherSouriauQuadratic]
  exact (fisherSouriauBilinear_diag_eq_fisherSouriauQuadratic
    (D := D) beta v).symm

end InfoGeometry.Lie.CanonicalZornG2CartanWeylEquivariantEnsemble
