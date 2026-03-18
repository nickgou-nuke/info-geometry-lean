import InfoGeometry.ExponentialFamily.Finite
import InfoGeometry.Potential.LogPotential
set_option linter.unusedSectionVars false

/-!
# KL–Bregman Bridge (Finite Exponential Family)

Algebraic bridge between parameterized KL divergence and Bregman divergence
of the log-partition potential, with a derivative-mean compatibility hypothesis.
-/

namespace InfoGeometry.ExponentialFamily

open scoped BigOperators

variable {α : Type _} [Fintype α] [Nonempty α]

/-- Mean of the sufficient statistic under parameter `θ`. -/
noncomputable def statMean
    (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  ∑ x, familyDensity F θ x * F.stat x

/-- Parameterized KL divergence `KL(P_θ || P_η)` for a finite exponential family. -/
noncomputable def KLParam
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) : ℝ :=
  ∑ x, familyDensity F θ x *
    (Real.log (familyDensity F θ x) - Real.log (familyDensity F η x))

/-! ### Optimal-Transport Naming Bridge -/

/-- OT naming alias for the regularized transport objective in natural parameters. -/
noncomputable abbrev entropicTransportObjective
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) : ℝ :=
  KLParam F θ η

/-- Exponential-family log-partition viewed as a `LogPotential`. -/
noncomputable def logPotential
    (F : FiniteExponentialFamilyData α) : InfoGeometry.LogPotential ℝ where
  ψ := familyLogPartition F

/-- OT naming alias for the convex potential gap driving the same objective. -/
noncomputable abbrev entropicTransportPotentialGap
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) : ℝ :=
  (logPotential F).bregman η θ

@[simp] lemma entropicTransportObjective_eq
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    entropicTransportObjective F θ η = KLParam F θ η := rfl

@[simp] lemma entropicTransportPotentialGap_eq
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    entropicTransportPotentialGap F θ η = (logPotential F).bregman η θ := rfl

lemma log_density_eq
    (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    Real.log (familyDensity F θ x) = familyStatistic F x θ - familyLogPartition F θ := by
  have hpos : 0 < familyDensity F θ x := familyDensity_pos F θ x
  apply Real.exp_injective
  calc
    Real.exp (Real.log (familyDensity F θ x))
        = familyDensity F θ x := Real.exp_log hpos
    _ = Real.exp (familyStatistic F x θ - familyLogPartition F θ) := by
          rw [familyDensity_eq]

lemma KLParam_eq
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    KLParam F θ η
      =
      (θ - η) * statMean F θ
        - (familyLogPartition F θ - familyLogPartition F η) := by
  unfold KLParam statMean
  calc
    ∑ x, familyDensity F θ x *
        (Real.log (familyDensity F θ x) - Real.log (familyDensity F η x))
      =
      ∑ x, familyDensity F θ x *
        (((θ - η) * F.stat x) - (familyLogPartition F θ - familyLogPartition F η)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [log_density_eq, log_density_eq]
          unfold familyStatistic
          ring
    _ =
      ∑ x, ((θ - η) * (familyDensity F θ x * F.stat x)
        - (familyLogPartition F θ - familyLogPartition F η) * familyDensity F θ x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ =
      (θ - η) * (∑ x, familyDensity F θ x * F.stat x)
        - (familyLogPartition F θ - familyLogPartition F η) * (∑ x, familyDensity F θ x) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ =
      (θ - η) * statMean F θ
        - (familyLogPartition F θ - familyLogPartition F η) := by
          rw [show (∑ x, familyDensity F θ x * F.stat x) = statMean F θ by rfl]
          rw [familyNormalization F θ]
          ring

lemma KLParam_self (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    KLParam F θ θ = 0 := by
  rw [KLParam_eq]
  ring

/-- KL equals Bregman divergence of the log-partition potential,
assuming the standard derivative-mean identity `ψ'(θ) = E_θ[T]`. -/
lemma KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv
    (F : FiniteExponentialFamilyData α)
    (θ η : ℝ)
    (hmean : statMean F θ = deriv (familyLogPartition F) θ) :
    KLParam F θ η = (logPotential F).bregman η θ := by
  rw [KLParam_eq]
  rw [hmean]
  unfold InfoGeometry.LogPotential.bregman logPotential
  unfold InfoGeometry.bregmanDiv
  ring

lemma KLParam_eq_bregman_if_deriv_mean
    (F : FiniteExponentialFamilyData α)
    (hmean : ∀ t, statMean F t = deriv (familyLogPartition F) t)
    (θ η : ℝ) :
    KLParam F θ η = (logPotential F).bregman η θ := by
  exact KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv
    (F := F) θ η (hmean θ)

lemma entropicTransportObjective_eq_potentialGap_if_deriv_mean
    (F : FiniteExponentialFamilyData α)
    (hmean : ∀ t, statMean F t = deriv (familyLogPartition F) t)
    (θ η : ℝ) :
    entropicTransportObjective F θ η = entropicTransportPotentialGap F θ η := by
  simpa [entropicTransportObjective, entropicTransportPotentialGap] using
    (KLParam_eq_bregman_if_deriv_mean (F := F) hmean θ η)

end InfoGeometry.ExponentialFamily
