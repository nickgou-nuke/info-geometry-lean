import InfoGeometry.ExponentialFamily.Finite
import InfoGeometry.Potential.LogPotential

/-!
# KL–Bregman Bridge (Finite Exponential Family)

Algebraic bridge between parameterized KL divergence and Bregman divergence
of the log-partition potential, with a derivative-mean compatibility hypothesis.
-/

namespace InfoGeometry.ExponentialFamily

open scoped BigOperators

variable {α : Type _} [Fintype α]

/-- Mean of the sufficient statistic under parameter `θ`. -/
noncomputable def statMean
    (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  ∑ x, density F θ x * F.stat x

/-- Parameterized KL divergence `KL(P_θ || P_η)` for a finite exponential family. -/
noncomputable def KLParam
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) : ℝ :=
  ∑ x, density F θ x *
    (Real.log (density F θ x) - Real.log (density F η x))

/-- Exponential-family log-partition viewed as a `LogPotential`. -/
noncomputable def logPotential
    (F : FiniteExponentialFamilyData α) : InfoGeometry.LogPotential ℝ where
  ψ := logPartition F

lemma log_density_eq
    (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    Real.log (density F θ x) = statistic F x θ - logPartition F θ := by
  rw [density_eq]
  simp

lemma KLParam_eq
    (F : FiniteExponentialFamilyData α) (θ η : ℝ) :
    KLParam F θ η
      =
      (θ - η) * statMean F θ
        - (logPartition F θ - logPartition F η) := by
  unfold KLParam statMean
  calc
    ∑ x, density F θ x *
        (Real.log (density F θ x) - Real.log (density F η x))
      =
      ∑ x, density F θ x *
        (((θ - η) * F.stat x) - (logPartition F θ - logPartition F η)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [log_density_eq, log_density_eq]
          unfold statistic
          ring
    _ =
      ∑ x, ((θ - η) * (density F θ x * F.stat x)
        - (logPartition F θ - logPartition F η) * density F θ x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ =
      (θ - η) * (∑ x, density F θ x * F.stat x)
        - (logPartition F θ - logPartition F η) * (∑ x, density F θ x) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ =
      (θ - η) * statMean F θ
        - (logPartition F θ - logPartition F η) := by
          rw [show (∑ x, density F θ x * F.stat x) = statMean F θ by rfl]
          rw [normalization F θ]
          ring

/-- KL equals Bregman divergence of the log-partition potential,
assuming the standard derivative-mean identity `ψ'(θ) = E_θ[T]`. -/
lemma KLParam_eq_LogPotential_bregman_of_statMean_eq_deriv
    (F : FiniteExponentialFamilyData α)
    (θ η : ℝ)
    (hmean : statMean F θ = deriv (logPartition F) θ) :
    KLParam F θ η = (logPotential F).bregman η θ := by
  rw [KLParam_eq]
  rw [hmean]
  unfold InfoGeometry.LogPotential.bregman logPotential
  unfold InfoGeometry.bregmanDiv
  ring

end InfoGeometry.ExponentialFamily
