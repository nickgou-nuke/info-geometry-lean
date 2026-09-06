import InfoGeometry.Basic
import InfoGeometry.ExponentialFamily.Class

/-!
# Finite Exponential Family

Core definitions and theorems for finite exponential families, using the ExponentialFamily typeclass abstraction.

## Main results
- `FiniteExponentialFamily` typeclass instance
- `partition`, `logPartition`, `statMean` as typeclass projections
- ...

## Warning
If `F.base.prob x = 0` for some `x`, then `Real.log (F.base.prob x)` is defined as 0 in Lean, but mathematically this should be −∞. Analytic theorems (e.g., differentiability) may require strict positivity of the base measure.

-/

namespace InfoGeometry.ExponentialFamily

open Finset

/--
  General finite exponential family as an instance of the ExponentialFamily typeclass.
  Given a base measure `P` and sufficient statistic `stat`, the density is:
    P.prob x * exp(θ * stat x) / partition(θ)
  where partition(θ) = ∑ x, P.prob x * exp(θ * stat x)
  The exponential identity uses log P.prob x in the statistic.
  WARNING: If `P.prob x = 0`, then `log 0 = 0` in Lean, but mathematically this should be −∞.
-/
structure FiniteExponentialFamilyData (α : Type) [Fintype α] where
  base : ProbabilityDist α
  stat : α → ℝ
  base_pos : ∀ x, 0 < base.prob x

variable {α : Type} [Fintype α]

noncomputable def partition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  ∑ x, F.base.prob x * Real.exp (θ * F.stat x)

noncomputable def logPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  Real.log (partition F θ)

noncomputable def statistic (F : FiniteExponentialFamilyData α) (x : α) (θ : ℝ) : ℝ :=
  θ * F.stat x + Real.log (F.base.prob x)

noncomputable def density (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) : ℝ :=
  F.base.prob x * Real.exp (θ * F.stat x) / partition F θ

lemma partition_pos (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    0 < partition F θ := by
  unfold partition
  have hnonneg :
      ∀ y ∈ (Finset.univ : Finset α),
        0 ≤ F.base.prob y * Real.exp (θ * F.stat y) := by
    intro y hy
    exact mul_nonneg (le_of_lt (F.base_pos y)) (le_of_lt (Real.exp_pos _))
  have hsum_ne_zero : (∑ y, F.base.prob y) ≠ 0 := by
    simp [F.base.sum_one]
  have hsum_univ_ne_zero :
      ∑ y ∈ (Finset.univ : Finset α), F.base.prob y ≠ 0 := by
    simpa using hsum_ne_zero
  rcases Finset.exists_ne_zero_of_sum_ne_zero
      (s := (Finset.univ : Finset α))
      (f := fun y => F.base.prob y)
      hsum_univ_ne_zero with ⟨y, hy, _hy_ne⟩
  have hpos_witness :
      ∃ y ∈ (Finset.univ : Finset α),
        0 < F.base.prob y * Real.exp (θ * F.stat y) := by
    exact ⟨y, hy, mul_pos (F.base_pos y) (Real.exp_pos _)⟩
  have hpos' :
      0 < ∑ y ∈ (Finset.univ : Finset α), F.base.prob y * Real.exp (θ * F.stat y) := by
    exact Finset.sum_pos' hnonneg hpos_witness
  simpa using hpos'

lemma density_eq (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    density F θ x = Real.exp (statistic F x θ - logPartition F θ) := by
  unfold density statistic logPartition partition
  rw [Real.exp_sub, Real.exp_add]
  have hZpos : 0 < ∑ y, F.base.prob y * Real.exp (θ * F.stat y) := by
    simpa [partition] using partition_pos F θ
  rw [Real.exp_log hZpos, Real.exp_log (F.base_pos x)]
  field_simp [ne_of_gt hZpos, ne_of_gt (F.base_pos x)]

lemma normalization (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    ∑ x, density F θ x = 1 := by
  unfold density partition
  have hZpos : 0 < ∑ y, F.base.prob y * Real.exp (θ * F.stat y) := by
    simpa [partition] using partition_pos F θ
  have hZne : (∑ y, F.base.prob y * Real.exp (θ * F.stat y)) ≠ 0 := ne_of_gt hZpos
  calc
    ∑ x, F.base.prob x * Real.exp (θ * F.stat x) / ∑ y, F.base.prob y * Real.exp (θ * F.stat y)
        = (∑ x, F.base.prob x * Real.exp (θ * F.stat x)) /
            ∑ y, F.base.prob y * Real.exp (θ * F.stat y) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun x => F.base.prob x * Real.exp (θ * F.stat x))
                (a := ∑ y, F.base.prob y * Real.exp (θ * F.stat y)))
    _ = 1 := by
          exact div_self hZne

/--
  Instance: any FiniteExponentialFamilyData gives a FiniteExponentialFamily in the typeclass sense.
-/
noncomputable instance (F : FiniteExponentialFamilyData α) :
    FiniteExponentialFamily α ℝ where
  statistic := statistic F
  logPartition := logPartition F
  density := density F
  density_eq := density_eq F
  normalization := normalization F

end InfoGeometry.ExponentialFamily
