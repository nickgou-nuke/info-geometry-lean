import InfoGeometry.Basic
import InfoGeometry.ExponentialFamily.Class

/-!
# Finite Exponential Family

Core definitions and theorems for finite exponential families, using the ExponentialFamily typeclass abstraction.

## Main results
- explicit family maps `familyPartition`, `familyLogPartition`, `familyStatistic`, `familyDensity`
- conversion `toFiniteExponentialFamily`
- ...

## Warning
This structure assumes strict positivity `base_pos : ∀ x, 0 < (base x).toReal`,
so `Real.log ((F.base x).toReal)` is always taken at a positive value.

-/

namespace InfoGeometry.ExponentialFamily

open Finset

/--
  General finite exponential family as an instance of the ExponentialFamily typeclass.
  Given a base measure `P` and sufficient statistic `stat`, the density is:
    P x * exp(θ * stat x) / partition(θ)
  where partition(θ) = ∑ x, P x * exp(θ * stat x)
  The exponential identity uses `log (P x)` in the statistic.
  This data structure includes strict positivity `base_pos`, so this log is always at a positive value.
-/
structure FiniteExponentialFamilyData (α : Type _) [Fintype α] where
  base : ProbabilityDist α
  stat : α → ℝ
  base_pos : ∀ x, 0 < (base x).toReal

variable {α : Type _} [Fintype α]

noncomputable def familyPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  ∑ x, (F.base x).toReal * Real.exp (θ * F.stat x)

noncomputable def familyLogPartition (F : FiniteExponentialFamilyData α) (θ : ℝ) : ℝ :=
  Real.log (familyPartition F θ)

noncomputable def familyStatistic (F : FiniteExponentialFamilyData α) (x : α) (θ : ℝ) : ℝ :=
  θ * F.stat x + Real.log ((F.base x).toReal)

noncomputable def familyDensity (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) : ℝ :=
  (F.base x).toReal * Real.exp (θ * F.stat x) / familyPartition F θ

section Nonempty

variable [Nonempty α]

lemma familyPartition_pos (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    0 < familyPartition F θ := by
  classical
  unfold familyPartition
  have hnonneg :
      ∀ y ∈ (Finset.univ : Finset α),
        0 ≤ (F.base y).toReal * Real.exp (θ * F.stat y) := by
    intro y hy
    exact mul_nonneg (le_of_lt (F.base_pos y)) (le_of_lt (Real.exp_pos _))
  obtain ⟨y, hy⟩ := (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty)
  have hpos_sorry :
      ∃ y ∈ (Finset.univ : Finset α),
        0 < (F.base y).toReal * Real.exp (θ * F.stat y) := by
    exact ⟨y, hy, mul_pos (F.base_pos y) (Real.exp_pos _)⟩
  have hpos' :
      0 < ∑ y ∈ (Finset.univ : Finset α), (F.base y).toReal * Real.exp (θ * F.stat y) := by
    exact Finset.sum_pos' hnonneg hpos_sorry
  simpa using hpos'

lemma familyDensity_eq (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    familyDensity F θ x = Real.exp (familyStatistic F x θ - familyLogPartition F θ) := by
  unfold familyDensity familyStatistic familyLogPartition familyPartition
  rw [Real.exp_sub, Real.exp_add]
  have hZpos : 0 < ∑ y, (F.base y).toReal * Real.exp (θ * F.stat y) := by
    simpa [familyPartition] using familyPartition_pos F θ
  rw [Real.exp_log hZpos, Real.exp_log (F.base_pos x)]
  field_simp [ne_of_gt hZpos, ne_of_gt (F.base_pos x)]

lemma familyDensity_pos (F : FiniteExponentialFamilyData α) (θ : ℝ) (x : α) :
    0 < familyDensity F θ x := by
  unfold familyDensity
  refine div_pos ?_ (familyPartition_pos F θ)
  exact mul_pos (F.base_pos x) (Real.exp_pos _)

lemma familyNormalization (F : FiniteExponentialFamilyData α) (θ : ℝ) :
    ∑ x, familyDensity F θ x = 1 := by
  unfold familyDensity familyPartition
  have hZpos : 0 < ∑ y, (F.base y).toReal * Real.exp (θ * F.stat y) := by
    simpa [familyPartition] using familyPartition_pos F θ
  have hZne : (∑ y, (F.base y).toReal * Real.exp (θ * F.stat y)) ≠ 0 := ne_of_gt hZpos
  calc
    ∑ x, (F.base x).toReal * Real.exp (θ * F.stat x) / ∑ y, (F.base y).toReal * Real.exp (θ * F.stat y)
        = (∑ x, (F.base x).toReal * Real.exp (θ * F.stat x)) /
            ∑ y, (F.base y).toReal * Real.exp (θ * F.stat y) := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset α))
                (f := fun x => (F.base x).toReal * Real.exp (θ * F.stat x))
                (a := ∑ y, (F.base y).toReal * Real.exp (θ * F.stat y)))
    _ = 1 := by
          exact div_self hZne

/--
  Bundle a concrete finite exponential family as `FiniteExponentialFamily`.
-/
noncomputable def toFiniteExponentialFamily (F : FiniteExponentialFamilyData α) :
    FiniteExponentialFamily α ℝ where
  statistic := familyStatistic F
  logPartition := familyLogPartition F
  density := familyDensity F
  density_eq := familyDensity_eq F
  normalization := familyNormalization F

end Nonempty

end InfoGeometry.ExponentialFamily
