import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace InfoGeometry.Information

variable {α : Type _} [Fintype α]
open Finset

/-- Finite exponential-family data with vector-valued sufficient statistic. -/
structure FiniteExpFamily (d : ℕ) where
  stat : α → Fin d → ℝ
  base : α → ℝ
  base_pos : ∀ x, 0 < base x

/-- Natural parameter pairing `⟨θ, stat(x)⟩`. -/
noncomputable def naturalParam
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (x : α) : ℝ :=
  ∑ i, θ i * F.stat x i

/-- Partition function for the finite exponential family. -/
noncomputable def partition
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) : ℝ :=
  ∑ x, Real.exp (naturalParam F θ x) * F.base x

lemma partition_pos
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    [Nonempty α] :
    0 < partition F θ := by
  classical
  unfold partition
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset α))
      (f := fun x => Real.exp (naturalParam F θ x) * F.base x)
      (by
        intro x hx
        exact mul_pos (Real.exp_pos _) (F.base_pos x))
      Finset.univ_nonempty)

/-- Log-partition function `ψ(θ)` for finite exponential families. -/
noncomputable def logPartition
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) : ℝ :=
  Real.log (partition F θ)

/-- Normalized model density at parameter `θ`. -/
noncomputable def density
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (x : α) : ℝ :=
  Real.exp (naturalParam F θ x) * F.base x / partition F θ

lemma density_nonneg
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (x : α)
    [Nonempty α] :
    0 ≤ density F θ x := by
  unfold density
  exact div_nonneg
    (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (F.base_pos x)))
    (le_of_lt (partition_pos F θ))

lemma density_pos
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (x : α)
    [Nonempty α] :
    0 < density F θ x := by
  unfold density
  exact div_pos
    (mul_pos (Real.exp_pos _) (F.base_pos x))
    (partition_pos F θ)

lemma density_sum_one
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    [Nonempty α] :
    ∑ x, density F θ x = 1 := by
  unfold density partition
  have hZne :
      (∑ y : α, Real.exp (naturalParam F θ y) * F.base y) ≠ 0 :=
    ne_of_gt (partition_pos F θ)
  calc
    ∑ x : α, Real.exp (naturalParam F θ x) * F.base x /
        ∑ y : α, Real.exp (naturalParam F θ y) * F.base y
      = (∑ x : α, Real.exp (naturalParam F θ x) * F.base x) /
          ∑ y : α, Real.exp (naturalParam F θ y) * F.base y := by
          symm
          simpa using
            (Finset.sum_div
              (s := (Finset.univ : Finset α))
              (f := fun x : α => Real.exp (naturalParam F θ x) * F.base x)
              (a := ∑ y : α, Real.exp (naturalParam F θ y) * F.base y))
    _ = 1 := by exact div_self hZne

/-- Expectation under the exponential-family model at parameter `θ`. -/
noncomputable def expectation
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (f : α → ℝ) : ℝ :=
  ∑ x, density F θ x * f x

/-- Mean of statistic component `i`. -/
noncomputable def statMean
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (i : Fin d) : ℝ :=
  expectation F θ (fun x => F.stat x i)

/-- Centered statistic component. -/
noncomputable def centeredStat
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (i : Fin d)
    (x : α) : ℝ :=
  F.stat x i - statMean F θ i

/-- Covariance matrix entry of statistic components `(i,j)`. -/
noncomputable def covariance
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  expectation F θ (fun x => centeredStat F θ i x * centeredStat F θ j x)

/-- Fisher metric in natural coordinates (covariance form). -/
noncomputable def fisherMetric
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (i j : Fin d) : ℝ :=
  covariance F θ i j

/-- Linear statistic associated with direction `v`. -/
noncomputable def linearStat
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (v : Fin d → ℝ)
    (x : α) : ℝ :=
  ∑ i, v i * F.stat x i

/-- Centered linear statistic associated with direction `v`. -/
noncomputable def centeredLinearStat
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (v : Fin d → ℝ)
    (x : α) : ℝ :=
  linearStat F v x - expectation F θ (linearStat F v)

/-- Fisher quadratic form `vᵀ G(θ) v`. -/
noncomputable def fisherQuadratic
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * fisherMetric F θ i j * v j

lemma expectation_linearStat
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) :
    expectation F θ (linearStat F v) = ∑ i, v i * statMean F θ i := by
  unfold expectation linearStat statMean
  calc
    ∑ x, density F θ x * ∑ i, v i * F.stat x i
        = ∑ x, ∑ i, density F θ x * (v i * F.stat x i) := by
            simp [Finset.mul_sum]
    _ = ∑ i, ∑ x, density F θ x * (v i * F.stat x i) := by
          rw [Finset.sum_comm]
    _ = ∑ i, v i * ∑ x, density F θ x * F.stat x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = ∑ i, v i * statMean F θ i := by
          simp [statMean, expectation]

lemma centeredLinearStat_eq_sum_centeredStat
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ)
    (x : α) :
    centeredLinearStat F θ v x = ∑ i, v i * centeredStat F θ i x := by
  unfold centeredLinearStat linearStat centeredStat
  have hExp :
      expectation F θ (fun x => ∑ i, v i * F.stat x i) = ∑ i, v i * statMean F θ i := by
    simpa [linearStat] using expectation_linearStat (F := F) (θ := θ) (v := v)
  rw [hExp]
  calc
    ∑ i, v i * F.stat x i - ∑ i, v i * statMean F θ i
        = ∑ i, (v i * F.stat x i - v i * statMean F θ i) := by
            have hsum :
                (∑ i, (v i * F.stat x i - v i * statMean F θ i))
                  = (∑ i, v i * F.stat x i) - (∑ i, v i * statMean F θ i) := by
              simp [Finset.sum_sub_distrib]
            exact hsum.symm
    _ = ∑ i, v i * (F.stat x i - statMean F θ i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

lemma fisher_as_variance
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) :
    fisherQuadratic F θ v =
      expectation F θ (fun x => (centeredLinearStat F θ v x) ^ (2 : ℕ)) := by
  unfold fisherQuadratic fisherMetric covariance expectation
  calc
    ∑ i, ∑ j, v i * (∑ x, density F θ x * (centeredStat F θ i x * centeredStat F θ j x)) * v j
        = ∑ i, ∑ j, ∑ x, density F θ x * (v i * centeredStat F θ i x * (v j * centeredStat F θ j x)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              v i * (∑ x, density F θ x * (centeredStat F θ i x * centeredStat F θ j x)) * v j
                  = (v i * v j) * ∑ x, density F θ x * (centeredStat F θ i x * centeredStat F θ j x) := by
                      ring
              _ = ∑ x, (v i * v j) * (density F θ x * (centeredStat F θ i x * centeredStat F θ j x)) := by
                    rw [Finset.mul_sum]
              _ = ∑ x, density F θ x * (v i * centeredStat F θ i x * (v j * centeredStat F θ j x)) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    ring
    _ = ∑ i, ∑ x, ∑ j, density F θ x * (v i * centeredStat F θ i x * (v j * centeredStat F θ j x)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ i, ∑ j, density F θ x * (v i * centeredStat F θ i x * (v j * centeredStat F θ j x)) := by
          rw [Finset.sum_comm]
    _ = ∑ x, density F θ x * (∑ i, v i * centeredStat F θ i x) * (∑ j, v j * centeredStat F θ j x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ x, density F θ x * (centeredLinearStat F θ v x) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [centeredLinearStat_eq_sum_centeredStat]
          ring

theorem fisher_positive_semidefinite
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ)
    [Nonempty α] :
    0 ≤ fisherQuadratic F θ v := by
  rw [fisher_as_variance]
  unfold expectation
  refine Finset.sum_nonneg ?_
  intro x hx
  exact mul_nonneg (density_nonneg F θ x) (pow_two_nonneg _)

theorem fisher_positive_definite
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (h_indep :
      ∀ v : Fin d → ℝ, v ≠ 0 →
        ∃ x, linearStat F v x ≠ expectation F θ (linearStat F v))
    [Nonempty α] :
    ∀ v : Fin d → ℝ, v ≠ 0 → 0 < fisherQuadratic F θ v := by
  intro v hv
  rcases h_indep v hv with ⟨x0, hx0⟩
  rw [fisher_as_variance]
  unfold expectation
  have h_nonneg :
      ∀ x ∈ (Finset.univ : Finset α),
        0 ≤ density F θ x * (centeredLinearStat F θ v x) ^ (2 : ℕ) := by
    intro x hx
    exact mul_nonneg (density_nonneg F θ x) (pow_two_nonneg _)
  have h_pos_witness :
      ∃ x ∈ (Finset.univ : Finset α),
        0 < density F θ x * (centeredLinearStat F θ v x) ^ (2 : ℕ) := by
    refine ⟨x0, Finset.mem_univ x0, ?_⟩
    have h_centered_ne :
        centeredLinearStat F θ v x0 ≠ 0 := by
      intro hzero
      apply hx0
      exact sub_eq_zero.mp (by simpa [centeredLinearStat] using hzero)
    exact mul_pos (density_pos F θ x0) (pow_two_pos_of_ne_zero h_centered_ne)
  exact Finset.sum_pos' h_nonneg h_pos_witness

/-- Minimal log-potential interface. -/
structure LogPotential (Θ : Type _) where
  ψ : Θ → ℝ

/-- Exponential-family induced log-potential on parameter space. -/
noncomputable def expLogPotential
    {d : ℕ}
    (F : FiniteExpFamily (α := α) d) :
    LogPotential (Fin d → ℝ) where
  ψ := logPartition F

/-- Bregman divergence generated by a log-potential. -/
noncomputable def bregman
    {Θ : Type _}
    [NormedAddCommGroup Θ]
    [NormedSpace ℝ Θ]
    (L : LogPotential Θ)
    (η θ : Θ) : ℝ :=
  L.ψ η - L.ψ θ - (fderiv ℝ L.ψ θ) (η - θ)

end InfoGeometry.Information
