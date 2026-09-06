import InfoGeometry.Projective.LogSumIneq
import InfoGeometry.Projective.GaugeReduction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


namespace InfoGeometry

namespace Projective.FaithfulKL
end Projective.FaithfulKL

open scoped BigOperators

namespace PositiveMeasure

variable {α : Type u} [Fintype α]

/-!
# Faithful KL Nonnegativity In Simplex Gauge

This file derives normalized (gauge-fixed) KL nonnegativity from the
constructive finite log-sum inequality.
-/

/-- Log-sum gives nonnegativity of the KL-like term on normalized representatives. -/
lemma klLike_normalize_nonneg [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    0 ≤
      klLike (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν) := by
  have hLS :=
    InfoGeometry.Projective.logSum_inequality
      (s := (Finset.univ : Finset α))
      (a := fun i => normalize (α := α) (R := ℝ) μ i)
      (b := fun i => normalize (α := α) (R := ℝ) ν i)
      (ha := by
        intro i hi
        exact (normalize (α := α) (R := ℝ) μ).pos i)
      (hb := by
        intro i hi
        exact (normalize (α := α) (R := ℝ) ν).pos i)

  have hsumμ :
      (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) μ i) = 1 := by
    simpa [PositiveMeasure.Z] using
      (Z_normalize (α := α) (R := ℝ) μ)

  have hsumν :
      (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) ν i) = 1 := by
    simpa [PositiveMeasure.Z] using
      (Z_normalize (α := α) (R := ℝ) ν)

  have hRHS :
      (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) μ i) *
        Real.log
          ((∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) μ i) /
            (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) ν i))
      = 0 := by
    rw [hsumμ, hsumν]
    simp

  have hLS' :
      klLike (α := α)
        (normalize (α := α) (R := ℝ) μ)
        (normalize (α := α) (R := ℝ) ν)
      ≥
      (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) μ i) *
        Real.log
          ((∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) μ i) /
            (∑ i ∈ (Finset.univ : Finset α), normalize (α := α) (R := ℝ) ν i)) := by
    simpa [klLike] using hLS

  rw [hRHS] at hLS'
  exact hLS'

/-- In simplex gauge, generalized KL is nonnegative (it equals `klLike`). -/
lemma generalizedKL_normalize_nonneg [Nonempty α]
    (μ ν : PositiveMeasure α ℝ) :
    0 ≤ generalizedKL (α := α)
      (normalize (α := α) (R := ℝ) μ)
      (normalize (α := α) (R := ℝ) ν) := by
  have h := klLike_normalize_nonneg (α := α) (μ := μ) (ν := ν)
  rw [generalizedKL_normalize_eq_klLike_normalize (α := α) (μ := μ) (ν := ν)]
  exact h

end PositiveMeasure

end InfoGeometry
