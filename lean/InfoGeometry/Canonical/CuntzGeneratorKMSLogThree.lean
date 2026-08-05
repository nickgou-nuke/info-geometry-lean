import Mathlib.Tactic
import InfoGeometry.Algebra.CuntzTensorQuotient

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Generator-level KMS temperature for the native algebraic Cuntz quotient

The carrier is the existing `CuntzAlg ℂ (Fin 3)`, not a commutative diagonal
coefficient algebra.  This file formalizes the finite generator consequence of
the gauge KMS relation.  Positivity, C*-completion, and analytic-strip KMS
continuation remain separate analytic layers.
-/

abbrev CuntzThree := CuntzAlg 3

def uniformPrimes3 : Fin 3 → ℕ := fun _ => 3

/-- Unital generator-level KMS data for the standard gauge normalization. -/
def GeneratorKMSAt (φ : CuntzThree →ₗ[ℂ] ℂ) (β : ℝ) : Prop :=
  φ 1 = 1 ∧
    ∀ i j : Fin 3,
      φ (cuntzS 3 i * cuntzSdag 3 j) =
        if i = j then (Real.exp (-β) : ℂ) else 0

theorem generatorKMS_partitionEquation
    {φ : CuntzThree →ₗ[ℂ] ℂ} {β : ℝ}
    (hKMS : GeneratorKMSAt φ β) :
    (3 : ℂ) * Real.exp (-β) = 1 := by
  have hsum : φ 1 = ∑ i : Fin 3, φ (cuntzS 3 i * cuntzSdag 3 i) := by
    rw [← map_sum, cuntz_ranges_sum_one]
  calc
    (3 : ℂ) * Real.exp (-β) =
        ∑ i : Fin 3, (Real.exp (-β) : ℂ) := by
          simp [Finset.sum_const, Finset.card_fin]
    _ = ∑ i : Fin 3, φ (cuntzS 3 i * cuntzSdag 3 i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa using (hKMS.2 i i).symm
    _ = φ 1 := hsum.symm
    _ = 1 := hKMS.1

theorem generatorKMS_beta_eq_log_three
    {φ : CuntzThree →ₗ[ℂ] ℂ} {β : ℝ}
    (hKMS : GeneratorKMSAt φ β) :
    β = Real.log 3 := by
  have hEq := generatorKMS_partitionEquation hKMS
  have hExp : Real.exp (-β) = 1 / 3 := by
    have hEq' : (3 : ℝ) * Real.exp (-β) = 1 := by
      exact_mod_cast hEq
    linarith
  have hLog : Real.exp (-Real.log 3) = 1 / 3 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hArguments : -β = -Real.log 3 := by
    apply Real.exp_injective
    rw [hExp, hLog]
  linarith

theorem generatorKMS_twoPoint_at_log_three
    (φ : CuntzThree →ₗ[ℂ] ℂ)
    (hKMS : GeneratorKMSAt φ (Real.log 3)) (i j : Fin 3) :
    φ (cuntzS 3 i * cuntzSdag 3 j) =
      if i = j then (1 / 3 : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [hKMS.2]
    simp [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  · simpa [hij] using hKMS.2 i j

theorem cuntzGeneratorKMS_log_three_synthesis
    {φ : CuntzThree →ₗ[ℂ] ℂ} {β : ℝ}
    (hKMS : GeneratorKMSAt φ β) :
    (β = Real.log 3) ∧
      (∀ i j : Fin 3,
        φ (cuntzS 3 i * cuntzSdag 3 j) =
          if i = j then (1 / 3 : ℂ) else 0) := by
  have hβ := generatorKMS_beta_eq_log_three hKMS
  constructor
  · exact hβ
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [hKMS.2]
      simp [hβ, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    · simpa [hij] using hKMS.2 i j

end InfoGeometry.Canonical