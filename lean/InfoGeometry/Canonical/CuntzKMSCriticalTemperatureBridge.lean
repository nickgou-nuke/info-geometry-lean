import Mathlib
import InfoGeometry.Algebra.CuntzTensorQuotient

namespace InfoGeometry.Canonical.CuntzKMSCriticalTemperatureBridge

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
# Native O₂ generator-level KMS bridge

This owner uses the algebraic Cuntz quotient `CuntzAlg 2`.  It deliberately
does not identify a scalar partition equation with a KMS state: the input is
an actual complex-linear functional on the quotient together with the
generator-level KMS relation.
-/

abbrev NativeCuntzTwo := CuntzAlg 2

def GeneratorKMSAtTwo
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ) (β : ℝ) : Prop :=
  φ 1 = 1 ∧
    ∀ i j : Fin 2,
      φ (cuntzS 2 i * cuntzSdag 2 j) =
        ((Real.exp (-β) : ℝ) : ℂ) *
          φ (cuntzSdag 2 j * cuntzS 2 i)

theorem native_o2_generator_two_point
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ) (β : ℝ)
    (hKMS : GeneratorKMSAtTwo φ β) (i j : Fin 2) :
    φ (cuntzS 2 i * cuntzSdag 2 j) =
      ((Real.exp (-β) : ℝ) : ℂ) * (if i = j then 1 else 0) := by
  rw [hKMS.2 i j, cuntz_orthogonality]
  by_cases h : i = j
  · subst j
    simp [hKMS.1]
  · simp [h, Ne.symm h]

theorem native_o2_generator_partition_equation
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ) (β : ℝ)
    (hKMS : GeneratorKMSAtTwo φ β) :
    (2 : ℂ) * ((Real.exp (-β) : ℝ) : ℂ) = 1 := by
  have hsum :
      ∑ i : Fin 2, φ (cuntzS 2 i * cuntzSdag 2 i) = 1 := by
    calc
      ∑ i : Fin 2, φ (cuntzS 2 i * cuntzSdag 2 i) =
          φ (∑ i : Fin 2, cuntzS 2 i * cuntzSdag 2 i) := by
            rw [map_sum]
      _ = φ 1 := by rw [cuntz_ranges_sum_one]
      _ = 1 := hKMS.1
  calc
    (2 : ℂ) * ((Real.exp (-β) : ℝ) : ℂ) =
        ∑ i : Fin 2, ((Real.exp (-β) : ℝ) : ℂ) := by simp
    _ = ∑ i : Fin 2, φ (cuntzS 2 i * cuntzSdag 2 i) := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      simpa using native_o2_generator_two_point φ β hKMS i i
    _ = 1 := hsum

theorem native_o2_generator_exp_neg_eq_half
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ) (β : ℝ)
    (hKMS : GeneratorKMSAtTwo φ β) :
    Real.exp (-β) = (1 / 2 : ℝ) := by
  have h := native_o2_generator_partition_equation φ β hKMS
  have h' : (2 : ℝ) * Real.exp (-β) = 1 := by
    exact_mod_cast h
  linarith

theorem native_o2_generator_beta_eq_log_two
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ) (β : ℝ)
    (hKMS : GeneratorKMSAtTwo φ β) :
    β = Real.log 2 := by
  have hexp := native_o2_generator_exp_neg_eq_half φ β hKMS
  have htarget : Real.exp (-β) = Real.exp (-Real.log 2) := by
    calc
      Real.exp (-β) = (1 / 2 : ℝ) := hexp
      _ = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have harg : -β = -Real.log 2 := Real.exp_injective htarget
  linarith

theorem native_o2_generator_two_point_at_log_two
    (φ : NativeCuntzTwo →ₗ[ℂ] ℂ)
    (hKMS : GeneratorKMSAtTwo φ (Real.log 2)) (i j : Fin 2) :
    φ (cuntzS 2 i * cuntzSdag 2 j) =
      if i = j then (1 / 2 : ℂ) else 0 := by
  have h := native_o2_generator_two_point φ (Real.log 2) hKMS i j
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  simpa using h

end InfoGeometry.Canonical.CuntzKMSCriticalTemperatureBridge
