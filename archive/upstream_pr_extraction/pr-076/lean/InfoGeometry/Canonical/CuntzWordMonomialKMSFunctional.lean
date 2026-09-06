import Mathlib
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient

/-!
## Candidate word-monomial law for the algebraic Cuntz quotient

This file records the finite-word formula
`ω(S_μ S_ν†) = δ_{μν} 3^(-|μ|)` as a specification.  It does not
claim positivity, bounded extension to a C*-completion, or analytic-strip
KMS continuation; those belong to a later owner.
-/

abbrev CuntzWord3 := List (Fin 3)

noncomputable def wordIsometry3 :
    CuntzWord3 → InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3
  | [] => 1
  | i :: w => cuntzS 3 i * wordIsometry3 w

@[simp] theorem wordIsometry3_nil :
    wordIsometry3 [] = (1 : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3) := rfl

@[simp] theorem wordIsometry3_cons (i : Fin 3) (w : CuntzWord3) :
    wordIsometry3 (i :: w) = cuntzS 3 i * wordIsometry3 w := rfl

theorem wordIsometry3_append (μ ν : CuntzWord3) :
    wordIsometry3 (μ ++ ν) = wordIsometry3 μ * wordIsometry3 ν := by
  induction μ with
  | nil => simp [wordIsometry3]
  | cons i μ ih =>
      simp only [List.cons_append, wordIsometry3_cons]
      rw [ih]
      simp [mul_assoc]

theorem star_wordIsometry3_append (μ ν : CuntzWord3) :
    star (wordIsometry3 (μ ++ ν)) =
      star (wordIsometry3 ν) * star (wordIsometry3 μ) := by
  rw [wordIsometry3_append, star_mul]

theorem wordIsometry3_isometry (μ : CuntzWord3) :
    star (wordIsometry3 μ) * wordIsometry3 μ = 1 := by
  induction μ with
  | nil => simp [wordIsometry3]
  | cons i μ ih =>
      rw [wordIsometry3_cons, star_mul, star_cuntzS]
      calc
        (star (wordIsometry3 μ) * cuntzSdag 3 i) *
              (cuntzS 3 i * wordIsometry3 μ) =
            (star (wordIsometry3 μ) *
              (cuntzSdag 3 i * cuntzS 3 i)) * wordIsometry3 μ := by
                simp [mul_assoc]
        _ = star (wordIsometry3 μ) * wordIsometry3 μ := by
          rw [cuntz_isometry]
          simp
        _ = 1 := ih

theorem wordIsometry3_range_projection_idempotent (μ : CuntzWord3) :
    (wordIsometry3 μ * star (wordIsometry3 μ)) *
        (wordIsometry3 μ * star (wordIsometry3 μ)) =
      wordIsometry3 μ * star (wordIsometry3 μ) := by
  calc
    (wordIsometry3 μ * star (wordIsometry3 μ)) *
          (wordIsometry3 μ * star (wordIsometry3 μ)) =
        wordIsometry3 μ *
          (star (wordIsometry3 μ) * wordIsometry3 μ) *
            star (wordIsometry3 μ) := by simp [mul_assoc]
    _ = wordIsometry3 μ * 1 * star (wordIsometry3 μ) := by
      rw [wordIsometry3_isometry]
    _ = wordIsometry3 μ * star (wordIsometry3 μ) := by simp

@[simp] theorem wordIsometry3_range_projection_star (μ : CuntzWord3) :
    star (wordIsometry3 μ * star (wordIsometry3 μ)) =
      wordIsometry3 μ * star (wordIsometry3 μ) := by
  simp [star_mul]

theorem wordIsometry3_range_projection_mul (μ : CuntzWord3) :
    (wordIsometry3 μ * star (wordIsometry3 μ)) * wordIsometry3 μ =
      wordIsometry3 μ := by
  calc
    (wordIsometry3 μ * star (wordIsometry3 μ)) * wordIsometry3 μ =
        wordIsometry3 μ * (star (wordIsometry3 μ) * wordIsometry3 μ) := by
          simp [mul_assoc]
    _ = wordIsometry3 μ * 1 := by rw [wordIsometry3_isometry]
    _ = wordIsometry3 μ := by simp

theorem wordIsometry3_star_mul_range_projection (μ : CuntzWord3) :
    star (wordIsometry3 μ) *
        (wordIsometry3 μ * star (wordIsometry3 μ)) =
      star (wordIsometry3 μ) := by
  calc
    star (wordIsometry3 μ) *
          (wordIsometry3 μ * star (wordIsometry3 μ)) =
        (star (wordIsometry3 μ) * wordIsometry3 μ) *
          star (wordIsometry3 μ) := by simp [mul_assoc]
    _ = 1 * star (wordIsometry3 μ) := by rw [wordIsometry3_isometry]
    _ = star (wordIsometry3 μ) := by simp

theorem wordIsometry3_orthogonal_of_ne_of_length_eq
    (μ ν : CuntzWord3) (hμν : μ ≠ ν)
    (hlen : μ.length = ν.length) :
    star (wordIsometry3 μ) * wordIsometry3 ν = 0 := by
  induction μ generalizing ν with
  | nil =>
      cases ν with
      | nil => exact False.elim (hμν rfl)
      | cons j ν => simp at hlen
  | cons i μ ih =>
      cases ν with
      | nil => simp at hlen
      | cons j ν =>
          by_cases hij : i = j
          · subst j
            have htail : μ ≠ ν := by
              intro h
              apply hμν
              simp [h]
            have hlen' : μ.length = ν.length := by
              simpa using hlen
            rw [wordIsometry3_cons, star_mul, star_cuntzS,
              wordIsometry3_cons]
            calc
              (star (wordIsometry3 μ) * cuntzSdag 3 i) *
                    (cuntzS 3 i * wordIsometry3 ν) =
                  star (wordIsometry3 μ) *
                    (cuntzSdag 3 i * cuntzS 3 i) *
                      wordIsometry3 ν := by simp [mul_assoc]
              _ = star (wordIsometry3 μ) * wordIsometry3 ν := by
                rw [cuntz_isometry]
                simp
              _ = 0 := ih ν htail hlen'
          · rw [wordIsometry3_cons, star_mul, star_cuntzS,
              wordIsometry3_cons]
            calc
              (star (wordIsometry3 μ) * cuntzSdag 3 i) *
                    (cuntzS 3 j * wordIsometry3 ν) =
                  star (wordIsometry3 μ) *
                    (cuntzSdag 3 i * cuntzS 3 j) *
                      wordIsometry3 ν := by simp [mul_assoc]
              _ = 0 := by
                rw [cuntz_distinct_orthogonal 3 hij]
                simp

noncomputable def canonicalKMSWordValue (μ ν : CuntzWord3) : ℂ :=
  if μ = ν then ((3 : ℂ)⁻¹) ^ μ.length else 0

@[simp] theorem canonicalKMSWordValue_self (μ : CuntzWord3) :
    canonicalKMSWordValue μ μ = ((3 : ℂ)⁻¹) ^ μ.length := by
  simp [canonicalKMSWordValue]

@[simp] theorem canonicalKMSWordValue_ne {μ ν : CuntzWord3} (h : μ ≠ ν) :
    canonicalKMSWordValue μ ν = 0 := by
  simp [canonicalKMSWordValue, h]

@[simp] theorem canonicalKMSWordValue_nil :
    canonicalKMSWordValue [] [] = 1 := by
  simp [canonicalKMSWordValue]

theorem canonicalKMSWordValue_single (i j : Fin 3) :
    canonicalKMSWordValue [i] [j] =
      if i = j then (1 / 3 : ℂ) else 0 := by
  by_cases h : i = j
  · subst j
    simp [canonicalKMSWordValue]
  · simp [canonicalKMSWordValue, h]

theorem canonicalKMSWordValue_cons_self (i : Fin 3) (w : CuntzWord3) :
    canonicalKMSWordValue (i :: w) (i :: w) =
      (3 : ℂ)⁻¹ * canonicalKMSWordValue w w := by
  simp [canonicalKMSWordValue, pow_succ, mul_comm]

theorem canonicalKMSWordValue_append_self (μ ν : CuntzWord3) :
    canonicalKMSWordValue (μ ++ ν) (μ ++ ν) =
      canonicalKMSWordValue μ μ * canonicalKMSWordValue ν ν := by
  simp [canonicalKMSWordValue, List.length_append, pow_add]

def WordMonomialKMSLaw
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ) : Prop :=
  ∀ μ ν : CuntzWord3,
    φ (wordIsometry3 μ * star (wordIsometry3 ν)) =
      canonicalKMSWordValue μ ν

theorem wordMonomialKMSLaw_generator
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ)
    (hLaw : WordMonomialKMSLaw φ) (i j : Fin 3) :
    φ (cuntzS 3 i * cuntzSdag 3 j) =
      if i = j then (1 / 3 : ℂ) else 0 := by
  have h := hLaw [i] [j]
  simpa [wordIsometry3, star_mul, star_cuntzS, star_cuntzSdag,
    canonicalKMSWordValue_single] using h

theorem wordMonomialKMSLaw_generatorKMSAt_log_three
    (φ : InfoGeometry.Algebra.CuntzTensorQuotient.CuntzAlg 3 →ₗ[ℂ] ℂ)
    (hLaw : WordMonomialKMSLaw φ) :
    GeneratorKMSAt φ (Real.log 3) := by
  constructor
  · have h := hLaw [] []
    simpa [wordIsometry3, canonicalKMSWordValue] using h
  · intro i j
    have h := wordMonomialKMSLaw_generator φ hLaw i j
    by_cases hij : i = j
    · subst j
      simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] using h
    · simpa [hij, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)] using h

end InfoGeometry.Canonical
