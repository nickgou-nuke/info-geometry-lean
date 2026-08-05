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

abbrev CuntzThreeWordCarrier := CuntzThree

noncomputable def wordIsometry3 : CuntzWord3 → CuntzThreeWordCarrier
  | [] => 1
  | i :: w => cuntzS 3 i * wordIsometry3 w

@[simp] theorem wordIsometry3_nil : wordIsometry3 [] = (1 : CuntzThree) := rfl

@[simp] theorem wordIsometry3_cons (i : Fin 3) (w : CuntzWord3) :
    wordIsometry3 (i :: w) = cuntzS 3 i * wordIsometry3 w := rfl

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

def WordMonomialKMSLaw
    (φ : CuntzThree →ₗ[ℂ] ℂ) : Prop :=
  ∀ μ ν : CuntzWord3,
    φ (wordIsometry3 μ * star (wordIsometry3 ν)) =
      canonicalKMSWordValue μ ν

theorem wordMonomialKMSLaw_generator
    (φ : CuntzThree →ₗ[ℂ] ℂ)
    (hLaw : WordMonomialKMSLaw φ) (i j : Fin 3) :
    φ (cuntzS 3 i * cuntzSdag 3 j) =
      if i = j then (1 / 3 : ℂ) else 0 := by
  have h := hLaw [i] [j]
  simpa [wordIsometry3, star_mul, star_cuntzS, star_cuntzSdag,
    canonicalKMSWordValue_single] using h

end InfoGeometry.Canonical
