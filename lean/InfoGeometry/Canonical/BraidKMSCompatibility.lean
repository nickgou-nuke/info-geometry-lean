/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.BraidPermutationActionOnCuntzFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CuntzGeneratorKMSLogThree
import InfoGeometry.Canonical.CuntzWordMonomialKMSFunctional
import InfoGeometry.Algebra.CuntzTensorQuotient
import InfoGeometry.Physics.B3PresentedGroup

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Physics.B3PresentedGroup

/-!
# Braid-KMS word-level compatibility

The results below establish invariance of the specified monomial KMS values
under relabelling the three generator indices. They remain statements about
finite words and their monomial readouts; they do not define an automorphism of
the Cuntz quotient or an analytic KMS state.
-/

/-- An injective relabelling of letters reflects equality of finite words. -/
theorem list_map_eq_iff_of_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (xs ys : List α) :
    List.map f xs = List.map f ys ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp
  | cons x xs ih =>
      cases ys with
      | nil => simp
      | cons y ys =>
          constructor
          · intro h
            injection h with hhead htail
            have hxy : x = y := hf hhead
            subst y
            congr 1
            exact (ih ys).mp htail
          · intro h
            injection h with hhead htail
            subst y
            subst ys
            rfl

/-- The canonical word-monomial KMS value is invariant under an alphabet
equivalence: relabelling preserves both equality of words and word length. -/
theorem canonicalKMSWordValue_map_equiv (σ : Fin 3 ≃ Fin 3)
    (μ ν : CuntzWord3) :
    canonicalKMSWordValue (List.map σ μ) (List.map σ ν) =
      canonicalKMSWordValue μ ν := by
  classical
  unfold canonicalKMSWordValue
  have hEq : List.map σ μ = List.map σ ν ↔ μ = ν :=
    list_map_eq_iff_of_injective σ σ.injective μ ν
  by_cases h : μ = ν
  · subst ν
    simp
  · have h' : List.map σ μ ≠ List.map σ ν := fun hmap => h (hEq.mp hmap)
    simp [h, h']

/-- The monomial KMS readout is invariant under every relabelling of the
three Cuntz generators. This is a word-monomial statement, not an algebra
automorphism theorem. -/
theorem wordMonomialKMSLaw_alphabetEquiv_invariant
    (φ : CuntzAlg 3 →ₗ[ℂ] ℂ) (hLaw : WordMonomialKMSLaw φ)
    (σ : Fin 3 ≃ Fin 3) (μ ν : CuntzWord3) :
    φ (wordIsometry3 (List.map σ μ) *
        star (wordIsometry3 (List.map σ ν))) =
      φ (wordIsometry3 μ * star (wordIsometry3 ν)) := by
  calc
    _ = canonicalKMSWordValue (List.map σ μ) (List.map σ ν) := hLaw _ _
    _ = canonicalKMSWordValue μ ν := canonicalKMSWordValue_map_equiv σ μ ν
    _ = _ := (hLaw μ ν).symm

/-- The word-monomial KMS readout is invariant under the finite `σ₁` index
permutation. -/
theorem wordMonomialKMSLaw_braidSigma1_invariant
    (φ : CuntzAlg 3 →ₗ[ℂ] ℂ) (hLaw : WordMonomialKMSLaw φ)
    (μ ν : CuntzWord3) :
    φ (wordIsometry3 (braidSigma1Action μ) *
        star (wordIsometry3 (braidSigma1Action ν))) =
      φ (wordIsometry3 μ * star (wordIsometry3 ν)) := by
  simpa [braidSigma1Action] using
    wordMonomialKMSLaw_alphabetEquiv_invariant φ hLaw braidSigma1LetterEquiv μ ν

/-- The word-monomial KMS readout is invariant under the finite `σ₂` index
permutation. -/
theorem wordMonomialKMSLaw_braidSigma2_invariant
    (φ : CuntzAlg 3 →ₗ[ℂ] ℂ) (hLaw : WordMonomialKMSLaw φ)
    (μ ν : CuntzWord3) :
    φ (wordIsometry3 (braidSigma2Action μ) *
        star (wordIsometry3 (braidSigma2Action ν))) =
      φ (wordIsometry3 μ * star (wordIsometry3 ν)) := by
  simpa [braidSigma2Action] using
    wordMonomialKMSLaw_alphabetEquiv_invariant φ hLaw braidSigma2LetterEquiv μ ν

end InfoGeometry.Canonical
