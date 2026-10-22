/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
import InfoGeometry.Canonical.CuntzQuotientWordReductionBridge

/-!
# Word-pair spanning for the tensor-quotient Cuntz algebra

This module proves algebraic spanning by all word-pair monomials on the actual
`RingQuot` carrier. It asserts no finite-dimensionality result or linear
independence of the spanning family.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzQuotientWordPairSpan

open InfoGeometry.Algebra.CuntzTensorQuotient
open InfoGeometry.Algebra.CuntzTensorTreeRealizationBridge
open InfoGeometry.Canonical.CuntzQuotientWordReductionBridge

variable (n : ℕ)

/-- The monomials whose complex span is the whole algebraic quotient. -/
def wordPair (p : List (Fin n) × List (Fin n)) : CuntzAlg n :=
  cuntzWordShift p.1 * cuntzWordShiftDag p.2

private def wordPairSpan : Submodule ℂ (CuntzAlg n) :=
  Submodule.span ℂ (Set.range (wordPair n))

private theorem wordPair_mem_span (p : List (Fin n) × List (Fin n)) :
    wordPair n p ∈ wordPairSpan n :=
  Submodule.subset_span ⟨p, rfl⟩

private theorem wordPair_mul_wordPair_mem_span
    (p q : List (Fin n) × List (Fin n)) :
    wordPair n p * wordPair n q ∈ wordPairSpan n := by
  change (cuntzWordShift p.1 * cuntzWordShiftDag p.2) *
      (cuntzWordShift q.1 * cuntzWordShiftDag q.2) ∈ wordPairSpan n
  rcases cuntzWordMonomial_mul_prefix_cases p.1 p.2 q.1 q.2 with h | h | h
  · rcases h with ⟨t, _, ht⟩
    rw [ht]
    exact wordPair_mem_span n (p.1 ++ t, q.2)
  · rcases h with ⟨t, _, ht⟩
    rw [ht]
    exact wordPair_mem_span n (p.1, q.2 ++ t)
  · rcases h with ⟨_, _, ht⟩
    rw [ht]
    exact (wordPairSpan n).zero_mem

private theorem wordPair_left_mul_span
    (p : List (Fin n) × List (Fin n)) {y : CuntzAlg n}
    (hy : y ∈ wordPairSpan n) : wordPair n p * y ∈ wordPairSpan n := by
  refine Submodule.span_induction
    (p := fun z _ => wordPair n p * z ∈ wordPairSpan n)
    ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨q, rfl⟩
    exact wordPair_mul_wordPair_mem_span n p q
  · simpa using (wordPairSpan n).zero_mem
  · intro z₁ z₂ _ _ hz₁ hz₂
    simpa [mul_add] using (wordPairSpan n).add_mem hz₁ hz₂
  · intro c z _ hz
    rw [mul_smul_comm]
    exact (wordPairSpan n).smul_mem c hz

private theorem wordPairSpan_mul_mem
    {x y : CuntzAlg n} (hx : x ∈ wordPairSpan n)
    (hy : y ∈ wordPairSpan n) : x * y ∈ wordPairSpan n := by
  refine Submodule.span_induction
    (p := fun z _ => z * y ∈ wordPairSpan n)
    ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨p, rfl⟩
    exact wordPair_left_mul_span n p hy
  · simpa using (wordPairSpan n).zero_mem
  · intro z₁ z₂ _ _ hz₁ hz₂
    simpa [add_mul] using (wordPairSpan n).add_mem hz₁ hz₂
  · intro c z _ hz
    rw [smul_mul_assoc]
    exact (wordPairSpan n).smul_mem c hz

private theorem quotientGenerator_mem_wordPairSpan (v : CuntzFree n) :
    cuntzMk n (TensorAlgebra.ι ℂ v) ∈ wordPairSpan n := by
  let qι : CuntzFree n →ₗ[ℂ] CuntzAlg n :=
    (cuntzMk n).toLinearMap.comp (TensorAlgebra.ι ℂ)
  change qι v ∈ wordPairSpan n
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp [qι]
  · intro v₁ v₂ hv₁ hv₂
    rw [map_add]
    exact (wordPairSpan n).add_mem hv₁ hv₂
  · intro g c
    rcases g with ⟨i, b⟩
    cases b
    · have hsingle : Finsupp.single (i, false) c =
          c • Finsupp.single (i, false) (1 : ℂ) := by
        ext g
        simp
      rw [hsingle, map_smul]
      apply (wordPairSpan n).smul_mem c
      change cuntzS n i ∈ wordPairSpan n
      have hmono : wordPair n ([i], ([] : List (Fin n))) = cuntzS n i := by
        simp [wordPair, cuntzWordShift, cuntzWordShiftDag]
      rw [← hmono]
      exact wordPair_mem_span n ([i], ([] : List (Fin n)))
    · have hsingle : Finsupp.single (i, true) c =
          c • Finsupp.single (i, true) (1 : ℂ) := by
        ext g
        simp
      rw [hsingle, map_smul]
      apply (wordPairSpan n).smul_mem c
      change cuntzSdag n i ∈ wordPairSpan n
      have hmono : wordPair n (([] : List (Fin n)), [i]) = cuntzSdag n i := by
        simp [wordPair, cuntzWordShift, cuntzWordShiftDag]
      rw [← hmono]
      exact wordPair_mem_span n (([] : List (Fin n)), [i])

private theorem tensorImage_mem_wordPairSpan (x : CuntzTensor n) :
    cuntzMk n x ∈ wordPairSpan n := by
  induction x using TensorAlgebra.induction with
  | algebraMap c =>
      rw [(cuntzMk n).commutes c]
      have hunit : (1 : CuntzAlg n) ∈ wordPairSpan n := by
        apply Submodule.subset_span
        exact ⟨(([] : List (Fin n)), ([] : List (Fin n))), by
          simp [wordPair, cuntzWordShift, cuntzWordShiftDag]⟩
      simpa [Algebra.smul_def] using
        (wordPairSpan n).smul_mem c hunit
  | ι v => exact quotientGenerator_mem_wordPairSpan n v
  | mul x y hx hy =>
      rw [map_mul]
      exact wordPairSpan_mul_mem n hx hy
  | add x y hx hy =>
      rw [map_add]
      exact (wordPairSpan n).add_mem hx hy

/-- Every element of the actual tensor-algebra quotient is a complex linear
combination of the word-pair monomials `S_u S_v†`. -/
theorem wordPair_span_eq_top :
    Submodule.span ℂ (Set.range (wordPair n)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (CuntzRel n) x
  exact tensorImage_mem_wordPairSpan n t

end InfoGeometry.Canonical.CuntzQuotientWordPairSpan
