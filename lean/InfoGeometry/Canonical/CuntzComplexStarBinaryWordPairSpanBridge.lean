/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge

/-!
# Word-pair spanning for the corrected binary complex-* quotient

This owner proves that the arbitrary word-pair monomials span the actual
quotient algebra.  The proof is through the tensor-algebra presentation and
then transport across the proved complexification equivalence.  It does not
use diagonal matrices, a boundary representation, or a scalar state.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge

open InfoGeometry.Topology.AlgebraicCuntzQuotient
open InfoGeometry.Physics.ComplexStarCuntzRedesign
open InfoGeometry.Algebra.CuntzComplexification
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordReductionBridge
open InfoGeometry.Algebra.CuntzComplexStarBinaryWordPairMultiplicationBridge

abbrev Target := CuntzAlg ℂ Bool
abbrev Source := ComplexStarCuntzAlg Bool

def targetWordPair (u v : List Bool) : Target :=
  targetWord u * targetWordDag v

def targetPair (p : List Bool × List Bool) : Target :=
  targetWordPair p.1 p.2

private theorem targetWord_append (u v : List Bool) :
    targetWord (u ++ v) = targetWord u * targetWord v := by
  induction u with
  | nil => simp [targetWord]
  | cons b u ih =>
      simp only [List.cons_append, targetWord]
      rw [ih, mul_assoc]

private theorem targetWordDag_append (u v : List Bool) :
    targetWordDag (u ++ v) = targetWordDag v * targetWordDag u := by
  induction u with
  | nil => simp [targetWordDag]
  | cons b u ih =>
      simp only [List.cons_append, targetWordDag]
      rw [ih, mul_assoc]

private def targetWordPairSpan : Submodule ℂ Target :=
  Submodule.span ℂ (Set.range targetPair)

private theorem targetWordPair_mem_span (u v : List Bool) :
    targetWordPair u v ∈ targetWordPairSpan :=
  Submodule.subset_span ⟨(u, v), rfl⟩

private theorem targetWordPair_mul_mem_span
    (u v x y : List Bool) :
    targetWordPair u v * targetWordPair x y ∈ targetWordPairSpan := by
  change (targetWord u * targetWordDag v) *
      (targetWord x * targetWordDag y) ∈ targetWordPairSpan
  rcases targetWord_prefix_cases v x with h | h | h
  · rcases h with ⟨t, _, ht⟩
    have hEq : (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) = targetWordPair (u ++ t) y := by
      calc
      (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) =
          targetWord u * (targetWordDag v * targetWord x) *
            targetWordDag y := by simp [mul_assoc]
      _ = targetWord u * targetWord t * targetWordDag y := by rw [ht]
      _ = targetWordPair (u ++ t) y := by
        simp only [targetWordPair]
        rw [targetWord_append]
    rw [hEq]
    exact targetWordPair_mem_span (u ++ t) y
  · rcases h with ⟨t, _, ht⟩
    have hEq : (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) = targetWordPair u (y ++ t) := by
      calc
      (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) =
          targetWord u * (targetWordDag v * targetWord x) *
            targetWordDag y := by simp [mul_assoc]
      _ = targetWord u * targetWordDag t * targetWordDag y := by rw [ht]
      _ = targetWordPair u (y ++ t) := by
        simp only [targetWordPair]
        rw [targetWordDag_append]
        simp only [mul_assoc]
    rw [hEq]
    exact targetWordPair_mem_span u (y ++ t)
  · rcases h with ⟨_, _, ht⟩
    have hEq : (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) = 0 := by
      calc
      (targetWord u * targetWordDag v) *
          (targetWord x * targetWordDag y) =
          targetWord u * (targetWordDag v * targetWord x) *
            targetWordDag y := by simp [mul_assoc]
      _ = 0 := by simp [ht]
    rw [hEq]
    exact targetWordPairSpan.zero_mem

private theorem targetWordPair_left_mul_span
    (u v : List Bool) {y : Target}
    (hy : y ∈ targetWordPairSpan) :
    targetWordPair u v * y ∈ targetWordPairSpan := by
  unfold targetWordPairSpan at hy ⊢
  refine Submodule.span_induction
    (p := fun z _ => targetWordPair u v * z ∈ targetWordPairSpan)
    ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with ⟨q, rfl⟩
    exact targetWordPair_mul_mem_span u v q.1 q.2
  · simpa using targetWordPairSpan.zero_mem
  · intro z₁ z₂ _ _ hz₁ hz₂
    simpa [mul_add] using targetWordPairSpan.add_mem hz₁ hz₂
  · intro c z _ hz
    rw [mul_smul_comm]
    exact targetWordPairSpan.smul_mem c hz

private theorem targetWordPairSpan_mul_mem
    {x y : Target} (hx : x ∈ targetWordPairSpan)
    (hy : y ∈ targetWordPairSpan) : x * y ∈ targetWordPairSpan := by
  unfold targetWordPairSpan at hx ⊢
  refine Submodule.span_induction
    (p := fun z _ => z * y ∈ targetWordPairSpan)
    ?_ ?_ ?_ ?_ hx
  · intro z hz
    rcases hz with ⟨p, rfl⟩
    exact targetWordPair_left_mul_span p.1 p.2 hy
  · simpa using targetWordPairSpan.zero_mem
  · intro z₁ z₂ _ _ hz₁ hz₂
    simpa [add_mul] using targetWordPairSpan.add_mem hz₁ hz₂
  · intro c z _ hz
    rw [smul_mul_assoc]
    exact targetWordPairSpan.smul_mem c hz

private theorem targetQuotientGenerator_mem_span
    (v : Gen ℂ Bool) :
    mk (R := ℂ) (TensorAlgebra.ι ℂ v) ∈ targetWordPairSpan := by
  unfold targetWordPairSpan
  let qι : Gen ℂ Bool →ₗ[ℂ] Target :=
    (mk (R := ℂ)).toLinearMap.comp (TensorAlgebra.ι ℂ)
  change qι v ∈ targetWordPairSpan
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp [qι]
  · intro v₁ v₂ hv₁ hv₂
    rw [map_add]
    exact targetWordPairSpan.add_mem hv₁ hv₂
  · intro g c
    cases g with
    | s b =>
      have hsingle : Finsupp.single (CuntzLetter.s b) c =
          c • Finsupp.single (CuntzLetter.s b) (1 : ℂ) := by
        ext g
        simp
      rw [hsingle, map_smul]
      apply targetWordPairSpan.smul_mem c
      change S b ∈ targetWordPairSpan
      have hmono : targetWordPair [b] [] = S b := by
        simp [targetWordPair, targetWord, targetWordDag]
      rw [← hmono]
      exact targetWordPair_mem_span [b] []
    | t b =>
      have hsingle : Finsupp.single (CuntzLetter.t b) c =
          c • Finsupp.single (CuntzLetter.t b) (1 : ℂ) := by
        ext g
        simp
      rw [hsingle, map_smul]
      apply targetWordPairSpan.smul_mem c
      change T b ∈ targetWordPairSpan
      have hmono : targetWordPair [] [b] = T b := by
        simp [targetWordPair, targetWord, targetWordDag]
      rw [← hmono]
      exact targetWordPair_mem_span [] [b]

private theorem targetTensorImage_mem_span (x : TAlg ℂ Bool) :
    mk (R := ℂ) x ∈ targetWordPairSpan := by
  unfold targetWordPairSpan at ⊢
  induction x using TensorAlgebra.induction with
  | algebraMap c =>
      rw [(mk (R := ℂ)).commutes c]
      have hunit : (1 : Target) ∈
          Submodule.span ℂ (Set.range targetPair) := by
        apply Submodule.subset_span
        exact ⟨([], []), by simp [targetPair, targetWordPair, targetWord, targetWordDag]⟩
      simpa [Algebra.smul_def] using
        (Submodule.span ℂ (Set.range targetPair)).smul_mem c hunit
  | ι v => exact targetQuotientGenerator_mem_span v
  | mul x y hx hy =>
      rw [map_mul]
      exact targetWordPairSpan_mul_mem hx hy
  | add x y hx hy =>
      rw [map_add]
      exact targetWordPairSpan.add_mem hx hy

private theorem target_wordPair_span_eq_top :
    Submodule.span ℂ (Set.range targetPair) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ :=
    RingQuot.mkAlgHom_surjective ℂ (@Rel ℂ Bool _ _ _) x
  exact targetTensorImage_mem_span t

def sourcePair (p : List Bool × List Bool) : Source :=
  complexStarWordPair p.1 p.2

def sourceWordPairSpan : Submodule ℂ Source :=
  Submodule.span ℂ (Set.range sourcePair)

private theorem complexification_wordPair (u v : List Bool) :
    complexificationAlgEquiv (complexStarWordPair u v) =
      targetWordPair u v := by
  simp [complexStarWordPair, targetWordPair,
    complexStarWord_toLetter, complexStarWord_star_toLetter]

private theorem complexification_wordPair_range :
    complexificationAlgEquiv.toLinearEquiv.toLinearMap ''
        Set.range sourcePair = Set.range targetPair := by
  ext z
  constructor
  · rintro ⟨x, ⟨⟨u, v⟩, rfl⟩, rfl⟩
    exact ⟨(u, v), (complexification_wordPair u v).symm⟩
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨sourcePair (u, v), ⟨(u, v), rfl⟩,
      by simpa [sourcePair, targetPair] using complexification_wordPair u v⟩

theorem sourceWordPairSpan_map_eq_top :
    sourceWordPairSpan.map complexificationAlgEquiv.toLinearEquiv.toLinearMap = ⊤ := by
  rw [sourceWordPairSpan, Submodule.map_span, complexification_wordPair_range,
    target_wordPair_span_eq_top]

theorem sourceWordPair_span_eq_top : sourceWordPairSpan = ⊤ := by
  apply top_unique
  intro x _
  have hxm : complexificationAlgEquiv.toLinearEquiv.toLinearMap x ∈
      sourceWordPairSpan.map complexificationAlgEquiv.toLinearEquiv.toLinearMap := by
    rw [sourceWordPairSpan_map_eq_top]
    trivial
  rcases hxm with ⟨y, hy, hxy⟩
  have : y = x := complexificationAlgEquiv.injective hxy
  simpa [this] using hy

end InfoGeometry.Canonical.CuntzComplexStarBinaryWordPairSpanBridge
