/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Routing.AttentionPolytope
import InfoGeometry.Canonical.Drazin
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# The Drazin/Birkhoff boundary for deterministic attention vertices

These results concern the native square routing matrix, for arbitrary size.
Zero complementary Drazin projector characterizes bijective routing, and hence
membership in the doubly stochastic polytope, among deterministic vertices.
No such equivalence is asserted for general stochastic mixtures.
-/

namespace InfoGeometry.Routing.AttentionPolytope
open Matrix DeterministicArgmaxAttention
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.Drazin.IsDrazinInverse
open scoped BigOperators

variable {n : ℕ}

@[simp] theorem deterministic_id : deterministicAttention (id : Fin n → Fin n) = 1 := by
  ext i j
  simp [deterministicAttention, Matrix.one_apply, eq_comm]

/-- A right inverse prevents two queries from selecting the same key. -/
theorem deterministic_injective_of_right_inverse (f : Fin n → Fin n)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : deterministicAttention f * B = 1) :
    Function.Injective f := by
  have hentry (i j : Fin n) : B (f i) j = if i = j then 1 else 0 := by
    simpa [Matrix.mul_apply, deterministicAttention, Matrix.one_apply] using
      congrArg (fun T : Matrix (Fin n) (Fin n) ℝ => T i j) hB
  intro i j hij
  by_contra hne
  have hi := hentry i i
  have hj := hentry j i
  rw [hij] at hi
  simp only [ite_true] at hi
  rw [ite_eq_right (Ne.symm hne)] at hj
  exact one_ne_zero (hi.symm.trans hj)

/-- The inverse routing function supplies an actual two-sided matrix inverse. -/
theorem deterministic_equiv_inverse (e : Fin n ≃ Fin n) :
    deterministicAttention e * deterministicAttention e.symm = 1 ∧
      deterministicAttention e.symm * deterministicAttention e = 1 := by
  constructor <;> rw [deterministic_mul] <;> ext i j <;>
    simp [deterministicAttention, Matrix.one_apply, eq_comm]

/-- Bijective routing has an index-zero Drazin witness, on the original carrier. -/
theorem deterministic_equiv_drazin (e : Fin n ≃ Fin n) :
    IsDrazinInverse (deterministicAttention e) (deterministicAttention e.symm) 0 := by
  obtain ⟨hab, hba⟩ := deterministic_equiv_inverse e
  exact ⟨hab.trans hba.symm, by rw [hba, one_mul], by simpa using hab⟩

/-- Among deterministic vertices, a vanishing nilpotent projector is exactly bijectivity. -/
theorem deterministic_complement_zero_iff_bijective (f : Fin n → Fin n)
    {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    (hD : IsDrazinInverse (deterministicAttention f) D k) :
    complementaryProjection (deterministicAttention f) D = 0 ↔ Function.Bijective f := by
  constructor
  · intro hz
    have hi : deterministicAttention f * D = 1 := (sub_eq_zero.mp hz).symm
    exact (Fintype.bijective_iff_injective_and_card f).2
      ⟨deterministic_injective_of_right_inverse f D hi, rfl⟩
  · intro hf
    let e : Fin n ≃ Fin n := Equiv.ofBijective f hf
    have hd : D = deterministicAttention e.symm :=
      unique_of_indices hD (deterministic_equiv_drazin e)
    rw [hd]
    change 1 - deterministicAttention e * deterministicAttention e.symm = 0
    rw [(deterministic_equiv_inverse e).1, sub_self]

/-- The native Birkhoff polytope cuts out exactly the bijective deterministic routes. -/
theorem deterministic_doublyStochastic_iff_bijective (f : Fin n → Fin n) :
    deterministicAttention f ∈ doublyStochastic ℝ (Fin n) ↔ Function.Bijective f := by
  rw [mem_doublyStochastic_iff_sum]
  constructor
  · intro h
    have hs : Function.Surjective f := by
      intro j
      by_contra hj
      have hz (i : Fin n) : deterministicAttention f i j = 0 := by
        have hji : j ≠ f i := fun he => hj ⟨i, he.symm⟩
        exact ite_eq_right hji
      have hc := h.2.2 j
      simp only [hz, Finset.sum_const_zero] at hc
      exact zero_ne_one hc
    exact (Fintype.bijective_iff_surjective_and_card f).2 ⟨hs, rfl⟩
  · intro hf
    refine ⟨(deterministic_mem f).1, deterministic_attention_row_sum f, ?_⟩
    intro j
    obtain ⟨i, rfl⟩ := hf.2 j
    simp [deterministicAttention, hf.1.eq_iff]

/-- The exact polytope/spectral bridge, restricted to deterministic vertices. -/
theorem deterministic_doublyStochastic_iff_complement_zero (f : Fin n → Fin n)
    {D : Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    (hD : IsDrazinInverse (deterministicAttention f) D k) :
    deterministicAttention f ∈ doublyStochastic ℝ (Fin n) ↔
      complementaryProjection (deterministicAttention f) D = 0 := by
  rw [deterministic_doublyStochastic_iff_bijective,
    deterministic_complement_zero_iff_bijective f hD]

end InfoGeometry.Routing.AttentionPolytope
