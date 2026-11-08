/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionValueCoordinates
import InfoGeometry.Routing.AttentionPolytopeSoftmax

/-!
# Value-dependent Caratheodory compression of attention

For each fixed value table and normalized nonnegative row, construct an
existential simplex with distinct original token indices, strictly positive
weights, and exactly the same output. Its keys lie in the original positive
support; hence no forbidden key is introduced. Its cardinality is at most d+1.

This is an existence theorem using native Mathlib Caratheodory, not a fast
executable sparsifier, a common subset for all queries, or an identification
of the compressed row with the original attention operator.
-/

noncomputable section

namespace InfoGeometry.Routing.AttentionValueCompression

open InfoGeometry.Projective.AttentionValueCoordinates
open scoped BigOperators

variable {J D : Type*} [Fintype J] [Fintype D]

/-- The missing existence theorem: a simplex of original positive-support keys
with positive normalized weights exactly reproduces the fixed value readout.
The embedding prevents repeated token indices, even if the value table has
repeated vectors. The chosen simplex and its coefficients may depend on V,p. -/
theorem exists_sparse_value_readout (V : J → D → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hmass : ∑ j, p j = 1) :
    ∃ (r : ℕ) (f : Fin r ↪ J) (w : Fin r → ℝ),
      r ≤ Fintype.card D + 1 ∧
      AffineIndependent ℝ (fun a => V (f a)) ∧
      (∀ a, 0 < p (f a)) ∧ (∀ a, 0 < w a) ∧
      (∑ a, w a) = 1 ∧
      (∑ a, w a • V (f a)) = ∑ j, p j • V j := by
  classical
  let support : Finset J := Finset.univ.filter (fun j => 0 < p j)
  have hzero (j : J) (hj : j ∉ support) : p j = 0 := by
    have hnp : ¬ 0 < p j := by simpa [support] using hj
    exact le_antisymm (le_of_not_gt hnp) (hp j)
  have hmass_support : ∑ j ∈ support, p j = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ support)]
    · exact hmass
    · intro j _ hj
      exact hzero j hj
  have hvalue_support : (∑ j ∈ support, p j • V j) = ∑ j, p j • V j := by
    apply Finset.sum_subset (Finset.subset_univ support)
    intro j _ hj
    rw [hzero j hj, zero_smul]
  have hx : (∑ j, p j • V j) ∈ convexHull ℝ (V '' {j | 0 < p j}) := by
    rw [← hvalue_support]
    apply (convex_convexHull ℝ _).sum_mem (fun j _ => hp j) hmass_support
    intro j hj
    exact subset_convexHull ℝ _ ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩
  obtain ⟨A, instA, z, u, hz, hind, hu, hsum, hread⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype A := instA
  have hchoose (a : A) : ∃ j : J, 0 < p j ∧ V j = z a :=
    hz (Set.mem_range_self a)
  choose f hfpos hf using hchoose
  have hfinj : Function.Injective f := by
    intro a b hab
    apply hind.injective
    rw [← hf a, ← hf b, hab]
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let g : Fin (Fintype.card A) ↪ J :=
    ⟨fun a => f (e.symm a), hfinj.comp e.symm.injective⟩
  refine ⟨Fintype.card A, g, fun a => u (e.symm a), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact affineIndependent_card_le z hind
  · have hg : (fun a => V (g a)) = z ∘ e.symm := by
      funext a
      exact hf (e.symm a)
    rw [hg]
    exact hind.comp_embedding e.symm.toEmbedding
  · intro a
    exact hfpos (e.symm a)
  · intro a
    exact hu (e.symm a)
  · exact (Equiv.sum_comp e.symm u).trans hsum
  · calc
      (∑ a, u (e.symm a) • V (g a)) = ∑ a, u (e.symm a) • z (e.symm a) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [show V (g a) = z (e.symm a) from hf (e.symm a)]
      _ = ∑ a, u a • z a := Equiv.sum_comp e.symm (fun a => u a • z a)
      _ = ∑ j, p j • V j := hread

/-- A chosen independent simplex has unique normalized readout coordinates. -/
theorem selected_simplex_coordinates_unique {r : ℕ} (V : J → D → ℝ)
    (f : Fin r ↪ J) (hf : AffineIndependent ℝ (fun a => V (f a)))
    (u w : Fin r → ℝ) (hu : ∑ a, u a = 1) (hw : ∑ a, w a = 1)
    (hread : (∑ a, u a • V (f a)) = ∑ a, w a • V (f a)) : u = w :=
  coordinates_unique (fun a => V (f a)) hf u w (hu.trans hw.symm) hread

/-- Existing attention-polytope membership supplies all required hypotheses. -/
theorem exists_attention_row_simplex {n m : ℕ}
    (P : Matrix (Fin n) (Fin m) ℝ)
    (hP : P ∈ AttentionPolytope.attentionPolytope n m)
    (V : Fin m → D → ℝ) (i : Fin n) :
    ∃ (r : ℕ) (f : Fin r ↪ Fin m) (w : Fin r → ℝ),
      r ≤ Fintype.card D + 1 ∧
      AffineIndependent ℝ (fun a => V (f a)) ∧
      (∀ a, 0 < P i (f a)) ∧ (∀ a, 0 < w a) ∧
      (∑ a, w a) = 1 ∧
      (∑ a, w a • V (f a)) = ∑ j, P i j • V j :=
  exists_sparse_value_readout V (fun j => P i j) (hP.1 i) (hP.2 i)

/-- Nonzero original attention weights cannot occur at masked-out keys. -/
theorem positive_support_respects_mask (p : J → ℝ) (allowed : J → Prop)
    (hmask : ∀ j, ¬ allowed j → p j = 0) {j : J} (hj : 0 < p j) : allowed j := by
  by_contra h
  exact (ne_of_gt hj) (hmask j h)

/-- Coordinate normalization agrees exactly with the existing softmax owner. -/
theorem softmax_dehomogenization (V : J → D → ℝ) (s : J → ℝ) (τ : ℝ) :
    dehomogenize (homogeneousDecoder V (fun j => Real.exp (s j / τ))) =
      ∑ j, FiniteSoftmax.weight s τ j • V j := by
  simpa [FiniteSoftmax.weight, FiniteSoftmax.partitionZ] using
    dehomogenize_homogeneousDecoder V (fun j => Real.exp (s j / τ))

/-- The Boltzmann homogeneous sum lies in the nonzero-mass affine chart. -/
theorem softmax_homogeneous_mass_pos [Nonempty J]
    (V : J → D → ℝ) (s : J → ℝ) (τ : ℝ) :
    0 < homogeneousDecoder V (fun j => Real.exp (s j / τ)) none := by
  simpa [FiniteSoftmax.partitionZ] using FiniteSoftmax.partitionZ_pos s τ

/-- Agreement on every value signal forces equality of the mixing operators.
Thus value-dependent sparsification cannot be advertised as universal operator
compression unless the original matrix itself is preserved. -/
theorem matrix_eq_of_all_value_actions {I : Type*}
    (P Q : Matrix I J ℝ)
    (h : ∀ v : J → ℝ, Matrix.mulVec P v = Matrix.mulVec Q v) : P = Q := by
  classical
  ext i j
  have hij := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hij

end InfoGeometry.Routing.AttentionValueCompression
