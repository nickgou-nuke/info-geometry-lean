/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionIdentifiability
import InfoGeometry.Routing.AttentionAnalogyFiber
import Mathlib.Geometry.Convex.ConvexSpace.Defs

/-!
# General probability fibers of the attention-value decoder

This is not restricted to the four-token analogy. A strictly positive
normalized row lies in a nontrivial continuum of equivalent rows whenever
its indexed values are affinely dependent. The affine dimension of the
whole probability fiber is proved using native `vectorSpan` and rank-nullity.
Probability vectors use the current `Convexity.StdSimplex` carrier.
-/

noncomputable section

namespace InfoGeometry.Routing.AttentionInteriorFiber

open InfoGeometry.Projective.AttentionValueCoordinates
open InfoGeometry.Projective.AttentionIdentifiability
open scoped BigOperators

variable {J D : Type*} [Fintype J]

/-- The inverse image of one homogeneous output inside the native probability simplex. -/
def probabilityFiber (V : J → D → ℝ) (p : J → ℝ) : Set (J → ℝ) :=
  Set.range (fun s : Convexity.StdSimplex ℝ J => (s.weights : J → ℝ)) ∩
    {q | homogeneousDecoder V q = homogeneousDecoder V p}

theorem mem_probabilityFiber_iff (V : J → D → ℝ) (p q : J → ℝ) :
    q ∈ probabilityFiber V p ↔
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧
        homogeneousDecoder V q = homogeneousDecoder V p := by
  simp [probabilityFiber, Convexity.StdSimplex.range_toFun_comp_weights, and_assoc]

theorem self_mem_probabilityFiber (V : J → D → ℝ) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hm : ∑ j, p j = 1) :
    p ∈ probabilityFiber V p :=
  (mem_probabilityFiber_iff V p p).mpr ⟨hp, hm, rfl⟩

/-- Strict positivity gives a common two-sided radius for every finite direction.
No feasibility hypothesis is hidden in the conclusion. -/
theorem exists_positive_radius (p δ : J → ℝ) (hp : ∀ j, 0 < p j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ j, 0 < (p + t • δ) j := by
  classical
  by_cases hJ : Nonempty J
  · letI := hJ
    obtain ⟨j₀, _, hmin⟩ := Finset.univ.exists_min_image
      (fun j => p j / (|δ j| + 1)) Finset.univ_nonempty
    let ε := p j₀ / (|δ j₀| + 1)
    have hε : 0 < ε := div_pos (hp j₀) (by positivity)
    refine ⟨ε, hε, ?_⟩
    intro t ht j
    have hden : 0 < |δ j| + 1 := by positivity
    have hb : ε * (|δ j| + 1) ≤ p j :=
      (le_div_iff₀ hden).mp (hmin j (Finset.mem_univ j))
    have hprod : |t| * |δ j| < p j := calc
      |t| * |δ j| ≤ |t| * (|δ j| + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg t)
      _ < ε * (|δ j| + 1) := mul_lt_mul_of_pos_right ht hden
      _ ≤ p j := hb
    have hlo := neg_abs_le (t * δ j)
    rw [abs_mul] at hlo
    change 0 < p j + t * δ j
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht j
    exact (hJ ⟨j⟩).elim

/-- A nonnegative kernel displacement remains in the exact probability fiber. -/
theorem kernel_shift_mem_probabilityFiber (V : J → D → ℝ) (p δ : J → ℝ)
    (hm : ∑ j, p j = 1) (hδ : δ ∈ (homogeneousDecoder V).ker)
    (t : ℝ) (hn : ∀ j, 0 ≤ (p + t • δ) j) :
    p + t • δ ∈ probabilityFiber V p := by
  have he := decoder_add_smul_of_mem_ker V p δ hδ t
  have hs := ((homogeneousDecoder_eq_iff V (p + t • δ) p).mp he).1
  exact (mem_probabilityFiber_iff V p (p + t • δ)).mpr ⟨hn, hs.trans hm, he⟩

/-- General interior continuum: every dependent value family has an injective
line of strictly positive normalized coordinates through each interior row. -/
theorem exists_positive_kernel_line (V : J → D → ℝ)
    (hV : ¬ AffineIndependent ℝ V) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    ∃ (δ : J → ℝ) (ε : ℝ), δ ≠ 0 ∧ δ ∈ (homogeneousDecoder V).ker ∧
      0 < ε ∧ Function.Injective (fun t : ℝ => p + t • δ) ∧
      ∀ t : ℝ, |t| < ε →
        p + t • δ ∈ probabilityFiber V p ∧ (∀ j, 0 < (p + t • δ) j) := by
  obtain ⟨δ, hne, hker⟩ := exists_nonzero_decoder_kernel V hV
  obtain ⟨ε, hε, hpos⟩ := exists_positive_radius p δ hp
  refine ⟨δ, ε, hne, hker, hε, kernel_line_injective p δ hne, ?_⟩
  intro t ht
  exact ⟨kernel_shift_mem_probabilityFiber V p δ hm hker t
    (fun j => (hpos t ht j).le), hpos t ht⟩

/-- In particular, at every interior row there is a distinct interior row with
identical mass and fixed-value readout. -/
theorem exists_distinct_positive_same_readout (V : J → D → ℝ)
    (hV : ¬ AffineIndependent ℝ V) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    ∃ q : J → ℝ, q ≠ p ∧ (∀ j, 0 < q j) ∧ (∑ j, q j) = 1 ∧
      (∑ j, q j • V j) = ∑ j, p j • V j := by
  obtain ⟨δ, ε, _, _, hε, hinj, hf⟩ := exists_positive_kernel_line V hV p hp hm
  have ht : |ε / 2| < ε := by rw [abs_of_pos (by positivity)]; linarith
  obtain ⟨hmem, hpos⟩ := hf (ε / 2) ht
  obtain ⟨_, hmass, hdec⟩ := (mem_probabilityFiber_iff V p _).mp hmem
  refine ⟨p + (ε / 2) • δ, ?_, hpos, hmass,
    ((homogeneousDecoder_eq_iff V _ p).mp hdec).2⟩
  intro he
  have hz : p + (ε / 2) • δ = p + (0 : ℝ) • δ := by simpa using he
  have := hinj hz
  linarith

/-- At a strictly positive probability row, positivity restores uniqueness
exactly when the full indexed value family is affinely independent. -/
theorem unique_probability_coords_at_positive_iff (V : J → D → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    (∀ q : J → ℝ, (∀ j, 0 ≤ q j) → (∑ j, q j) = 1 →
      (∑ j, q j • V j) = (∑ j, p j • V j) → q = p) ↔
        AffineIndependent ℝ V := by
  constructor
  · intro h
    by_contra hV
    obtain ⟨q, hne, hpos, hmass, hread⟩ :=
      exists_distinct_positive_same_readout V hV p hp hm
    exact hne (h q (fun j => (hpos j).le) hmass hread)
  · intro hV q _ hmass hread
    exact coordinates_unique V hV q p (hmass.trans hm.symm) hread

/-- Every difference of points in a probability fiber is a kernel vector. -/
theorem vectorSpan_probabilityFiber_le_ker (V : J → D → ℝ) (p : J → ℝ) :
    vectorSpan ℝ (probabilityFiber V p) ≤ (homogeneousDecoder V).ker := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro z ⟨q, hq, r, hr, rfl⟩
  have hq' := ((mem_probabilityFiber_iff V p q).mp hq).2.2
  have hr' := ((mem_probabilityFiber_iff V p r).mp hr).2.2
  change homogeneousDecoder V (q - r) = 0
  rw [map_sub, hq', hr', sub_self]

/-- An interior probability fiber spans the entire homogeneous kernel.
This connects its actual affine dimension to rank-nullity. -/
theorem vectorSpan_probabilityFiber_eq_ker (V : J → D → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    vectorSpan ℝ (probabilityFiber V p) = (homogeneousDecoder V).ker := by
  apply le_antisymm (vectorSpan_probabilityFiber_le_ker V p)
  intro δ hδ
  obtain ⟨ε, hε, hpos⟩ := exists_positive_radius p δ hp
  have ht : 0 < ε / 2 := by positivity
  have hsmall : |ε / 2| < ε := by rw [abs_of_pos ht]; linarith
  have hq := kernel_shift_mem_probabilityFiber V p δ hm hδ (ε / 2)
    (fun j => (hpos (ε / 2) hsmall j).le)
  have hpp := self_mem_probabilityFiber V p (fun j => (hp j).le) hm
  have hs : (ε / 2) • δ ∈ vectorSpan ℝ (probabilityFiber V p) := by
    simpa only [vsub_eq_sub, add_sub_cancel_left] using vsub_mem_vectorSpan ℝ hq hpp
  have hi := (vectorSpan ℝ (probabilityFiber V p)).smul_mem (ε / 2)⁻¹ hs
  simpa [smul_smul, ne_of_gt ht] using hi

section Dimension
variable [Fintype D]

/-- Exact affine dimension of the probability fiber through an interior row. -/
theorem fiber_finrank_eq_card_sub_rank (V : J → D → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    Module.finrank ℝ (vectorSpan ℝ (probabilityFiber V p)) =
      Fintype.card J - Module.finrank ℝ (homogeneousDecoder V).range := by
  rw [vectorSpan_probabilityFiber_eq_ker V p hp hm, decoder_nullity_eq]

/-- Ambient head dimension supplies a lower bound, including rank-deficient values. -/
theorem fiber_finrank_lower_bound (V : J → D → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    Fintype.card J - (Fintype.card D + 1) ≤
      Module.finrank ℝ (vectorSpan ℝ (probabilityFiber V p)) := by
  rw [vectorSpan_probabilityFiber_eq_ker V p hp hm]
  exact decoder_nullity_lower_bound V

theorem fiber_finrank_of_full_rank (V : J → D → ℝ)
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1)
    (hrank : Module.finrank ℝ (homogeneousDecoder V).range = Fintype.card D + 1) :
    Module.finrank ℝ (vectorSpan ℝ (probabilityFiber V p)) =
      Fintype.card J - (Fintype.card D + 1) := by
  rw [fiber_finrank_eq_card_sub_rank V p hp hm, hrank]

/-- Long contexts necessarily have distinct interior coordinate representations. -/
theorem long_context_nonunique (V : J → D → ℝ)
    (hcard : Fintype.card D + 1 < Fintype.card J) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1) :
    ∃ q : J → ℝ, q ≠ p ∧ (∀ j, 0 < q j) ∧ (∑ j, q j) = 1 ∧
      (∑ j, q j • V j) = ∑ j, p j • V j :=
  exists_distinct_positive_same_readout V (not_affineIndependent_of_card_gt V hcard) p hp hm

end Dimension

/-- Nonuniqueness for actual unmasked softmax rows, with explicit alternative
finite logits. This permits arbitrary scores, not independently fixed Q,K. -/
theorem softmax_nonidentifiable (V : J → D → ℝ)
    (hV : ¬ AffineIndependent ℝ V) [Nonempty J] (s : J → ℝ)
    (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ t : J → ℝ,
      (fun j => FiniteSoftmax.weight t τ j) ≠ (fun j => FiniteSoftmax.weight s τ j) ∧
      (∑ j, FiniteSoftmax.weight t τ j • V j) =
        ∑ j, FiniteSoftmax.weight s τ j • V j := by
  obtain ⟨q, hne, hpos, hmass, hread⟩ := exists_distinct_positive_same_readout V hV
    (FiniteSoftmax.weight s τ) (FiniteSoftmax.weight_pos s τ) (FiniteSoftmax.weight_sum_one s τ)
  have hreal (j : J) := AttentionAnalogyFiber.softmax_log_probability q hpos hmass τ hτ j
  refine ⟨fun j => τ * Real.log (q j), ?_, ?_⟩
  · simpa only [hreal] using hne
  · simpa only [hreal] using hread

/-- The attachment's explicit collinear values. -/
def collinearValues : Fin 3 → Fin 1 → ℝ := fun j _ => (j.val : ℝ)

def uniformRow : Fin 3 → ℝ := ![1/3, 1/3, 1/3]

def peakedRow : Fin 3 → ℝ := ![1/6, 2/3, 1/6]

/-- Both rows are strictly positive, normalized and distinct, but decode to 1. -/
theorem collinear_counterexample :
    (∀ j, 0 < uniformRow j) ∧ (∀ j, 0 < peakedRow j) ∧
    (∑ j, uniformRow j) = 1 ∧ (∑ j, peakedRow j) = 1 ∧
    uniformRow ≠ peakedRow ∧
    (∑ j, uniformRow j • collinearValues j) = (fun _ => 1) ∧
    (∑ j, peakedRow j • collinearValues j) = (fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j; fin_cases j <;> norm_num [uniformRow]
  · intro j; fin_cases j <;> norm_num [peakedRow]
  · norm_num [uniformRow, Fin.sum_univ_succ]
  · norm_num [peakedRow, Fin.sum_univ_succ]
  · intro h
    have h0 := congrFun h (0 : Fin 3)
    norm_num [uniformRow, peakedRow] at h0
  · funext d
    norm_num [uniformRow, collinearValues, Fin.sum_univ_succ]
  · funext d
    norm_num [peakedRow, collinearValues, Fin.sum_univ_succ]

/-- Explicit softmax logits for both rows of the concrete counterexample. -/
theorem collinear_softmax_realization :
    (fun j => FiniteSoftmax.weight (fun k => Real.log (uniformRow k)) 1 j) = uniformRow ∧
    (fun j => FiniteSoftmax.weight (fun k => Real.log (peakedRow k)) 1 j) = peakedRow := by
  obtain ⟨hp, hq, hmp, hmq, _⟩ := collinear_counterexample
  constructor
  · funext j
    simpa only [one_mul] using
      AttentionAnalogyFiber.softmax_log_probability uniformRow hp hmp 1 one_ne_zero j
  · funext j
    simpa only [one_mul] using
      AttentionAnalogyFiber.softmax_log_probability peakedRow hq hmq 1 one_ne_zero j

end InfoGeometry.Routing.AttentionInteriorFiber
