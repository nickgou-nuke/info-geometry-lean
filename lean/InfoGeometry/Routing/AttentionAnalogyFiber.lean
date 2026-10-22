/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionAnalogyKernel
import InfoGeometry.Routing.FiniteSoftmax

/-!
# Probability and softmax fibers of an exact analogy

The closed simplex includes zero-weight boundary rows; finite unmasked softmax
is strictly positive. Both cases are treated explicitly. Log-softmax inversion
uses arbitrary scores, not a claim of realizability with fixed query/key maps.
The full two-marginal coupling interval is an extension of the centered example.
-/

noncomputable section
namespace InfoGeometry.Routing.AttentionAnalogyFiber

open InfoGeometry.Projective.AttentionValueCoordinates
open InfoGeometry.Projective.AttentionAnalogyKernel
open scoped BigOperators

variable {D : Type*}

/-- The centered line of four-token distributions. -/
def fiber (ε : ℝ) : Fin 4 → ℝ := ![1/4-ε, 1/4+ε, 1/4+ε, 1/4-ε]

@[simp] theorem fiber_sum (ε : ℝ) : ∑ j, fiber ε j = 1 := by
  simp [fiber, Fin.sum_univ_succ] <;> ring

theorem fiber_eq_shift (ε : ℝ) : fiber ε = fiber 0 + ε • delta := by
  funext j
  fin_cases j <;> simp [fiber, delta] <;> ring

theorem fiber_injective : Function.Injective fiber := by
  intro ε η h
  have h1 := congrFun h (1 : Fin 4)
  norm_num [fiber] at h1
  linarith

/-- The exact closed feasibility interval. -/
theorem fiber_mem_simplex_iff (ε : ℝ) :
    fiber ε ∈ stdSimplex ℝ (Fin 4) ↔ -1/4 ≤ ε ∧ ε ≤ 1/4 := by
  constructor
  · intro h
    have h0 := h.1 (0 : Fin 4)
    have h1 := h.1 (1 : Fin 4)
    norm_num [fiber] at h0 h1
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, fiber_sum ε⟩
    intro j
    fin_cases j <;> simp [fiber] <;> linarith

/-- The strict interval is exactly the finite unmasked-softmax regime. -/
theorem fiber_pos_iff (ε : ℝ) :
    (∀ j, 0 < fiber ε j) ↔ -1/4 < ε ∧ ε < 1/4 := by
  constructor
  · intro h
    have h0 := h (0 : Fin 4)
    have h1 := h (1 : Fin 4)
    norm_num [fiber] at h0 h1
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩ j
    fin_cases j <;> simp [fiber] <;> linarith

theorem fiber_homogeneous_invariant (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (ε : ℝ) :
    homogeneousDecoder V (fiber ε) = homogeneousDecoder V (fiber 0) := by
  rw [fiber_eq_shift]
  exact homogeneous_shift_invariant V hV (fiber 0) ε

theorem fiber_readout_invariant (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (ε : ℝ) :
    (∑ j, fiber ε j • V j) = ∑ j, fiber 0 j • V j :=
  ((homogeneousDecoder_eq_iff V _ _).mp (fiber_homogeneous_invariant V hV ε)).2

theorem fiber_readout_midpoint (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (ε : ℝ) :
    (∑ j, fiber ε j • V j) = (1/2 : ℝ) • V 1 + (1/2 : ℝ) • V 2 := by
  rw [fiber_readout_invariant V hV ε]
  funext d
  simp [fiber, Fin.sum_univ_succ, parallelogram_coordinate hV d] <;> ring

@[simp] theorem fiber_left_endpoint : fiber (-1/4) = ![1/2, 0, 0, 1/2] := by
  funext j
  fin_cases j <;> norm_num [fiber]

@[simp] theorem fiber_right_endpoint : fiber (1/4) = ![0, 1/2, 1/2, 0] := by
  funext j
  fin_cases j <;> norm_num [fiber]

/-- Every strictly positive probability row has a finite logit representative
in the existing softmax owner, at any nonzero temperature. -/
theorem softmax_log_probability {J : Type*} [Fintype J]
    (p : J → ℝ) (hp : ∀ j, 0 < p j) (hm : ∑ j, p j = 1)
    (τ : ℝ) (hτ : τ ≠ 0) (j : J) :
    FiniteSoftmax.weight (fun k => τ * Real.log (p k)) τ j = p j := by
  have he (k : J) : Real.exp ((τ * Real.log (p k)) / τ) = p k := by
    have ht : (τ * Real.log (p k)) / τ = Real.log (p k) := by field_simp [hτ]
    rw [ht, Real.exp_log (hp k)]
  simp only [FiniteSoftmax.weight, FiniteSoftmax.partitionZ, he, hm, div_one]

/-- The whole interior fiber consists of actual softmax rows for explicit logits. -/
theorem fiber_softmax_realization (ε τ : ℝ)
    (hε : -1/4 < ε ∧ ε < 1/4) (hτ : τ ≠ 0) :
    (fun j => FiniteSoftmax.weight (fun k => τ * Real.log (fiber ε k)) τ j) =
      fiber ε := by
  funext j
  exact softmax_log_probability (fiber ε) ((fiber_pos_iff ε).mpr hε) (fiber_sum ε) τ hτ j

/-- The first boundary row in the proposed signed two-head identity. -/
def midpointHead : Fin 3 → ℝ := ![0, 1/2, 1/2]

def baseHead : Fin 3 → ℝ := ![1, 0, 0]

theorem boundary_heads_simplex :
    midpointHead ∈ stdSimplex ℝ (Fin 3) ∧ baseHead ∈ stdSimplex ℝ (Fin 3) := by
  constructor <;> constructor
  · intro j; fin_cases j <;> norm_num [midpointHead]
  · norm_num [midpointHead, Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [baseHead]
  · norm_num [baseHead, Fin.sum_univ_succ]

theorem signed_boundary_heads (V : Fin 4 → D → ℝ) (hV : IsParallelogram V) :
    (2 : ℝ) • (∑ j, midpointHead j • firstThree V j) -
      (∑ j, baseHead j • firstThree V j) = V 3 := by
  funext d
  simp [midpointHead, baseHead, firstThree, Fin.sum_univ_succ,
    parallelogram_coordinate hV d] <;> ring

/-- No finite, unmasked softmax row is the zero-containing midpoint head. -/
theorem midpointHead_not_unmasked_softmax (s : Fin 3 → ℝ) (τ : ℝ) :
    (fun j => FiniteSoftmax.weight s τ j) ≠ midpointHead := by
  intro h
  have hp := FiniteSoftmax.weight_pos s τ (0 : Fin 3)
  have h0 := congrFun h (0 : Fin 3)
  rw [h0] at hp
  norm_num [midpointHead] at hp

/-- An exact signed realization can instead use strictly positive rows. -/
def positiveHead : Fin 3 → ℝ := ![1/9, 4/9, 4/9]

def negativeHead : Fin 3 → ℝ := ![2/3, 1/6, 1/6]

theorem positive_heads_pos :
    (∀ j, 0 < positiveHead j) ∧ (∀ j, 0 < negativeHead j) := by
  constructor <;> intro j <;> fin_cases j <;> norm_num [positiveHead, negativeHead]

theorem positive_heads_mass : (∑ j, positiveHead j) = 1 ∧
    (∑ j, negativeHead j) = 1 := by
  constructor <;> norm_num [positiveHead, negativeHead, Fin.sum_univ_succ]

theorem signed_positive_heads (V : Fin 4 → D → ℝ) (hV : IsParallelogram V) :
    (3 : ℝ) • (∑ j, positiveHead j • firstThree V j) -
      (2 : ℝ) • (∑ j, negativeHead j • firstThree V j) = V 3 := by
  funext d
  simp [positiveHead, negativeHead, firstThree, Fin.sum_univ_succ,
    parallelogram_coordinate hV d] <;> ring

/-- Two genuine finite-softmax rows, with a separately specified signed output map. -/
theorem signed_softmax_heads (V : Fin 4 → D → ℝ) (hV : IsParallelogram V) :
    (3 : ℝ) • (∑ j, FiniteSoftmax.weight (fun k => Real.log (positiveHead k)) 1 j •
      firstThree V j) -
    (2 : ℝ) • (∑ j, FiniteSoftmax.weight (fun k => Real.log (negativeHead k)) 1 j •
      firstThree V j) = V 3 := by
  have hp (j : Fin 3) := softmax_log_probability positiveHead positive_heads_pos.1
    positive_heads_mass.1 1 one_ne_zero j
  have hn (j : Fin 3) := softmax_log_probability negativeHead positive_heads_pos.2
    positive_heads_mass.2 1 one_ne_zero j
  simp only [one_mul] at hp hn
  simp_rw [hp, hn]
  exact signed_positive_heads V hV

/-- General two-feature coupling with joint (1,1) mass t. -/
def coupling (a b t : ℝ) : Fin 4 → ℝ := ![1-a-b+t, a-t, b-t, t]

@[simp] theorem coupling_sum (a b t : ℝ) : ∑ j, coupling a b t j = 1 := by
  simp [coupling, Fin.sum_univ_succ] <;> ring

@[simp] theorem coupling_firstMarginal (a b t : ℝ) :
    firstMarginal (coupling a b t) = a := by simp [firstMarginal, coupling]

@[simp] theorem coupling_secondMarginal (a b t : ℝ) :
    secondMarginal (coupling a b t) = b := by simp [secondMarginal, coupling]

/-- Every mass-one row is determined by its two marginals and one joint mass. -/
theorem eq_coupling_of_mass_one (p : Fin 4 → ℝ) (hp : ∑ j, p j = 1) :
    p = coupling (firstMarginal p) (secondMarginal p) (p 3) := by
  have hm := hp
  simp [Fin.sum_univ_succ] at hm
  funext j
  fin_cases j <;> simp [coupling, firstMarginal, secondMarginal] <;> linarith

/-- Exact Frechet feasibility bounds on the unobserved joint coupling. -/
theorem coupling_mem_simplex_iff (a b t : ℝ) :
    coupling a b t ∈ stdSimplex ℝ (Fin 4) ↔
      max 0 (a+b-1) ≤ t ∧ t ≤ min a b := by
  constructor
  · intro h
    have h0 := h.1 (0 : Fin 4)
    have h1 := h.1 (1 : Fin 4)
    have h2 := h.1 (2 : Fin 4)
    have h3 := h.1 (3 : Fin 4)
    norm_num [coupling] at h0 h1 h2 h3
    exact ⟨max_le h3 (by linarith), le_min (by linarith) (by linarith)⟩
  · rintro ⟨hlo, hhi⟩
    have h0 : 0 ≤ t := le_trans (le_max_left _ _) hlo
    have h1 : a+b-1 ≤ t := le_trans (le_max_right _ _) hlo
    have h2 : t ≤ a := le_trans hhi (min_le_left _ _)
    have h3 : t ≤ b := le_trans hhi (min_le_right _ _)
    refine ⟨?_, coupling_sum a b t⟩
    intro j
    fin_cases j <;> simp [coupling] <;> linarith

/-- The readout discards precisely the coupling parameter in this family. -/
theorem coupling_readout (V : Fin 4 → D → ℝ) (hV : IsParallelogram V)
    (a b t : ℝ) :
    (∑ j, coupling a b t j • V j) = V 0 + a • (V 1 - V 0) + b • (V 2 - V 0) := by
  rw [normalized_readout_marginals V hV _ (coupling_sum a b t),
    coupling_firstMarginal, coupling_secondMarginal]

/-- The centered example is the (1/2,1/2) marginal fiber. -/
theorem fiber_eq_coupling (ε : ℝ) : fiber ε = coupling (1/2) (1/2) (1/4-ε) := by
  funext j
  fin_cases j <;> simp [fiber, coupling] <;> ring

end InfoGeometry.Routing.AttentionAnalogyFiber
