/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.AttentionValueCoordinates
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Exact affine analogies in attention-value space

Indices 0,1,2,3 denote the four values in a parallelogram. The traditional
word-analogy names are labels only: the parallelogram equation is an explicit
hypothesis, not an empirical assertion about trained embeddings.

This module reuses the homogeneous decoder and native `AffineIndependent` and
`stdSimplex`. Signed readout is not itself a probability attention row.
-/

noncomputable section
namespace InfoGeometry.Projective.AttentionAnalogyKernel

open InfoGeometry.Projective.AttentionValueCoordinates
open scoped BigOperators

variable {D : Type*}

/-- Exact equality of the two feature displacements. -/
def IsParallelogram (V : Fin 4 → D → ℝ) : Prop :=
  V 1 - V 0 = V 3 - V 2

/-- The first three original values, with their original ordering. -/
def firstThree (V : Fin 4 → D → ℝ) : Fin 3 → D → ℝ := ![V 0, V 1, V 2]

/-- The signed affine extrapolation weights. -/
def extrapolation : Fin 3 → ℝ := ![-1, 1, 1]

/-- The zero-mass four-token dependence direction. -/
def delta : Fin 4 → ℝ := ![-1, 1, 1, -1]

/-- The measured algebraic defect; it need not vanish for a given value table. -/
def defect (V : Fin 4 → D → ℝ) : D → ℝ := -V 0 + V 1 + V 2 - V 3

lemma parallelogram_coordinate {V : Fin 4 → D → ℝ}
    (hV : IsParallelogram V) (d : D) :
    V 3 d = -V 0 d + V 1 d + V 2 d := by
  have h := congrFun hV d
  change V 1 d - V 0 d = V 3 d - V 2 d at h
  linarith

theorem parallelogram_iff_defect_zero (V : Fin 4 → D → ℝ) :
    IsParallelogram V ↔ defect V = 0 := by
  constructor
  · intro h
    funext d
    simp only [defect, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply]
    rw [parallelogram_coordinate h d]
    ring
  · intro h
    funext d
    have hd := congrFun h d
    change -V 0 d + V 1 d + V 2 d - V 3 d = 0 at hd
    change V 1 d - V 0 d = V 3 d - V 2 d
    linarith

theorem parallelogram_translation_iff (V : Fin 4 → D → ℝ) (c : D → ℝ) :
    IsParallelogram (fun j => V j + c) ↔ IsParallelogram V := by
  simp only [IsParallelogram, add_sub_add_right_eq_sub]

@[simp] theorem extrapolation_sum : ∑ j, extrapolation j = 1 := by
  norm_num [extrapolation, Fin.sum_univ_succ]

theorem extrapolation_not_simplex : extrapolation ∉ stdSimplex ℝ (Fin 3) := by
  intro h
  have h0 := h.1 (0 : Fin 3)
  norm_num [extrapolation] at h0

/-- The target has affine coordinates (-1,1,1) in the first three values. -/
theorem extrapolation_readout (V : Fin 4 → D → ℝ) (hV : IsParallelogram V) :
    (∑ j, extrapolation j • firstThree V j) = V 3 := by
  funext d
  simp [extrapolation, firstThree, Fin.sum_univ_succ,
    parallelogram_coordinate hV d] <;> ring

/-- Negative coordinates exclude every probability readout only when the
first three values are affinely independent. -/
theorem no_simplex_extrapolation (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (hind : AffineIndependent ℝ (firstThree V))
    (p : Fin 3 → ℝ) (hp : p ∈ stdSimplex ℝ (Fin 3)) :
    (∑ j, p j • firstThree V j) ≠ V 3 := by
  intro hread
  have hcoeff : p = extrapolation :=
    coordinates_unique (firstThree V) hind p extrapolation
      (hp.2.trans extrapolation_sum.symm)
      (hread.trans (extrapolation_readout V hV).symm)
  exact extrapolation_not_simplex (hcoeff ▸ hp)

@[simp] theorem delta_sum : ∑ j, delta j = 0 := by
  norm_num [delta, Fin.sum_univ_succ]

theorem delta_ne_zero : delta ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  norm_num [delta] at h0

/-- This identity does not assume an exact analogy. -/
theorem delta_readout (V : Fin 4 → D → ℝ) :
    (∑ j, delta j • V j) = defect V := by
  funext d
  simp [delta, defect, Fin.sum_univ_succ] <;> ring

/-- An exact analogy is precisely this nonzero vector's membership in the
actual native linear decoder kernel. -/
theorem parallelogram_iff_delta_mem_ker (V : Fin 4 → D → ℝ) :
    IsParallelogram V ↔ delta ∈ (homogeneousDecoder V).ker := by
  rw [mem_ker_homogeneousDecoder_iff, delta_sum, delta_readout,
    parallelogram_iff_defect_zero]
  simp

theorem parallelogram_not_affineIndependent (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) : ¬ AffineIndependent ℝ V := by
  intro hind
  have hk := (mem_ker_homogeneousDecoder_iff V delta).mp
    ((parallelogram_iff_delta_mem_ker V).mp hV)
  have hz := hind.eq_zero_of_sum_eq_zero hk.1 hk.2 (0 : Fin 4) (Finset.mem_univ _)
  norm_num [delta] at hz

/-- Linear homogeneous readout is invariant along the kernel direction. -/
theorem homogeneous_shift_invariant (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (p : Fin 4 → ℝ) (ε : ℝ) :
    homogeneousDecoder V (p + ε • delta) = homogeneousDecoder V p := by
  have hk : homogeneousDecoder V delta = 0 :=
    (parallelogram_iff_delta_mem_ker V).mp hV
  rw [map_add, map_smul, hk, smul_zero, add_zero]

/-- Approximate analogies have an exact residual formula, not an exact kernel. -/
theorem readout_shift_defect (V : Fin 4 → D → ℝ) (p : Fin 4 → ℝ) (ε : ℝ) :
    (∑ j, (p + ε • delta) j • V j) - (∑ j, p j • V j) = ε • defect V := by
  have hsum : (∑ j, (p + ε • delta) j • V j) =
      (∑ j, p j • V j) + ε • (∑ j, delta j • V j) := by
    simp [Pi.add_apply, Pi.smul_apply, add_smul, mul_smul,
      Finset.sum_add_distrib, Finset.smul_sum]
  rw [hsum, delta_readout]
  abel

theorem norm_readout_shift_defect [Fintype D]
    (V : Fin 4 → D → ℝ) (p : Fin 4 → ℝ) (ε : ℝ) :
    ‖(∑ j, (p + ε • delta) j • V j) - (∑ j, p j • V j)‖ =
      |ε| * ‖defect V‖ := by
  rw [readout_shift_defect, norm_smul, Real.norm_eq_abs]

/-- Collapse the fourth value into the first three using the analogy relation. -/
def collapse (p : Fin 4 → ℝ) : Fin 3 → ℝ := ![p 0 - p 3, p 1 + p 3, p 2 + p 3]

theorem collapse_mass (p : Fin 4 → ℝ) : ∑ j, collapse p j = ∑ j, p j := by
  simp [collapse, Fin.sum_univ_succ] <;> ring

theorem collapse_readout (V : Fin 4 → D → ℝ) (hV : IsParallelogram V)
    (p : Fin 4 → ℝ) :
    (∑ j, collapse p j • firstThree V j) = ∑ j, p j • V j := by
  funext d
  simp [collapse, firstThree, Fin.sum_univ_succ, parallelogram_coordinate hV d] <;> ring

/-- With an independent first triangle, there are no further kernel directions. -/
theorem mem_ker_iff_multiple_delta (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (hind : AffineIndependent ℝ (firstThree V))
    (p : Fin 4 → ℝ) :
    p ∈ (homogeneousDecoder V).ker ↔ ∃ t : ℝ, p = t • delta := by
  constructor
  · intro hp
    obtain ⟨hm, hv⟩ := (mem_ker_homogeneousDecoder_iff V p).mp hp
    have hz := hind.eq_zero_of_sum_eq_zero
      ((collapse_mass p).trans hm) ((collapse_readout V hV p).trans hv)
    have h0 := hz (0 : Fin 3) (Finset.mem_univ _)
    have h1 := hz (1 : Fin 3) (Finset.mem_univ _)
    have h2 := hz (2 : Fin 3) (Finset.mem_univ _)
    norm_num [collapse] at h0 h1 h2
    refine ⟨-p 3, ?_⟩
    funext j
    fin_cases j <;> simp [delta] <;> linarith
  · rintro ⟨t, rfl⟩
    exact (homogeneousDecoder V).ker.smul_mem t
      ((parallelogram_iff_delta_mem_ker V).mp hV)

/-- Coordinate labels for the two observable feature marginals. -/
def firstMarginal (p : Fin 4 → ℝ) : ℝ := p 1 + p 3

def secondMarginal (p : Fin 4 → ℝ) : ℝ := p 2 + p 3

/-- Unnormalized factorization; normalization is not silently assumed. -/
theorem readout_marginal_factorization (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (p : Fin 4 → ℝ) :
    (∑ j, p j • V j) = (∑ j, p j) • V 0 +
      firstMarginal p • (V 1 - V 0) + secondMarginal p • (V 2 - V 0) := by
  funext d
  simp [firstMarginal, secondMarginal, Fin.sum_univ_succ,
    parallelogram_coordinate hV d] <;> ring

theorem normalized_readout_marginals (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (p : Fin 4 → ℝ) (hp : ∑ j, p j = 1) :
    (∑ j, p j • V j) = V 0 + firstMarginal p • (V 1 - V 0) +
      secondMarginal p • (V 2 - V 0) := by
  rw [readout_marginal_factorization V hV p, hp, one_smul]

/-- Equal mass and readout recover precisely the marginals on a nondegenerate
parallelogram, not the joint coupling. -/
theorem equal_readout_iff_equal_marginals (V : Fin 4 → D → ℝ)
    (hV : IsParallelogram V) (hind : AffineIndependent ℝ (firstThree V))
    (p q : Fin 4 → ℝ) (hm : (∑ j, p j) = ∑ j, q j) :
    (∑ j, p j • V j) = (∑ j, q j • V j) ↔
      firstMarginal p = firstMarginal q ∧ secondMarginal p = secondMarginal q := by
  constructor
  · intro hv
    have hc : collapse p = collapse q := coordinates_unique (firstThree V) hind
      (collapse p) (collapse q)
      ((collapse_mass p).trans (hm.trans (collapse_mass q).symm))
      ((collapse_readout V hV p).trans (hv.trans (collapse_readout V hV q).symm))
    constructor
    · simpa [collapse, firstMarginal] using congrFun hc (1 : Fin 3)
    · simpa [collapse, secondMarginal] using congrFun hc (2 : Fin 3)
  · rintro ⟨h1, h2⟩
    rw [readout_marginal_factorization V hV p, readout_marginal_factorization V hV q,
      hm, h1, h2]

end InfoGeometry.Projective.AttentionAnalogyKernel
