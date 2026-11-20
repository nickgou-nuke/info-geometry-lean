/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Probability.AitchisonContingency
import InfoGeometry.Convex.LogSumExp

/-!
# Geometric-marginal projection of positive probability tables

Probability points are Mathlib's native `StdSimplex`; the strict positivity
hypotheses used below are separate from its nonnegative normalization contract.
The existing `LogSumExp.softmax` closes the geometric row and column means.
The resulting product table is the unique closest positive independent table
for the explicitly defined squared Euclidean distance between CLR coordinates.
This is a geometric least-squares statement, not a multinomial likelihood claim.
-/

noncomputable section
open scoped BigOperators

namespace InfoGeometry.Probability.AitchisonContingency

open InfoGeometry.Probability.BipartiteLogCoupling
open InfoGeometry.Convex.LogSumExp
open Convexity

/-- The existing softmax, packaged in the native finite probability simplex. -/
def softmaxSimplex {K : Type*} [Fintype K] [Nonempty K] (x : K → ℝ) :
    StdSimplex ℝ K where
  weights := Finsupp.equivFunOnFinite.symm (softmax x)
  nonneg k := by simpa using softmax_nonneg x k
  total := by simpa [Finsupp.sum_fintype] using sum_softmax_eq_one x

@[simp] theorem softmaxSimplex_weights {K : Type*} [Fintype K] [Nonempty K]
    (x : K → ℝ) (k : K) : (softmaxSimplex x).weights k = softmax x k := by
  simp [softmaxSimplex]

theorem softmaxSimplex_pos {K : Type*} [Fintype K] [Nonempty K]
    (x : K → ℝ) (k : K) : 0 < (softmaxSimplex x).weights k := by
  rw [softmaxSimplex_weights]
  exact div_pos (Real.exp_pos _) (sumExp_pos x)

theorem softmaxSimplex_add_const {K : Type*} [Fintype K] [Nonempty K]
    (x : K → ℝ) (c : ℝ) :
    softmaxSimplex (fun k => x k + c) = softmaxSimplex x := by
  apply StdSimplex.ext
  apply Finsupp.ext
  intro k
  simp only [softmaxSimplex_weights]
  have hx : (fun k => x k + c) = x + c • uniformShift := by
    funext k
    simp [uniformShift]
  rw [hx]
  exact congrFun (softmax_add_uniformShift x c) k

theorem log_softmax {K : Type*} [Fintype K] [Nonempty K]
    (x : K → ℝ) (k : K) : Real.log (softmax x k) = x k - lse x := by
  unfold softmax lse
  rw [Real.log_div (Real.exp_pos _).ne' (sumExp_pos x).ne', Real.log_exp]

theorem softmaxSimplex_log {K : Type*} [Fintype K] [Nonempty K]
    (P : StdSimplex ℝ K) (hP : ∀ k, 0 < P.weights k) :
    softmaxSimplex (fun k => Real.log (P.weights k)) = P := by
  have hs : sumExp (fun k => Real.log (P.weights k)) = 1 := by
    unfold sumExp
    simp_rw [Real.exp_log (hP _)]
    exact P.total_of_fintype
  apply StdSimplex.ext
  apply Finsupp.ext
  intro k
  rw [softmaxSimplex_weights]
  change Real.exp (Real.log (P.weights k)) / sumExp (fun k => Real.log (P.weights k)) = _
  rw [Real.exp_log (hP k), hs, div_one]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Native probability product, with its finite normalization proved. -/
def productSimplex (u : StdSimplex ℝ I) (v : StdSimplex ℝ J) :
    StdSimplex ℝ (I × J) where
  weights := Finsupp.equivFunOnFinite.symm (fun ij => u.weights ij.1 * v.weights ij.2)
  nonneg ij := by simpa using mul_nonneg (u.weights_nonneg ij.1) (v.weights_nonneg ij.2)
  total := by
    simp [Finsupp.sum_fintype, Fintype.sum_prod_type, ← Finset.mul_sum]

@[simp] theorem productSimplex_weights (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (i : I) (j : J) : (productSimplex u v).weights (i, j) = u.weights i * v.weights j := by
  simp [productSimplex]

theorem productSimplex_pos (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ j, 0 < v.weights j) (ij : I × J) :
    0 < (productSimplex u v).weights ij := by
  exact mul_pos (hu ij.1) (hv ij.2)

/-- The log-weight matrix of a native probability table. -/
def logMatrix (P : StdSimplex ℝ (I × J)) : Matrix I J ℝ :=
  fun i j => Real.log (P.weights (i, j))

/-- Global arithmetic centering in log coordinates. -/
def centerLog (X : Matrix I J ℝ) : Matrix I J ℝ :=
  fun i j => X i j - grandMean X

/-- Centered log-ratio coordinates. Strict positivity is explicit in the theorems. -/
def clr (P : StdSimplex ℝ (I × J)) : Matrix I J ℝ := centerLog (logMatrix P)

variable [Nonempty I] [Nonempty J]

private theorem card_real_ne_zero (K : Type*) [Fintype K] [Nonempty K] :
    (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

theorem grandMean_sub_const (X : Matrix I J ℝ) (c : ℝ) :
    grandMean (fun i j => X i j - c) = grandMean X - c := by
  unfold grandMean
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [card_real_ne_zero I, card_real_ne_zero J]

theorem centerLog_sub_const (X : Matrix I J ℝ) (c : ℝ) :
    centerLog (fun i j => X i j - c) = centerLog X := by
  ext i j
  simp only [centerLog, grandMean_sub_const]
  ring

theorem totalSum_centerLog (X : Matrix I J ℝ) : totalSumLinear (centerLog X) = 0 := by
  simp only [totalSumLinear, LinearMap.coe_mk, AddHom.coe_mk, centerLog,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold grandMean
  rw [← mul_assoc, mul_div_cancel₀ _
    (mul_ne_zero (card_real_ne_zero I) (card_real_ne_zero J)), sub_self]

omit [Nonempty I] [Nonempty J] in
theorem centerLog_eq_self_of_total_eq_zero (X : Matrix I J ℝ)
    (hX : totalSumLinear X = 0) : centerLog X = X := by
  have hg : grandMean X = 0 := by
    change totalSumLinear X / ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) = 0
    rw [hX, zero_div]
  ext i j
  simp [centerLog, hg]

theorem clr_softmaxSimplex (X : Matrix I J ℝ) :
    clr (softmaxSimplex (fun ij : I × J => X ij.1 ij.2)) = centerLog X := by
  have hl : logMatrix (softmaxSimplex (fun ij : I × J => X ij.1 ij.2)) =
      fun i j => X i j - lse (fun ij : I × J => X ij.1 ij.2) := by
    ext i j
    simp [logMatrix, log_softmax]
  rw [clr, hl, centerLog_sub_const]

theorem softmaxSimplex_clr (P : StdSimplex ℝ (I × J))
    (hP : ∀ ij, 0 < P.weights ij) :
    softmaxSimplex (fun ij : I × J => clr P ij.1 ij.2) = P := by
  change softmaxSimplex (fun ij : I × J =>
    Real.log (P.weights ij) + (-grandMean (logMatrix P))) = P
  rw [softmaxSimplex_add_const, softmaxSimplex_log P hP]

theorem clr_injective (P Q : StdSimplex ℝ (I × J))
    (hP : ∀ ij, 0 < P.weights ij) (hQ : ∀ ij, 0 < Q.weights ij)
    (h : clr P = clr Q) : P = Q := by
  calc
    P = softmaxSimplex (fun ij : I × J => clr P ij.1 ij.2) := (softmaxSimplex_clr P hP).symm
    _ = softmaxSimplex (fun ij : I × J => clr Q ij.1 ij.2) := by rw [h]
    _ = Q := softmaxSimplex_clr Q hQ

theorem totalSum_clr (P : StdSimplex ℝ (I × J)) : totalSumLinear (clr P) = 0 :=
  totalSum_centerLog _

omit [Nonempty I] [Nonempty J] in
theorem sumExp_additive (a : I → ℝ) (b : J → ℝ) :
    sumExp (fun ij : I × J => a ij.1 + b ij.2) = sumExp a * sumExp b := by
  simp only [sumExp, Fintype.sum_prod_type, Real.exp_add, ← Finset.mul_sum,
    ← Finset.sum_mul]

theorem softmaxSimplex_additive (a : I → ℝ) (b : J → ℝ) :
    softmaxSimplex (fun ij : I × J => a ij.1 + b ij.2) =
      productSimplex (softmaxSimplex a) (softmaxSimplex b) := by
  apply StdSimplex.ext
  apply Finsupp.ext
  rintro ⟨i, j⟩
  simp only [softmaxSimplex_weights, productSimplex_weights]
  unfold softmax
  rw [sumExp_additive, Real.exp_add, div_mul_div_comm]

/-- Closure of the row geometric means; these are not arithmetic marginals. -/
def geometricRowMarginal (P : StdSimplex ℝ (I × J)) : StdSimplex ℝ I :=
  softmaxSimplex (rowLogMean (logMatrix P))

/-- Closure of the column geometric means. -/
def geometricColMarginal (P : StdSimplex ℝ (I × J)) : StdSimplex ℝ J :=
  softmaxSimplex (colLogMean (logMatrix P))

/-- The actual product of the closed row and column geometric marginals. -/
def independentProjection (P : StdSimplex ℝ (I × J)) : StdSimplex ℝ (I × J) :=
  productSimplex (geometricRowMarginal P) (geometricColMarginal P)

theorem independentProjection_pos (P : StdSimplex ℝ (I × J)) (ij : I × J) :
    0 < (independentProjection P).weights ij := by
  exact productSimplex_pos _ _ (softmaxSimplex_pos _) (softmaxSimplex_pos _) ij

theorem independentProjection_eq_softmax (P : StdSimplex ℝ (I × J)) :
    independentProjection P = softmaxSimplex (fun ij : I × J =>
      rowLogMean (logMatrix P) ij.1 + colLogMean (logMatrix P) ij.2) :=
  (softmaxSimplex_additive _ _).symm

variable [DecidableEq I] [DecidableEq J]

theorem interaction_centerLog (X : Matrix I J ℝ) :
    interaction (centerLog X) = interaction X := by
  have hs : centerLog X = X + rowShift (fun _ => -grandMean X) + colShift (fun _ => 0) := by
    ext i j
    simp [centerLog, rowShift, colShift, sub_eq_add_neg]
  rw [hs]
  exact interaction_shift X (fun _ => -grandMean X) (fun _ => 0)

theorem additiveProjection_clr_apply (P : StdSimplex ℝ (I × J)) (i : I) (j : J) :
    additiveProjection (clr P) i j =
      rowLogMean (logMatrix P) i + colLogMean (logMatrix P) j - 2 * grandMean (logMatrix P) := by
  rw [additiveProjection_apply]
  change clr P i j - interaction (centerLog (logMatrix P)) i j = _
  rw [interaction_centerLog, interaction_apply]
  simp only [clr, centerLog]
  ring

theorem independentProjection_eq_projected_softmax (P : StdSimplex ℝ (I × J)) :
    independentProjection P = softmaxSimplex (fun ij : I × J =>
      additiveProjection (clr P) ij.1 ij.2) := by
  rw [independentProjection_eq_softmax]
  have h : (fun ij : I × J => rowLogMean (logMatrix P) ij.1 + colLogMean (logMatrix P) ij.2) =
      fun ij : I × J => additiveProjection (clr P) ij.1 ij.2 + 2 * grandMean (logMatrix P) := by
    funext ij
    rw [additiveProjection_clr_apply]
    ring
  rw [h, softmaxSimplex_add_const]

/-- The probability construction realizes the actual orthogonal CLR projection. -/
theorem clr_independentProjection (P : StdSimplex ℝ (I × J)) :
    clr (independentProjection P) = additiveProjection (clr P) := by
  rw [independentProjection_eq_projected_softmax, clr_softmaxSimplex]
  apply centerLog_eq_self_of_total_eq_zero
  rw [additiveProjection_preserves_total, totalSum_clr]

/-- Every genuine positive probability product has additive CLR coordinates. -/
theorem clr_product_mem_additive (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ j, 0 < v.weights j) :
    clr (productSimplex u v) ∈ additiveSubspace := by
  apply (mem_additiveSubspace_iff _).mpr
  refine ⟨fun i => Real.log (u.weights i),
    fun j => Real.log (v.weights j) - grandMean (logMatrix (productSimplex u v)), ?_⟩
  ext i j
  simp only [clr, centerLog, logMatrix, productSimplex_weights, Matrix.add_apply,
    rowShift, colShift]
  rw [Real.log_mul (hu i).ne' (hv j).ne']
  ring

/-- A positive table is reconstructed by closing the sum of its independent
CLR component and its canonical log interaction. This is the normalized
multiplicative decomposition in probability coordinates. -/
theorem independent_interaction_reconstruction (P : StdSimplex ℝ (I × J))
    (hP : ∀ ij, 0 < P.weights ij) :
    P = softmaxSimplex (fun ij : I × J =>
      clr (independentProjection P) ij.1 ij.2 + interaction (logMatrix P) ij.1 ij.2) := by
  have hi : interaction (clr P) = interaction (logMatrix P) := interaction_centerLog _
  have hsplit : clr (independentProjection P) + interaction (logMatrix P) = clr P := by
    rw [clr_independentProjection, additiveProjection_apply, hi, sub_add_cancel]
  calc
    P = softmaxSimplex (fun ij : I × J => clr P ij.1 ij.2) :=
      (softmaxSimplex_clr P hP).symm
    _ = softmaxSimplex (fun ij : I × J =>
        clr (independentProjection P) ij.1 ij.2 + interaction (logMatrix P) ij.1 ij.2) := by
      congr 1
      funext ij
      exact (congrFun (congrFun hsplit ij.1) ij.2).symm

/-- Squared Aitchison distance in the unscaled Euclidean CLR convention. -/
def aitchisonSq (P Q : StdSimplex ℝ (I × J)) : ℝ := frobeniusSq (clr P - clr Q)

/-- Exact decomposition against every positive normalized independent table. -/
theorem independent_pythagorean (P : StdSimplex ℝ (I × J))
    (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (hP : ∀ ij, 0 < P.weights ij)
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ j, 0 < v.weights j) :
    aitchisonSq P (productSimplex u v) = aitchisonSq P (independentProjection P) +
      aitchisonSq (independentProjection P) (productSimplex u v) := by
  have hsplit : clr P = centerLog (clr (independentProjection P) + interaction (logMatrix P)) :=
    (congrArg clr (independent_interaction_reconstruction P hP)).trans
      (clr_softmaxSimplex (clr (independentProjection P) + interaction (logMatrix P)))
  have ht : totalSumLinear (clr (independentProjection P) + interaction (logMatrix P)) = 0 := by
    rw [map_add, totalSum_clr, totalSum_interaction, add_zero]
  rw [centerLog_eq_self_of_total_eq_zero _ ht] at hsplit
  have hr : clr P - clr (independentProjection P) = interaction (logMatrix P) := by
    rw [hsplit]
    abel
  unfold aitchisonSq
  rw [hr, clr_independentProjection]
  have hp := additive_pythagorean (clr P) (clr (productSimplex u v))
    (clr_product_mem_additive u v hu hv)
  have hi : interaction (clr P) = interaction (logMatrix P) := interaction_centerLog _
  rw [hi] at hp
  exact hp

theorem independent_best_approximation (P : StdSimplex ℝ (I × J))
    (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (hP : ∀ ij, 0 < P.weights ij)
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ j, 0 < v.weights j) :
    aitchisonSq P (independentProjection P) ≤ aitchisonSq P (productSimplex u v) := by
  rw [independent_pythagorean P u v hP hu hv]
  exact le_add_of_nonneg_right (frobeniusSq_nonneg _)

/-- Equality in the minimum is equality of native probability tables. -/
theorem independent_best_approximation_eq_iff (P : StdSimplex ℝ (I × J))
    (u : StdSimplex ℝ I) (v : StdSimplex ℝ J)
    (hP : ∀ ij, 0 < P.weights ij)
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ j, 0 < v.weights j) :
    aitchisonSq P (productSimplex u v) = aitchisonSq P (independentProjection P) ↔
      productSimplex u v = independentProjection P := by
  constructor
  · intro h
    have hp := independent_pythagorean P u v hP hu hv
    rw [h] at hp
    have hz : aitchisonSq (independentProjection P) (productSimplex u v) = 0 :=
      add_eq_left.mp hp.symm
    have hc : clr (independentProjection P) = clr (productSimplex u v) :=
      sub_eq_zero.mp ((frobeniusSq_eq_zero _).mp hz)
    exact clr_injective _ _ (productSimplex_pos u v hu hv)
      (independentProjection_pos P) hc.symm
  · intro h
    rw [h]

/-- The residual size is the existing interaction of the original log table. -/
theorem projection_residual_sq (P : StdSimplex ℝ (I × J)) :
    aitchisonSq P (independentProjection P) = frobeniusSq (interaction (logMatrix P)) := by
  rw [aitchisonSq, clr_independentProjection, additiveProjection_apply, sub_sub_cancel]
  rw [clr, interaction_centerLog]

end InfoGeometry.Probability.AitchisonContingency
