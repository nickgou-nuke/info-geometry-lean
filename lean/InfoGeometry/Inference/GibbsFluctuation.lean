/-
Copyright (c) 2024-2026 Nikolay Goutev and Dimitar Tonev.
Institute for Nuclear Research and Nuclear Energy (INRNE-BAS),
Bulgarian Academy of Sciences.

Authors: Nikolay Goutev, Dimitar Tonev
-/

import InfoGeometry.Inference.FiniteGibbsInference
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Gibbs fluctuation pressure

This module formalizes the scalar part of the information-geometric curvature
decomposition. The fluctuation term is a weighted variance divided by the
positive temperature; the exact scalar curvature is defined as stiffness minus
fluctuation pressure.
-/

open scoped BigOperators

namespace InfoGeometry.Inference

variable {Data : Type*} [Fintype Data]

/-- Weighted mean of a scalar observable. -/
noncomputable def weightedMean (w f : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * f i

/-- Weighted variance around the weighted mean. -/
noncomputable def weightedVariance (w f : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * (f i - weightedMean w f) ^ 2

theorem weightedVariance_nonneg
    (w f : Data → ℝ) (hw : ∀ i, 0 ≤ w i) :
    0 ≤ weightedVariance w f := by
  unfold weightedVariance
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i) (sq_nonneg _)

/--
The weighted variance is the pairwise squared-disagreement energy on the
finite probability simplex.  This is the exact finite analogue of the
dispersion/phase-separation quantity used by the Gibbs diagnostics.
-/
theorem weightedVariance_eq_half_pairwise
    (w f : Data → ℝ) (hw : ∑ i : Data, w i = 1) :
    weightedVariance w f =
      (1 / 2 : ℝ) * ∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2 := by
  classical
  let m : ℝ := weightedMean w f
  have hsum : ∑ i : Data, w i = 1 := hw
  have hsumf : ∑ i : Data, w i * f i = m := by rfl
  have hfactor (a b : Data → ℝ) :
      (∑ i : Data, a i) * (∑ j : Data, b j) =
        ∑ i : Data, ∑ j : Data, a i * b j := by
    exact Finset.sum_mul_sum (Finset.univ : Finset Data) (Finset.univ : Finset Data) a b
  have hconst : ∑ i : Data, w i * m ^ 2 = m ^ 2 := by
    rw [← Finset.sum_mul]
    rw [hsum]
    ring
  have hcross : ∑ i : Data, w i * (2 * f i * m) = 2 * m ^ 2 := by
    calc
      _ = ∑ i : Data, (2 * m) * (w i * f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (2 * m) * ∑ i : Data, w i * f i := by
        rw [Finset.mul_sum]
      _ = 2 * m ^ 2 := by rw [hsumf]; ring
  have hleft :
      ∑ i : Data, w i * (f i - m) ^ 2 =
        (∑ i : Data, w i * f i ^ 2) - m ^ 2 := by
    simp_rw [sub_sq]
    simp only [mul_sub, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcross, hconst]
    ring
  rw [show weightedVariance w f = ∑ i : Data, w i * (f i - m) ^ 2 by rfl, hleft]
  have hdouble :
      ∑ i : Data, ∑ j : Data, w i * w j * (f i - f j) ^ 2 =
        2 * ((∑ i : Data, w i * f i ^ 2) - m ^ 2) := by
    simp_rw [sub_sq]
    simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hA :
        ∑ i : Data, ∑ j : Data, w i * w j * f i ^ 2 =
          ∑ i : Data, w i * f i ^ 2 := by
      calc
        _ = ∑ i : Data, ∑ j : Data, (w i * f i ^ 2) * w j := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ i : Data, w i * f i ^ 2) * (∑ j : Data, w j) := by
          exact (hfactor (fun i : Data => w i * f i ^ 2) w).symm
        _ = ∑ i : Data, w i * f i ^ 2 := by rw [hsum]; ring
    have hC :
        ∑ i : Data, ∑ j : Data, w i * w j * f j ^ 2 =
          ∑ j : Data, w j * f j ^ 2 := by
      calc
        _ = ∑ i : Data, ∑ j : Data, w i * (w j * f j ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ i : Data, w i) * (∑ j : Data, w j * f j ^ 2) := by
          exact (hfactor w (fun j : Data => w j * f j ^ 2)).symm
        _ = ∑ j : Data, w j * f j ^ 2 := by rw [hsum]; ring
    have hscale (q : Data → ℝ) :
        2 * (∑ i : Data, q i) = ∑ i : Data, 2 * q i := by
      calc
        _ = (∑ i : Data, q i) * 2 := by ring
        _ = ∑ i : Data, q i * 2 := by rw [Finset.sum_mul]
        _ = ∑ i : Data, 2 * q i := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    have hB :
        ∑ i : Data, ∑ j : Data, w i * w j * (2 * f i * f j) =
          2 * m ^ 2 := by
      calc
        _ = ∑ i : Data, ∑ j : Data, 2 * ((w i * f i) * (w j * f j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = 2 * (∑ i : Data, ∑ j : Data, (w i * f i) * (w j * f j)) := by
          calc
            _ = ∑ i : Data, 2 * (∑ j : Data, (w i * f i) * (w j * f j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (hscale (fun j : Data => (w i * f i) * (w j * f j))).symm
            _ = _ := (hscale (fun i : Data => ∑ j : Data, (w i * f i) * (w j * f j))).symm
        _ = 2 * ((∑ i : Data, w i * f i) * (∑ j : Data, w j * f j)) := by
          rw [hfactor (fun i : Data => w i * f i) (fun j : Data => w j * f j)]
        _ = 2 * m ^ 2 := by rw [hsumf]; ring
    rw [hA, hB, hC]
    ring
  rw [hdouble]
  ring

/--
With strictly positive weights, zero pairwise dispersion is equivalent to
agreement of the observable on every pair of finite data points.
-/
theorem weightedVariance_eq_zero_iff_of_pos
    (w f : Data → ℝ) (hw : ∑ i : Data, w i = 1)
    (hwpos : ∀ i, 0 < w i) :
    weightedVariance w f = 0 ↔ ∀ i j, f i = f j := by
  constructor
  · intro hzero i j
    have hnonneg : ∀ i j, 0 ≤ w i * w j * (f i - f j) ^ 2 := by
      intro i j
      exact mul_nonneg (mul_nonneg (hwpos i).le (hwpos j).le) (sq_nonneg _)
    have hdouble : ∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2 = 0 := by
      have hpair := weightedVariance_eq_half_pairwise w f hw
      rw [hzero] at hpair
      linarith
    have houter : ∀ i, ∑ j : Data, w i * w j * (f i - f j) ^ 2 = 0 := by
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset Data)) (f := fun i =>
          ∑ j : Data, w i * w j * (f i - f j) ^ 2) (by
            intro i hi
            exact Finset.sum_nonneg (fun j hj => hnonneg i j))).mp hdouble
      intro i
      exact hsum i (Finset.mem_univ i)
    have hterm : w i * w j * (f i - f j) ^ 2 = 0 := by
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset Data)) (f := fun j =>
          w i * w j * (f i - f j) ^ 2) (by
            intro j hj
            exact hnonneg i j)).mp (houter i)
      exact hsum j (Finset.mem_univ j)
    have hsq : (f i - f j) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with hcoef | hsq
      · rcases mul_eq_zero.mp hcoef with hi0 | hj0
        · exact False.elim ((ne_of_gt (hwpos i)) hi0)
        · exact False.elim ((ne_of_gt (hwpos j)) hj0)
      · exact hsq
    exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hsq)
  · intro hconst
    rw [weightedVariance_eq_half_pairwise w f hw]
    have hdouble : ∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      rw [hconst i j]
      simp
    rw [hdouble]
    ring

/-- Weighted scalar stiffness, supplied by the per-observation curvature. -/
noncomputable def fisherStiffness (w h₂ : Data → ℝ) : ℝ :=
  ∑ i : Data, w i * h₂ i

/-- Fluctuation pressure at temperature `ε`. -/
noncomputable def fluctuationPressure (w f : Data → ℝ) (ε : ℝ) : ℝ :=
  weightedVariance w f / ε

/-- Exact scalar curvature in the `A - B` decomposition. -/
noncomputable def exactScalarHessian
    (w h₂ f : Data → ℝ) (ε : ℝ) : ℝ :=
  fisherStiffness w h₂ - fluctuationPressure w f ε

theorem fluctuationPressure_nonneg
    (w f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∀ i, 0 ≤ w i) :
    0 ≤ fluctuationPressure w f ε := by
  unfold fluctuationPressure
  exact div_nonneg (weightedVariance_nonneg w f hw) hε.le

/--
At positive temperature, fluctuation pressure is the pairwise disagreement
energy divided by `2 ε`.
-/
theorem fluctuationPressure_eq_half_pairwise
    (w f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∑ i : Data, w i = 1) :
    fluctuationPressure w f ε =
      (1 / (2 * ε) : ℝ) * ∑ i : Data, ∑ j : Data,
        w i * w j * (f i - f j) ^ 2 := by
  unfold fluctuationPressure
  rw [weightedVariance_eq_half_pairwise w f hw]
  field_simp [ne_of_gt hε]

/--
For positive temperature and strictly positive weights, zero fluctuation
pressure is exactly the finite-data coherence condition.
-/
theorem fluctuationPressure_eq_zero_iff_of_pos
    (w f : Data → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hw : ∑ i : Data, w i = 1) (hwpos : ∀ i, 0 < w i) :
    fluctuationPressure w f ε = 0 ↔ ∀ i j, f i = f j := by
  constructor
  · intro hzero
    apply (weightedVariance_eq_zero_iff_of_pos w f hw hwpos).mp
    exact (div_eq_zero_iff.mp hzero).resolve_right (ne_of_gt hε)
  · intro hconst
    unfold fluctuationPressure
    rw [(weightedVariance_eq_zero_iff_of_pos w f hw hwpos).mpr hconst]
    simp

theorem gibbsFluctuationPressure_nonneg
    {Theta : Type*} [Nonempty Data]
    (M : FiniteGibbs.Model (Data := Data) (Theta := Theta))
    (θ : Theta) (ε : ℝ) (hε : 0 < ε) (f : Data → ℝ) :
    0 ≤ fluctuationPressure (FiniteGibbs.weight M θ ε) f ε := by
  exact fluctuationPressure_nonneg
    (FiniteGibbs.weight M θ ε) f ε hε
    (fun i => (FiniteGibbs.weight_pos M θ ε i).le)

end InfoGeometry.Inference
