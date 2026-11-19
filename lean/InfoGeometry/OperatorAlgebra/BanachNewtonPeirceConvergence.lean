/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Banach-Algebra Super-Convergence of the Newton–Peirce Flow

Analytical closure of Bucket 3 from
`InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry`:
while algebraic termination of `newtonPeirceStep^[k] x` required nilpotency of
`idempotencyDefect x`, over any `[NormedRing B]` (without assuming `NormOneClass B`)
quadratic defect shrinkage controls step sizes whenever `‖idempotencyDefect x‖ < 1 / 6`.
When `[CompleteSpace B]` holds, the iterates converge to a genuine idempotent
`e : B` preserving commutators, one-sided supports, annihilators, and intertwiners.

## Three-Bucket Audit Map

* **BUCKET 1 (Reused upstream owners)**:
  - `InfoGeometry.Core.IdempotentGraphGrassmannian`: `idempotencyDefect`,
    `newtonPeirceStep`, `idempotencyDefect_newtonPeirceStep`.
  - `InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry`:
    `newtonPeirceStep_iterates_intertwines`, `newtonPeirceStep_iterates_left_support`,
    `newtonPeirceStep_iterates_right_support`, `newtonPeirceStep_iterates_left_annihilated`,
    `newtonPeirceStep_iterates_right_annihilated`.
  - `InfoGeometry.MetaCompiler`: `TypedArchetype`, `Phase`, `#register_archetype`,
    `#audit_archetype`.
* **BUCKET 2 (New analytic theorems proved here)**:
  - Norm-one-free `[NormedRing B]` bounds `norm_newtonPeirceStep_sub_self_le`,
    `norm_idempotencyDefect_newtonPeirceStep_le`, quadratic `2 ^ k`-exponent defect
    bound `four_mul_norm_idempotencyDefect_iterate_le_two_pow`, and Cauchy criterion
    `newtonPeirceStep_iterate_cauchySeq` for `‖idempotencyDefect x‖ < 1 / 6`.
  - Complete Banach-algebra limit `banach_newtonPeirce_limit_idempotent_and_intertwiner`
    yielding `e * e = e`, `Commute x e`, intertwiner transport, and support/annihilator
    persistence.
  - Concrete non-nilpotent oblique operator witness on `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)`
    proving `(idempotencyDefect clmPerturbedSeed) ^ (n + 1) ≠ 0` for all `n : ℕ`
    alongside norm-convergent Newton–Peirce healing (`‖δ‖ ≤ 9 / 100 < 1 / 6`).
* **BUCKET 3 (Out-of-scope / excluded)**:
  - Global basin-of-attraction classification beyond `‖idempotencyDefect x‖ < 1 / 6` and
    unbounded spectral resolutions outside `[NormedRing B]`.
-/

namespace InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence

open Filter Topology
open InfoGeometry.Core.IdempotentGraphGrassmannian
open InfoGeometry.OperatorAlgebra.PeirceBruhatAporiaTowerAndMatrixGeometry
open InfoGeometry.MetaCompiler

section ScalarHelpers

private theorem scalar_one_add_two_mul_le {a m d : ℝ}
    (h1 : a ≤ d + (m * d + m * d)) : a ≤ (1 + 2 * m) * d := by
  linarith [h1]

private theorem scalar_three_add_four_mul {u v d : ℝ}
    (hu : u ≤ (d * d) * d) (hv : v ≤ d * d) :
    ((u + u) + (u + u)) + (v + v + v) ≤ d ^ 2 * (3 + 4 * d) := by
  nlinarith [hu, hv, sq_nonneg d]

private theorem scalar_cubic_defect_le_four_sq {d : ℝ} (hd4 : d ≤ 1 / 4) :
    d ^ 2 * (3 + 4 * d) ≤ 4 * d ^ 2 := by
  nlinarith [hd4, sq_nonneg d]

private theorem scalar_four_mul_sq_step {c d q : ℝ} (hc : c ≤ 4 * d ^ 2)
    (hq : 4 * d ≤ q) (hd0 : 0 ≤ d) : 4 * c ≤ q ^ 2 := by
  have h16 : (4 * d) ^ 2 ≤ q ^ 2 := by
    have hq0 : 0 ≤ q := by linarith [hq, hd0]
    nlinarith [hq, hd0, hq0]
  nlinarith [hc, h16]

private theorem scalar_four_mul_le_one {d : ℝ} (h : d ≤ 1 / 4) : 4 * d ≤ 1 := by
  linarith [h]

private theorem scalar_div_four_le_init {c d p : ℝ} (hc : 4 * c ≤ p) (hp : p ≤ 4 * d) :
    c ≤ d := by
  linarith [hc, hp]

private theorem scalar_four_mul_lt_one {d : ℝ} (h : d < 1 / 4) : 4 * d < 1 := by
  linarith [h]

private theorem scalar_next_step_ratio
    {d0 d1 d2 m1 m2 : ℝ}
    (hd0_lt : d0 < 1 / 6)
    (hd1_nn : 0 ≤ d1) (hd1_le : d1 ≤ d0)
    (hd2_nn : 0 ≤ d2) (hd2_le : d2 ≤ 4 * d1 ^ 2)
    (hm1_nn : 0 ≤ m1)
    (hm2_le : m2 ≤ m1 + (1 + 2 * m1) * d1) :
    (1 + 2 * m2) * d2 ≤ (6 * d0) * ((1 + 2 * m1) * d1) := by
  have h1m1 : 0 ≤ 1 + 2 * m1 := by linarith [hm1_nn]
  have h1d1 : 0 ≤ 1 + 2 * d1 := by linarith [hd1_nn]
  have hm2_prod : (1 + 2 * m2) ≤ (1 + 2 * m1) * (1 + 2 * d1) := by
    nlinarith [hm2_le, h1m1, hd1_nn]
  have hcoef : 4 * (1 + 2 * d1) * d1 ≤ 6 * d0 := by
    have hd1_lt : d1 < 1 / 6 := lt_of_le_of_lt hd1_le hd0_lt
    nlinarith [hd1_nn, hd1_le, hd1_lt]
  have hsq :
      (1 + 2 * m1) * (1 + 2 * d1) * (4 * d1 ^ 2) =
        (4 * (1 + 2 * d1) * d1) * ((1 + 2 * m1) * d1) := by
    ring
  calc
    (1 + 2 * m2) * d2
        ≤ (1 + 2 * m1) * (1 + 2 * d1) * d2 :=
          mul_le_mul_of_nonneg_right hm2_prod hd2_nn
    _ ≤ (1 + 2 * m1) * (1 + 2 * d1) * (4 * d1 ^ 2) :=
          mul_le_mul_of_nonneg_left hd2_le (mul_nonneg h1m1 h1d1)
    _ = (4 * (1 + 2 * d1) * d1) * ((1 + 2 * m1) * d1) := hsq
    _ ≤ (6 * d0) * ((1 + 2 * m1) * d1) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg h1m1 hd1_nn)

private theorem scalar_one_sixth_lt_one_fourth {d : ℝ} (hd : d < 1 / 6) : d < 1 / 4 := by
  linarith [hd]

private theorem scalar_six_mul_lt_one {d : ℝ} (hd : d < 1 / 6) : 6 * d < 1 := by
  linarith [hd]

private theorem scalar_nonneg_six_mul {d : ℝ} (hd : 0 ≤ d) : 0 ≤ 6 * d := by
  linarith [hd]

private theorem scalar_geom_assoc (a q d p : ℝ) :
    q * ((a * d) * p) = (a * d) * (q * p) := by
  ring

private theorem scalar_seed_defect_0 (x y : ℝ) :
    (x + (1 / 10 : ℝ) * y + (1 / 10 : ℝ) * ((1 / 10 : ℝ) * y)) - (x + (1 / 10 : ℝ) * y) =
      (1 / 100 : ℝ) * y := by
  ring

private theorem scalar_seed_defect_1 (y : ℝ) :
    (1 / 10 : ℝ) * ((1 / 10 : ℝ) * y) - (1 / 10 : ℝ) * y = -(9 / 100 : ℝ) * y := by
  ring

private theorem scalar_pow_step (a b : ℝ) : a * (a * b) = (a * a) * b := by
  ring

private theorem scalar_coord0_nine_hundredths {u v : ℝ} (hv : |u| ≤ v) :
    |(1 / 100 : ℝ) * u| ≤ (9 / 100 : ℝ) * v := by
  rw [abs_mul]
  have h1 : |(1 / 100 : ℝ)| = 1 / 100 := by norm_num
  rw [h1]
  nlinarith [hv, abs_nonneg u]

private theorem scalar_coord1_nine_hundredths {u v : ℝ} (hv : |u| ≤ v) :
    |-(9 / 100 : ℝ) * u| ≤ (9 / 100 : ℝ) * v := by
  rw [abs_mul, abs_neg]
  have h9 : |(9 / 100 : ℝ)| = 9 / 100 := by norm_num
  rw [h9]
  nlinarith [hv, abs_nonneg u]

private theorem scalar_norm_nine_hundredths : (9 / 100 : ℝ) < 1 / 6 := by
  norm_num

end ScalarHelpers

section NormedRingBounds

variable {B : Type*} [NormedRing B]

/-- Exact ring identity separating a Newton–Peirce step from its input by
`idempotencyDefect x`. -/
theorem newtonPeirceStep_sub_self {R : Type*} [Ring R] (x : R) :
    newtonPeirceStep x - x = idempotencyDefect x - 2 * x * idempotencyDefect x := by
  unfold newtonPeirceStep idempotencyDefect
  noncomm_ring

/-- Norm-one-free step-size estimate in any `[NormedRing B]`. -/
theorem norm_newtonPeirceStep_sub_self_le (x : B) :
    ‖newtonPeirceStep x - x‖ ≤ (1 + 2 * ‖x‖) * ‖idempotencyDefect x‖ := by
  rw [newtonPeirceStep_sub_self]
  have h2x : (2 : B) * x * idempotencyDefect x =
      x * idempotencyDefect x + x * idempotencyDefect x := by
    noncomm_ring
  rw [h2x]
  have hmul :
      ‖x * idempotencyDefect x + x * idempotencyDefect x‖ ≤
        ‖x‖ * ‖idempotencyDefect x‖ + ‖x‖ * ‖idempotencyDefect x‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
  have htri :
      ‖idempotencyDefect x - (x * idempotencyDefect x + x * idempotencyDefect x)‖ ≤
        ‖idempotencyDefect x‖ +
          (‖x‖ * ‖idempotencyDefect x‖ + ‖x‖ * ‖idempotencyDefect x‖) :=
    (norm_sub_le _ _).trans (add_le_add le_rfl hmul)
  exact scalar_one_add_two_mul_le htri

/-- Cubic-quadratic norm contraction inequality for a single Newton–Peirce step
in any `[NormedRing B]`. -/
theorem norm_idempotencyDefect_newtonPeirceStep_le (x : B) :
    ‖idempotencyDefect (newtonPeirceStep x)‖ ≤
      ‖idempotencyDefect x‖ ^ 2 * (3 + 4 * ‖idempotencyDefect x‖) := by
  rw [idempotencyDefect_newtonPeirceStep]
  let δ := idempotencyDefect x
  have hExpand :
      δ * δ * (4 * δ - 3) =
        ((δ * δ * δ + δ * δ * δ) + (δ * δ * δ + δ * δ * δ)) -
          (δ * δ + δ * δ + δ * δ) := by
    noncomm_ring
  rw [hExpand]
  have hTri3 :
      ‖δ * δ + δ * δ + δ * δ‖ ≤ ‖δ * δ‖ + ‖δ * δ‖ + ‖δ * δ‖ :=
    (norm_add_le (δ * δ + δ * δ) (δ * δ)).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hTri :
      ‖((δ * δ * δ + δ * δ * δ) + (δ * δ * δ + δ * δ * δ)) -
          (δ * δ + δ * δ + δ * δ)‖ ≤
        ((‖δ * δ * δ‖ + ‖δ * δ * δ‖) + (‖δ * δ * δ‖ + ‖δ * δ * δ‖)) +
          (‖δ * δ‖ + ‖δ * δ‖ + ‖δ * δ‖) :=
    (norm_sub_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))) hTri3)
  have h2 : ‖δ * δ‖ ≤ ‖δ‖ * ‖δ‖ := norm_mul_le δ δ
  have h3 : ‖δ * δ * δ‖ ≤ (‖δ‖ * ‖δ‖) * ‖δ‖ :=
    (norm_mul_le (δ * δ) δ).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg δ))
  exact hTri.trans (scalar_three_add_four_mul h3 h2)

/-- Super-exponential `2 ^ k` norm decay of `idempotencyDefect (newtonPeirceStep^[k] x)`
under the threshold `‖idempotencyDefect x‖ ≤ 1 / 4`. -/
theorem four_mul_norm_idempotencyDefect_iterate_le_two_pow
    {x : B} (hδ : ‖idempotencyDefect x‖ ≤ 1 / 4) (k : ℕ) :
    4 * ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤
      (4 * ‖idempotencyDefect x‖) ^ (2 ^ k) := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, pow_one, le_refl]
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    have hq_nn : 0 ≤ 4 * ‖idempotencyDefect x‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    have hq_le : 4 * ‖idempotencyDefect x‖ ≤ 1 := scalar_four_mul_le_one hδ
    have hpow_le : (4 * ‖idempotencyDefect x‖) ^ (2 ^ k) ≤ 1 := pow_le_one₀ hq_nn hq_le
    have hdk_le : ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ 1 / 4 :=
      scalar_div_four_le_init (ih.trans hpow_le) (by norm_num)
    have hstep1 := norm_idempotencyDefect_newtonPeirceStep_le (newtonPeirceStep^[k] x)
    have hstep2 := scalar_cubic_defect_le_four_sq hdk_le
    have hstep3 := scalar_four_mul_sq_step (hstep1.trans hstep2) ih (norm_nonneg _)
    have hpow_eq : ((4 * ‖idempotencyDefect x‖) ^ (2 ^ k)) ^ 2 =
        (4 * ‖idempotencyDefect x‖) ^ (2 ^ (k + 1)) := by
      rw [← pow_mul, ← pow_succ]
    exact hpow_eq ▸ hstep3

/-- Monotone upper bound `‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ ‖idempotencyDefect x‖`
whenever `‖idempotencyDefect x‖ ≤ 1 / 4`. -/
theorem norm_idempotencyDefect_iterate_le_init
    {x : B} (hδ : ‖idempotencyDefect x‖ ≤ 1 / 4) (k : ℕ) :
    ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ ‖idempotencyDefect x‖ := by
  have h4 := four_mul_norm_idempotencyDefect_iterate_le_two_pow hδ k
  have hq_nn : 0 ≤ 4 * ‖idempotencyDefect x‖ := mul_nonneg (by norm_num) (norm_nonneg _)
  have hq_le : 4 * ‖idempotencyDefect x‖ ≤ 1 := scalar_four_mul_le_one hδ
  have h1le : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpow : (4 * ‖idempotencyDefect x‖) ^ (2 ^ k) ≤ 4 * ‖idempotencyDefect x‖ := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq_nn hq_le h1le
  exact scalar_div_four_le_init h4 hpow

/-- Under `‖idempotencyDefect x‖ < 1 / 4`, the idempotency defect converges to `0`
in `[NormedRing B]`. -/
theorem idempotencyDefect_newtonPeirceStep_tendsto_zero
    {x : B} (hδ : ‖idempotencyDefect x‖ < 1 / 4) :
    Filter.Tendsto (fun k : ℕ => idempotencyDefect (newtonPeirceStep^[k] x))
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let q : ℝ := 4 * ‖idempotencyDefect x‖
  have hq_nn : 0 ≤ q := mul_nonneg (by norm_num) (norm_nonneg _)
  have hq_lt : q < 1 := scalar_four_mul_lt_one hδ
  have hpow_lim : Filter.Tendsto (fun k : ℕ => q ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
  have hmaj_lim : Filter.Tendsto (fun k : ℕ => (1 / 4 : ℝ) * q ^ k) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hpow_lim.const_mul (1 / 4 : ℝ)
  refine squeeze_zero (fun _ => norm_nonneg _) ?_ hmaj_lim
  intro k
  have h2pow := four_mul_norm_idempotencyDefect_iterate_le_two_pow hδ.le k
  have hkle : k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
  have hpow_le : q ^ (2 ^ k) ≤ q ^ k := pow_le_pow_of_le_one hq_nn hq_lt.le hkle
  have h4le : 4 * ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ q ^ k := h2pow.trans hpow_le
  have h4inv : (1 / 4 : ℝ) * (4 * ‖idempotencyDefect (newtonPeirceStep^[k] x)‖) ≤
      (1 / 4 : ℝ) * q ^ k := mul_le_mul_of_nonneg_left h4le (by norm_num)
  simpa [one_div, inv_mul_cancel_left₀ (by norm_num : (4 : ℝ) ≠ 0)] using h4inv

private theorem stepBound_geometric_le {x : B} (hδ : ‖idempotencyDefect x‖ < 1 / 6) (k : ℕ) :
    (1 + 2 * ‖newtonPeirceStep^[k] x‖) * ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤
      ((1 + 2 * ‖x‖) * ‖idempotencyDefect x‖) * (6 * ‖idempotencyDefect x‖) ^ k := by
  have hδ4 : ‖idempotencyDefect x‖ ≤ 1 / 4 := (scalar_one_sixth_lt_one_fourth hδ).le
  induction k with
  | zero =>
    simp only [Function.iterate_zero_apply, pow_zero, mul_one, le_refl]
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    have hdk_le : ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ ‖idempotencyDefect x‖ :=
      norm_idempotencyDefect_iterate_le_init hδ4 k
    have hdk4 : ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ≤ 1 / 4 := hdk_le.trans hδ4
    have hdnext_le :
        ‖idempotencyDefect (newtonPeirceStep (newtonPeirceStep^[k] x))‖ ≤
          4 * ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ ^ 2 :=
      (norm_idempotencyDefect_newtonPeirceStep_le _).trans
        (scalar_cubic_defect_le_four_sq hdk4)
    have hnorm_next :
        ‖newtonPeirceStep (newtonPeirceStep^[k] x)‖ ≤
          ‖newtonPeirceStep^[k] x‖ +
            (1 + 2 * ‖newtonPeirceStep^[k] x‖) *
              ‖idempotencyDefect (newtonPeirceStep^[k] x)‖ := by
      have htri := norm_add_le (newtonPeirceStep^[k] x)
        (newtonPeirceStep (newtonPeirceStep^[k] x) - newtonPeirceStep^[k] x)
      rw [add_sub_cancel] at htri
      exact htri.trans (add_le_add le_rfl (norm_newtonPeirceStep_sub_self_le _))
    have hratio := scalar_next_step_ratio hδ (norm_nonneg _) hdk_le (norm_nonneg _)
      hdnext_le (norm_nonneg _) hnorm_next
    have h6_nn : 0 ≤ 6 * ‖idempotencyDefect x‖ := scalar_nonneg_six_mul (norm_nonneg _)
    calc
      (1 + 2 * ‖newtonPeirceStep (newtonPeirceStep^[k] x)‖) *
          ‖idempotencyDefect (newtonPeirceStep (newtonPeirceStep^[k] x))‖
          ≤ (6 * ‖idempotencyDefect x‖) *
              ((1 + 2 * ‖newtonPeirceStep^[k] x‖) *
                ‖idempotencyDefect (newtonPeirceStep^[k] x)‖) := hratio
      _ ≤ (6 * ‖idempotencyDefect x‖) *
            (((1 + 2 * ‖x‖) * ‖idempotencyDefect x‖) *
              (6 * ‖idempotencyDefect x‖) ^ k) :=
          mul_le_mul_of_nonneg_left ih h6_nn
      _ = ((1 + 2 * ‖x‖) * ‖idempotencyDefect x‖) *
            (6 * ‖idempotencyDefect x‖) ^ (k + 1) := by
          rw [pow_succ']
          exact scalar_geom_assoc (1 + 2 * ‖x‖) (6 * ‖idempotencyDefect x‖)
            ‖idempotencyDefect x‖ ((6 * ‖idempotencyDefect x‖) ^ k)

/-- Under `‖idempotencyDefect x‖ < 1 / 6`, the Newton–Peirce trajectory `newtonPeirceStep^[k] x`
is Cauchy in `[NormedRing B]` (without `NormOneClass B`). -/
theorem newtonPeirceStep_iterate_cauchySeq
    {x : B} (hδ : ‖idempotencyDefect x‖ < 1 / 6) :
    CauchySeq (fun k : ℕ => newtonPeirceStep^[k] x) := by
  refine cauchySeq_of_le_geometric (6 * ‖idempotencyDefect x‖)
    ((1 + 2 * ‖x‖) * ‖idempotencyDefect x‖) (scalar_six_mul_lt_one hδ) ?_
  intro k
  simp only [dist_eq_norm, Function.iterate_succ_apply']
  rw [norm_sub_rev]
  exact (norm_newtonPeirceStep_sub_self_le _).trans (stepBound_geometric_le hδ k)

end NormedRingBounds

section CompleteBanachConvergence

/-- Polynomial invariance of commutators under one Newton–Peirce step in any `[Ring R]`. -/
theorem commute_newtonPeirceStep {R : Type*} [Ring R] {a x : R} (h : Commute a x) :
    Commute a (newtonPeirceStep x) := by
  rw [Commute, SemiconjBy] at h ⊢
  unfold newtonPeirceStep
  calc
    a * (3 * x * x - 2 * x * x * x)
        = 3 * (a * x) * x - 2 * (a * x) * x * x := by noncomm_ring
    _ = 3 * (x * a) * x - 2 * (x * a) * x * x := by rw [h]
    _ = 3 * x * (a * x) - 2 * x * (a * x) * x := by noncomm_ring
    _ = 3 * x * (x * a) - 2 * x * (x * a) * x := by rw [h]
    _ = 3 * x * x * a - 2 * x * x * (a * x) := by noncomm_ring
    _ = 3 * x * x * a - 2 * x * x * (x * a) := by rw [h]
    _ = (3 * x * x - 2 * x * x * x) * a := by noncomm_ring

/-- Every element commuting with `x` commutes with every iterate `newtonPeirceStep^[k] x`. -/
theorem commute_newtonPeirceStep_iterates {R : Type*} [Ring R] {a x : R}
    (h : Commute a x) (k : ℕ) :
    Commute a (newtonPeirceStep^[k] x) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact commute_newtonPeirceStep ih

/-- **Analytic Bucket-3 Closure (Banach-Algebra Super-Convergence)**:
In any complete normed ring `[NormedRing B] [CompleteSpace B]`, every operator `x : B` with
initial defect `‖idempotencyDefect x‖ < 1 / 6` converges along `newtonPeirceStep^[k] x` to an
exact idempotent `e : B` preserving commutativity, one-sided supports, annihilators, and
bilateral intertwiners. -/
theorem banach_newtonPeirce_limit_idempotent_and_intertwiner
    {B : Type*} [NormedRing B] [CompleteSpace B] {x : B} (hδ : ‖idempotencyDefect x‖ < 1 / 6) :
    ∃ e : B,
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x) Filter.atTop (nhds e) ∧
      e * e = e ∧
      Commute x e ∧
      (∀ a : B, Commute a x → Commute a e) ∧
      (∀ p : B, p * x = x → p * e = e) ∧
      (∀ p : B, x * p = x → e * p = e) ∧
      (∀ a : B, a * x = 0 → a * e = 0) ∧
      (∀ a : B, x * a = 0 → e * a = 0) ∧
      (∀ (y z e_z : B),
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] z) Filter.atTop (nhds e_z) →
        x * y = y * z → e * y = y * e_z) := by
  obtain ⟨e, he⟩ := cauchySeq_tendsto_of_complete (newtonPeirceStep_iterate_cauchySeq hδ)
  have hDefLim :
      Filter.Tendsto (fun k : ℕ => idempotencyDefect (newtonPeirceStep^[k] x))
        Filter.atTop (nhds (idempotencyDefect e)) :=
    (he.mul he).sub he
  have hDefZero := idempotencyDefect_newtonPeirceStep_tendsto_zero (scalar_one_sixth_lt_one_fourth hδ)
  have hIdem : e * e = e :=
    idempotencyDefect_eq_zero_iff.mp (tendsto_nhds_unique hDefLim hDefZero)
  have hComm : ∀ a : B, Commute a x → Commute a e := by
    intro a ha
    have hL : Filter.Tendsto (fun k : ℕ => a * newtonPeirceStep^[k] x)
        Filter.atTop (nhds (a * e)) := tendsto_const_nhds.mul he
    have hR : Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x * a)
        Filter.atTop (nhds (e * a)) := he.mul tendsto_const_nhds
    have hEq : (fun k : ℕ => a * newtonPeirceStep^[k] x) =
        (fun k : ℕ => newtonPeirceStep^[k] x * a) := by
      funext k
      exact (commute_newtonPeirceStep_iterates ha k).eq
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  have hCommSelf : Commute x e := hComm x (Commute.refl x)
  have hLeftSup : ∀ p : B, p * x = x → p * e = e := by
    intro p hp
    have hL : Filter.Tendsto (fun k : ℕ => p * newtonPeirceStep^[k] x)
        Filter.atTop (nhds (p * e)) := tendsto_const_nhds.mul he
    have hEq : (fun k : ℕ => p * newtonPeirceStep^[k] x) =
        (fun k : ℕ => newtonPeirceStep^[k] x) := by
      funext k
      exact newtonPeirceStep_iterates_left_support hp k
    rw [hEq] at hL
    exact tendsto_nhds_unique hL he
  have hRightSup : ∀ p : B, x * p = x → e * p = e := by
    intro p hp
    have hR : Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x * p)
        Filter.atTop (nhds (e * p)) := he.mul tendsto_const_nhds
    have hEq : (fun k : ℕ => newtonPeirceStep^[k] x * p) =
        (fun k : ℕ => newtonPeirceStep^[k] x) := by
      funext k
      exact newtonPeirceStep_iterates_right_support hp k
    rw [hEq] at hR
    exact tendsto_nhds_unique hR he
  have hLeftAnn : ∀ a : B, a * x = 0 → a * e = 0 := by
    intro a ha
    have hL : Filter.Tendsto (fun k : ℕ => a * newtonPeirceStep^[k] x)
        Filter.atTop (nhds (a * e)) := tendsto_const_nhds.mul he
    have hEq : (fun k : ℕ => a * newtonPeirceStep^[k] x) = fun _ => 0 := by
      funext k
      exact newtonPeirceStep_iterates_left_annihilated ha k
    rw [hEq] at hL
    exact tendsto_nhds_unique hL tendsto_const_nhds
  have hRightAnn : ∀ a : B, x * a = 0 → e * a = 0 := by
    intro a ha
    have hR : Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x * a)
        Filter.atTop (nhds (e * a)) := he.mul tendsto_const_nhds
    have hEq : (fun k : ℕ => newtonPeirceStep^[k] x * a) = fun _ => 0 := by
      funext k
      exact newtonPeirceStep_iterates_right_annihilated ha k
    rw [hEq] at hR
    exact tendsto_nhds_unique hR tendsto_const_nhds
  have hInter : ∀ (y z e_z : B),
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] z) Filter.atTop (nhds e_z) →
      x * y = y * z → e * y = y * e_z := by
    intro y z e_z he_z hxy
    have hL : Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x * y)
        Filter.atTop (nhds (e * y)) := he.mul tendsto_const_nhds
    have hR : Filter.Tendsto (fun k : ℕ => y * newtonPeirceStep^[k] z)
        Filter.atTop (nhds (y * e_z)) := tendsto_const_nhds.mul he_z
    have hEq : (fun k : ℕ => newtonPeirceStep^[k] x * y) =
        (fun k : ℕ => y * newtonPeirceStep^[k] z) := by
      funext k
      exact newtonPeirceStep_iterates_intertwines hxy k
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  exact ⟨e, he, hIdem, hCommSelf, hComm, hLeftSup, hRightSup, hLeftAnn, hRightAnn, hInter⟩

end CompleteBanachConvergence

section ConcreteContinuousOperatorWitness

/-- Continuous orthogonal projection onto the first coordinate of `ℝ²`. -/
noncomputable def clmCut : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![v 0, 0]
      map_add' := fun u v => by ext i; fin_cases i <;> simp
      map_smul' := fun r v => by ext i; fin_cases i <;> simp }

/-- Noncommuting oblique near-idempotent operator on `ℝ²` (`v ↦ ![v 0 + (1 / 10) v 1, (1 / 10) v 1]`)
whose idempotency defect is non-nilpotent at every power `n + 1`, yet strictly inside the Banach
super-convergence disk (`‖δ‖ ≤ 9 / 100 < 1 / 6`). -/
noncomputable def clmPerturbedSeed : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ![v 0 + (1 / 10 : ℝ) * v 1, (1 / 10 : ℝ) * v 1]
      map_add' := fun u v => by
        ext i
        fin_cases i <;> simp [mul_add, add_add_add_comm]
      map_smul' := fun r v => by
        ext i
        fin_cases i <;> simp [mul_add, mul_left_comm] }

private theorem idempotencyDefect_clmPerturbedSeed_apply (v : Fin 2 → ℝ) :
    idempotencyDefect clmPerturbedSeed v = ![(1 / 100 : ℝ) * v 1, -(9 / 100 : ℝ) * v 1] := by
  have hSeed : ∀ w : Fin 2 → ℝ,
      clmPerturbedSeed w = ![w 0 + (1 / 10 : ℝ) * w 1, (1 / 10 : ℝ) * w 1] := fun _ => rfl
  unfold idempotencyDefect
  rw [sub_apply]
  change clmPerturbedSeed (clmPerturbedSeed v) - clmPerturbedSeed v =
    ![(1 / 100 : ℝ) * v 1, -(9 / 100 : ℝ) * v 1]
  rw [hSeed, hSeed]
  ext i
  fin_cases i
  · change v 0 + (1 / 10 : ℝ) * v 1 + (1 / 10 : ℝ) * ((1 / 10 : ℝ) * v 1) -
        (v 0 + (1 / 10 : ℝ) * v 1) = (1 / 100 : ℝ) * v 1
    exact scalar_seed_defect_0 (v 0) (v 1)
  · change (1 / 10 : ℝ) * ((1 / 10 : ℝ) * v 1) - (1 / 10 : ℝ) * v 1 = -(9 / 100 : ℝ) * v 1
    exact scalar_seed_defect_1 (v 1)

private theorem idempotencyDefect_clmPerturbedSeed_pow_coord1 (n : ℕ) (v : Fin 2 → ℝ) :
    ((idempotencyDefect clmPerturbedSeed) ^ (n + 1)) v 1 =
      (-(9 / 100 : ℝ)) ^ (n + 1) * v 1 := by
  induction n with
  | zero =>
    rw [pow_one, idempotencyDefect_clmPerturbedSeed_apply]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [pow_one]
  | succ n ih =>
    rw [pow_succ']
    change (idempotencyDefect clmPerturbedSeed)
        (((idempotencyDefect clmPerturbedSeed) ^ (n + 1)) v) 1 =
      (-(9 / 100 : ℝ)) ^ (n + 1 + 1) * v 1
    rw [idempotencyDefect_clmPerturbedSeed_apply]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [ih, ← mul_assoc, ← pow_succ']

/-- **Banach Witness Beyond Algebraic Nilpotency**:
`clmPerturbedSeed` and `clmCut` fail to commute in `(Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)`,
`(idempotencyDefect clmPerturbedSeed) ^ (n + 1) ≠ 0` for every `n : ℕ` (so the algebraic nilpotency
theorem never applies at any finite stage), yet `‖idempotencyDefect clmPerturbedSeed‖ ≤ 9 / 100 < 1 / 6`
and the Newton–Peirce iterates converge in operator norm to a commuting idempotent `e`. -/
theorem non_nilpotent_oblique_clm_banach_convergence_witness :
    clmCut * clmPerturbedSeed ≠ clmPerturbedSeed * clmCut ∧
    (∀ n : ℕ, (idempotencyDefect clmPerturbedSeed) ^ (n + 1) ≠ 0) ∧
    ‖idempotencyDefect clmPerturbedSeed‖ ≤ (9 / 100 : ℝ) ∧
    ∃ e : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
      Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] clmPerturbedSeed) Filter.atTop (nhds e) ∧
      e * e = e ∧
      Commute clmPerturbedSeed e := by
  have hCut : ∀ w : Fin 2 → ℝ, clmCut w = ![w 0, 0] := fun _ => rfl
  have hSeed : ∀ w : Fin 2 → ℝ,
      clmPerturbedSeed w = ![w 0 + (1 / 10 : ℝ) * w 1, (1 / 10 : ℝ) * w 1] := fun _ => rfl
  have hNoncomm : clmCut * clmPerturbedSeed ≠ clmPerturbedSeed * clmCut := by
    intro hEq
    have hApp := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T ![0, 1] 0) hEq
    change clmCut (clmPerturbedSeed ![0, 1]) 0 = clmPerturbedSeed (clmCut ![0, 1]) 0 at hApp
    simp only [hCut, hSeed, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero] at hApp
    norm_num at hApp
  have hNonNilp : ∀ n : ℕ, (idempotencyDefect clmPerturbedSeed) ^ (n + 1) ≠ 0 := by
    intro n hZero
    have hCoord := congrArg (fun T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) => T ![0, 1] 1) hZero
    rw [idempotencyDefect_clmPerturbedSeed_pow_coord1] at hCoord
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, mul_one, zero_apply, Pi.zero_apply] at hCoord
    exact pow_ne_zero (n + 1) (by norm_num : (-(9 / 100 : ℝ)) ≠ 0) hCoord
  have hNorm : ‖idempotencyDefect clmPerturbedSeed‖ ≤ (9 / 100 : ℝ) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
    rw [idempotencyDefect_clmPerturbedSeed_apply]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg v))).2 fun i => ?_
    have hv1 : |v 1| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
    fin_cases i
    · change ‖(1 / 100 : ℝ) * v 1‖ ≤ (9 / 100 : ℝ) * ‖v‖
      rw [Real.norm_eq_abs]
      exact scalar_coord0_nine_hundredths hv1
    · change ‖-(9 / 100 : ℝ) * v 1‖ ≤ (9 / 100 : ℝ) * ‖v‖
      rw [Real.norm_eq_abs]
      exact scalar_coord1_nine_hundredths hv1
  have hLt : ‖idempotencyDefect clmPerturbedSeed‖ < 1 / 6 :=
    lt_of_le_of_lt hNorm scalar_norm_nine_hundredths
  obtain ⟨e, he, hIdem, hComm, _⟩ := banach_newtonPeirce_limit_idempotent_and_intertwiner hLt
  exact ⟨hNoncomm, hNonNilp, hNorm, e, he, hIdem, hComm⟩

/-- Registered QMS archetype certifying analytic Banach-algebra Newton–Peirce convergence
together with the non-nilpotent continuous operator witness. -/
noncomputable def banachNewtonPeirceSuperConvergenceArchetype : TypedArchetype Unit .proved where
  name := `InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence.banachNewtonPeirceSuperConvergenceArchetype
  phase := Phase.kernelCertifiedPromotion.toNat
  claim := fun _ =>
    (∀ (B : Type) [NormedRing B] [CompleteSpace B] (x : B),
      ‖idempotencyDefect x‖ < 1 / 6 →
      ∃ e : B,
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] x) Filter.atTop (nhds e) ∧
        e * e = e ∧
        Commute x e) ∧
    (clmCut * clmPerturbedSeed ≠ clmPerturbedSeed * clmCut ∧
      (∀ n : ℕ, (idempotencyDefect clmPerturbedSeed) ^ (n + 1) ≠ 0) ∧
      ∃ e : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
        Filter.Tendsto (fun k : ℕ => newtonPeirceStep^[k] clmPerturbedSeed) Filter.atTop (nhds e) ∧
        e * e = e ∧
        Commute clmPerturbedSeed e)
  evidence := fun _ => by
    refine ⟨?_, ?_⟩
    · intro B _ _ x hx
      obtain ⟨e, he, hIdem, hComm, _⟩ := banach_newtonPeirce_limit_idempotent_and_intertwiner hx
      exact ⟨e, he, hIdem, hComm⟩
    · have hW := non_nilpotent_oblique_clm_banach_convergence_witness
      exact ⟨hW.1, hW.2.1, hW.2.2.2⟩

#register_archetype banachNewtonPeirceSuperConvergenceArchetype
#audit_archetype banachNewtonPeirceSuperConvergenceArchetype

end ConcreteContinuousOperatorWitness

end InfoGeometry.OperatorAlgebra.BanachNewtonPeirceConvergence
