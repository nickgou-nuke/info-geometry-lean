/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
import InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
import InfoGeometry.Canonical.DualConnectionsFiniteExpFamily
import InfoGeometry.Modular.AmariChentsovDualConnections
import InfoGeometry.Statistical.DualFlatCurvature
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Pi

/-!
# Eguchi Divergence Metrics, Exponential-Family Dual Manifolds, and Affine Curvature

This module completes three central pillars of classical information geometry without assumed
metric-derivative or curvature-decomposition packets:

1. **Eguchi's Divergence-to-Metric Equations (0th, 1st, and 2nd Order)**:
   - Proves that along any twice-differentiable simplex-interior curve `Q : ℝ → ProbInterior α`
     passing through `Q 0 = P`, both Kullback–Leibler (`ArakiDonald.relativeEntropy`, `α = ±1`)
     and Amari `α`-divergences (`amariAlphaDivergence αParam`, `αParam ^ 2 ≠ 1`) vanish to 0th
     and 1st order at `t = 0` and recover `fisherMetric P (dq 0) (dq 0)` identically at 2nd
     order in both arguments.
2. **Third Cumulant, Metric Derivative, and Constructive `DualConnectionManifold (Fin d → ℝ)`**:
   - Defines `thirdCumulant F θ u v w` for `Information.FiniteExpFamily d`, proves total
     symmetry, trilinearity, and coincidence with `DualConnections.chentsovTensor` on
     `centeredScore`.
   - Proves `HasDerivAt (fun t => fisherBilinearForm F (θ + t • u) v w) (thirdCumulant F θ u v w) 0`.
   - Inverts the strictly positive-definite Fisher linear operator `fisherLinearOp F θ` under
     linear independence of statistics (`fisherLinearEquiv`) and constructs the non-trivial
     exponential-family `AmariChentsovDualConnections.DualConnectionManifold (Fin d → ℝ)` with
     `nabla_e = 0`, discharging `amari_duality` from calculus and equating `amariCubicForm` to
     `thirdCumulant`.
3. **Genuine Affine Connection Curvature & `Statistical.CurvatureDecompositionPacket` Instance**:
   - Defines `connCurvature` and `covariantExteriorDeriv` for any bilinear bracket and linear
     connections `∇, ∇* : T →ₗ[ℝ] Module.End ℝ T`, proves the curvature sum and difference laws
     unconditionally, and constructs `affineCurvatureDecompositionPacket` and
     `dualManifoldCurvaturePacket`.
-/

noncomputable section

namespace InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature

open Finset
open scoped BigOperators
open InfoGeometry.Epistemology.ChentsovMetricInvariance
open InfoGeometry.InformationGeometry.ParametricCramerRaoAndCumulants
open InfoGeometry.InformationGeometry.CsiszarAlphaDivergenceAndChentsovMonotonicity
open InfoGeometry.InformationGeometry.ArakiDonald
open InfoGeometry.Canonical
open InfoGeometry.Canonical.DualConnections
open InfoGeometry.Modular.AmariChentsovDualConnections
open InfoGeometry.Statistical
open InfoGeometry.Analytic

/-! ### 1. Eguchi Divergence-to-Metric Equations -/

section EguchiMetrics

variable {α : Type*} [Fintype α]

/-- Pointwise normalization derivative: along any differentiable simplex curve `Q : ℝ → ProbInterior α`,
the tangent velocities sum to zero at every parameter `t`. -/
theorem sum_dq_eq_zero (Q : ℝ → ProbInterior α) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) (t : ℝ) :
    ∑ a, dq t a = 0 :=
  deriv_prob_sum_eq_zero (fun s a => (Q s).p a) (dq t) t (fun s => (Q s).sum_one) (hd1 t)

/-- Second-order normalization derivative: the acceleration profile at `t = 0` sums to zero. -/
theorem sum_d2q_eq_zero (Q : ℝ → ProbInterior α) (dq : ℝ → α → ℝ) (d2q : α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t)
    (hd2 : ∀ a, HasDerivAt (fun t => dq t a) (d2q a) 0) :
    ∑ a, d2q a = 0 := by
  have hsum : HasDerivAt (fun t => ∑ a, dq t a) (∑ a, d2q a) 0 :=
    HasDerivAt.fun_sum (fun a _ => hd2 a)
  have hfn : (fun t => ∑ a, dq t a) = fun _ => (0 : ℝ) := funext (sum_dq_eq_zero Q dq hd1)
  have hzero : HasDerivAt (fun t => ∑ a, dq t a) 0 0 := by
    simpa [hfn] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  exact hsum.unique hzero

/-- 0th-order KL Eguchi identity: `D_KL(P ∥ Q 0) = 0` when `Q 0 = P`. -/
theorem eguchi_kl_right_zero [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) :
    ArakiDonald.relativeEntropy P.p (Q 0).p = 0 := by
  rw [hQ0]
  unfold ArakiDonald.relativeEntropy
  refine Finset.sum_eq_zero ?_
  intro a _
  rw [div_self (ne_of_gt (P.pos a)), Real.log_one, mul_zero]

/-- Exact 1st-order derivative of `t ↦ D_KL(P ∥ Q t)` at every parameter `t`. -/
theorem eguchi_kl_right_hasDerivAt [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) (t : ℝ) :
    HasDerivAt (fun s => ArakiDonald.relativeEntropy P.p (Q s).p)
      (∑ a, -(P.p a * (dq t a / (Q t).p a))) t := by
  unfold ArakiDonald.relativeEntropy
  refine HasDerivAt.fun_sum ?_
  intro a _
  have hQt_ne : (Q t).p a ≠ 0 := ne_of_gt ((Q t).pos a)
  have hratio : HasDerivAt (fun s => P.p a / (Q s).p a)
      (-(P.p a * dq t a) / (Q t).p a ^ 2) t := by
    simpa [zero_mul, zero_sub] using (hasDerivAt_const t (P.p a)).fun_div (hd1 t a) hQt_ne
  have hlog := hratio.log (div_ne_zero (ne_of_gt (P.pos a)) hQt_ne)
  have hterm := (hasDerivAt_const t (P.p a)).fun_mul hlog
  have hval :
      0 * Real.log (P.p a / (Q t).p a) +
          P.p a * (-(P.p a * dq t a) / (Q t).p a ^ 2 / (P.p a / (Q t).p a)) =
        -(P.p a * (dq t a / (Q t).p a)) := by
    have hP_ne : P.p a ≠ 0 := ne_of_gt (P.pos a)
    field_simp [hP_ne, hQt_ne]
    ring
  rwa [hval] at hterm

/-- 1st-order KL Eguchi identity: `d/dt|_{t=0} D_KL(P ∥ Q t) = 0`. -/
theorem eguchi_kl_right_firstDeriv [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) :
    HasDerivAt (fun s => ArakiDonald.relativeEntropy P.p (Q s).p) 0 0 := by
  have hd := eguchi_kl_right_hasDerivAt P Q dq hd1 0
  have hval : ∑ a, -(P.p a * (dq 0 a / (Q 0).p a)) = 0 := by
    calc
      ∑ a, -(P.p a * (dq 0 a / (Q 0).p a))
          = ∑ a, -dq 0 a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [hQ0, mul_div_cancel₀ _ (ne_of_gt (P.pos a))]
      _ = -∑ a, dq 0 a := by rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [sum_dq_eq_zero Q dq hd1 0, neg_zero]
  rwa [hval] at hd

/-- **2nd-Order KL Eguchi Equation (Target Argument)**:
`d²/dt²|_{t=0} D_KL(P ∥ Q t) = fisherMetric P (dq 0) (dq 0)`. -/
theorem eguchi_kl_right_secondDeriv [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) (dq : ℝ → α → ℝ) (d2q : α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t)
    (hd2 : ∀ a, HasDerivAt (fun t => dq t a) (d2q a) 0) :
    deriv (deriv (fun s => ArakiDonald.relativeEntropy P.p (Q s).p)) 0 =
      fisherMetric P (dq 0) (dq 0) := by
  have hderiv_fn :
      deriv (fun s => ArakiDonald.relativeEntropy P.p (Q s).p) =
        fun t => ∑ a, -(P.p a * (dq t a / (Q t).p a)) := by
    funext t
    exact (eguchi_kl_right_hasDerivAt P Q dq hd1 t).deriv
  have hd2_sum :
      HasDerivAt (fun t => ∑ a, -(P.p a * (dq t a / (Q t).p a)))
        (fisherMetric P (dq 0) (dq 0)) 0 := by
    have hraw :
        HasDerivAt (fun t => ∑ a, -(P.p a * (dq t a / (Q t).p a)))
          (∑ a, -(P.p a * ((d2q a * (Q 0).p a - dq 0 a * dq 0 a) / (Q 0).p a ^ 2))) 0 := by
      refine HasDerivAt.fun_sum ?_
      intro a _
      exact ((hd2 a).div (hd1 0 a) (ne_of_gt ((Q 0).pos a))).const_mul (P.p a) |>.neg
    have hval :
        ∑ a, -(P.p a * ((d2q a * (Q 0).p a - dq 0 a * dq 0 a) / (Q 0).p a ^ 2)) =
          fisherMetric P (dq 0) (dq 0) := by
      have hterm :
          ∑ a, -(P.p a * ((d2q a * (Q 0).p a - dq 0 a * dq 0 a) / (Q 0).p a ^ 2)) =
            ∑ a, (dq 0 a * dq 0 a / P.p a - d2q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [hQ0]
        have hPne : P.p a ≠ 0 := ne_of_gt (P.pos a)
        field_simp [hPne]
        ring
      rw [hterm, Finset.sum_sub_distrib, sum_d2q_eq_zero Q dq d2q hd1 hd2, sub_zero]
      rfl
    rwa [hval] at hraw
  rw [hderiv_fn]
  exact hd2_sum.deriv

/-- Exact 1st-order derivative of `t ↦ D_KL(Q t ∥ P)` at every parameter `t`. -/
theorem eguchi_kl_left_hasDerivAt [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) (t : ℝ) :
    HasDerivAt (fun s => ArakiDonald.relativeEntropy (Q s).p P.p)
      (∑ a, (dq t a * Real.log ((Q t).p a / P.p a) + dq t a)) t := by
  unfold ArakiDonald.relativeEntropy
  refine HasDerivAt.fun_sum ?_
  intro a _
  have hPne : P.p a ≠ 0 := ne_of_gt (P.pos a)
  have hQt_ne : (Q t).p a ≠ 0 := ne_of_gt ((Q t).pos a)
  have hlog : HasDerivAt (fun s => Real.log ((Q s).p a / P.p a)) (dq t a / (Q t).p a) t := by
    have hquot : HasDerivAt (fun s => (Q s).p a / P.p a) (dq t a / P.p a) t :=
      (hd1 t a).div_const (P.p a)
    have h := hquot.log (div_ne_zero hQt_ne hPne)
    have hsimp : dq t a / P.p a / ((Q t).p a / P.p a) = dq t a / (Q t).p a := by
      field_simp [hPne, hQt_ne]
    rwa [hsimp] at h
  have hmul := (hd1 t a).mul hlog
  have hval : dq t a * Real.log ((Q t).p a / P.p a) + (Q t).p a * (dq t a / (Q t).p a) =
      dq t a * Real.log ((Q t).p a / P.p a) + dq t a := by
    rw [mul_div_cancel₀ _ hQt_ne]
  rwa [hval] at hmul

/-- 1st-order KL Eguchi identity (left argument): `d/dt|_{t=0} D_KL(Q t ∥ P) = 0`. -/
theorem eguchi_kl_left_firstDeriv [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) :
    HasDerivAt (fun s => ArakiDonald.relativeEntropy (Q s).p P.p) 0 0 := by
  have hd := eguchi_kl_left_hasDerivAt P Q dq hd1 0
  have hval : ∑ a, (dq 0 a * Real.log ((Q 0).p a / P.p a) + dq 0 a) = 0 := by
    calc
      ∑ a, (dq 0 a * Real.log ((Q 0).p a / P.p a) + dq 0 a)
          = ∑ a, dq 0 a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [hQ0, div_self (ne_of_gt (P.pos a)), Real.log_one, mul_zero, zero_add]
      _ = 0 := sum_dq_eq_zero Q dq hd1 0
  rwa [hval] at hd

/-- **2nd-Order KL Eguchi Equation (Source Argument)**:
`d²/dt²|_{t=0} D_KL(Q t ∥ P) = fisherMetric P (dq 0) (dq 0)`. -/
theorem eguchi_kl_left_secondDeriv [DecidableEq α] (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) (dq : ℝ → α → ℝ) (d2q : α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t)
    (hd2 : ∀ a, HasDerivAt (fun t => dq t a) (d2q a) 0) :
    deriv (deriv (fun s => ArakiDonald.relativeEntropy (Q s).p P.p)) 0 =
      fisherMetric P (dq 0) (dq 0) := by
  have hderiv_fn :
      deriv (fun s => ArakiDonald.relativeEntropy (Q s).p P.p) =
        fun t => ∑ a, (dq t a * Real.log ((Q t).p a / P.p a) + dq t a) := by
    funext t
    exact (eguchi_kl_left_hasDerivAt P Q dq hd1 t).deriv
  have hd2_sum :
      HasDerivAt (fun t => ∑ a, (dq t a * Real.log ((Q t).p a / P.p a) + dq t a))
        (fisherMetric P (dq 0) (dq 0)) 0 := by
    have hraw :
        HasDerivAt (fun t => ∑ a, (dq t a * Real.log ((Q t).p a / P.p a) + dq t a))
          (∑ a, ((d2q a * Real.log ((Q 0).p a / P.p a) +
              dq 0 a * (dq 0 a / (Q 0).p a)) + d2q a)) 0 := by
      refine HasDerivAt.fun_sum ?_
      intro a _
      have hPne : P.p a ≠ 0 := ne_of_gt (P.pos a)
      have hQ0_ne : (Q 0).p a ≠ 0 := ne_of_gt ((Q 0).pos a)
      have hlog : HasDerivAt (fun s => Real.log ((Q s).p a / P.p a)) (dq 0 a / (Q 0).p a) 0 := by
        have hquot := (hd1 0 a).div_const (P.p a)
        have h := hquot.log (div_ne_zero hQ0_ne hPne)
        have hsimp : dq 0 a / P.p a / ((Q 0).p a / P.p a) = dq 0 a / (Q 0).p a := by
          field_simp [hPne, hQ0_ne]
        rwa [hsimp] at h
      exact ((hd2 a).mul hlog).add (hd2 a)
    have hval :
        ∑ a, ((d2q a * Real.log ((Q 0).p a / P.p a) + dq 0 a * (dq 0 a / (Q 0).p a)) + d2q a) =
          fisherMetric P (dq 0) (dq 0) := by
      have hterm :
          ∑ a, ((d2q a * Real.log ((Q 0).p a / P.p a) + dq 0 a * (dq 0 a / (Q 0).p a)) + d2q a) =
            ∑ a, (dq 0 a * dq 0 a / P.p a + d2q a) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [hQ0, div_self (ne_of_gt (P.pos a)), Real.log_one, mul_zero, zero_add]
        ring
      rw [hterm, Finset.sum_add_distrib, sum_d2q_eq_zero Q dq d2q hd1 hd2, add_zero]
      rfl
    rwa [hval] at hraw
  rw [hderiv_fn]
  exact hd2_sum.deriv

/-- 0th-order Amari `α`-divergence Eguchi identity: `D^{(α)}(P ∥ Q 0) = 0`. -/
theorem eguchi_amariAlpha_right_zero (αParam : ℝ) (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) :
    amariAlphaDivergence αParam P.p (Q 0).p = 0 := by
  rw [hQ0]
  unfold amariAlphaDivergence
  have hsum : ∑ a, (P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ ((1 - αParam) / 2) = 1 := by
    calc
      ∑ a, (P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ ((1 - αParam) / 2)
          = ∑ a, P.p a := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [← Real.rpow_add (P.pos a)]
              have hexp : (1 + αParam) / 2 + (1 - αParam) / 2 = 1 := by ring
              rw [hexp, Real.rpow_one]
      _ = 1 := P.sum_one
  rw [hsum, sub_self, mul_zero]

/-- Exact 1st-order derivative of `t ↦ D^{(α)}(P ∥ Q t)` at every parameter `t`. -/
theorem eguchi_amariAlpha_right_hasDerivAt (αParam : ℝ) (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) (t : ℝ) :
    HasDerivAt (fun s => amariAlphaDivergence αParam P.p (Q s).p)
      ((4 / (1 - αParam ^ 2)) *
        (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
          (dq t a * ((1 - αParam) / 2 * (Q t).p a ^ ((1 - αParam) / 2 - 1))))) t := by
  unfold amariAlphaDivergence
  apply HasDerivAt.const_mul
  apply HasDerivAt.const_sub
  refine HasDerivAt.fun_sum ?_
  intro a _
  have hQt_ne : (Q t).p a ≠ 0 := ne_of_gt ((Q t).pos a)
  have hrpow := (hd1 t a).rpow_const (Or.inl hQt_ne) (p := (1 - αParam) / 2)
  have hmul := hrpow.const_mul ((P.p a) ^ ((1 + αParam) / 2))
  have hsim :
      (P.p a) ^ ((1 + αParam) / 2) *
          (dq t a * ((1 - αParam) / 2) * (Q t).p a ^ ((1 - αParam) / 2 - 1)) =
        (P.p a) ^ ((1 + αParam) / 2) *
          (dq t a * ((1 - αParam) / 2 * (Q t).p a ^ ((1 - αParam) / 2 - 1))) := by ring
  rwa [hsim] at hmul

/-- 1st-order Amari `α`-divergence Eguchi identity: `d/dt|_{t=0} D^{(α)}(P ∥ Q t) = 0`. -/
theorem eguchi_amariAlpha_right_firstDeriv (αParam : ℝ) (P : ProbInterior α)
    (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P) (dq : ℝ → α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t) :
    HasDerivAt (fun s => amariAlphaDivergence αParam P.p (Q s).p) 0 0 := by
  have hd := eguchi_amariAlpha_right_hasDerivAt αParam P Q dq hd1 0
  have hval :
      (4 / (1 - αParam ^ 2)) *
        (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
          (dq 0 a * ((1 - αParam) / 2 * (Q 0).p a ^ ((1 - αParam) / 2 - 1)))) = 0 := by
    have hsum :
        ∑ a, (P.p a) ^ ((1 + αParam) / 2) *
            (dq 0 a * ((1 - αParam) / 2 * (Q 0).p a ^ ((1 - αParam) / 2 - 1))) = 0 := by
      calc
        ∑ a, (P.p a) ^ ((1 + αParam) / 2) *
              (dq 0 a * ((1 - αParam) / 2 * (Q 0).p a ^ ((1 - αParam) / 2 - 1)))
            = ∑ a, ((1 - αParam) / 2) * dq 0 a := by
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [hQ0]
                have hexp : (1 + αParam) / 2 + ((1 - αParam) / 2 - 1) = 0 := by ring
                calc
                  (P.p a) ^ ((1 + αParam) / 2) *
                      (dq 0 a * ((1 - αParam) / 2 * (P.p a) ^ ((1 - αParam) / 2 - 1)))
                      = ((1 - αParam) / 2 * dq 0 a) *
                          ((P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ ((1 - αParam) / 2 - 1)) := by
                            ring
                  _ = ((1 - αParam) / 2 * dq 0 a) *
                        ((P.p a) ^ ((1 + αParam) / 2 + ((1 - αParam) / 2 - 1))) := by
                          rw [← Real.rpow_add (P.pos a)]
                  _ = ((1 - αParam) / 2) * dq 0 a := by
                        rw [hexp, Real.rpow_zero, mul_one]
        _ = ((1 - αParam) / 2) * ∑ a, dq 0 a := by rw [← Finset.mul_sum]
        _ = 0 := by rw [sum_dq_eq_zero Q dq hd1 0, mul_zero]
    rw [hsum, neg_zero, mul_zero]
  rwa [hval] at hd

/-- **2nd-Order Amari `α`-Divergence Eguchi Equation (Target Argument)**:
for every `α ≠ ±1` (`αParam ^ 2 ≠ 1`), differentiating `D^{(α)}(P ∥ Q t)` twice at `t = 0`
recovers `fisherMetric P (dq 0) (dq 0)`. -/
theorem eguchi_amariAlpha_right_secondDeriv (αParam : ℝ) (hα : αParam ^ 2 ≠ 1)
    (P : ProbInterior α) (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P)
    (dq : ℝ → α → ℝ) (d2q : α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t)
    (hd2 : ∀ a, HasDerivAt (fun t => dq t a) (d2q a) 0) :
    deriv (deriv (fun s => amariAlphaDivergence αParam P.p (Q s).p)) 0 =
      fisherMetric P (dq 0) (dq 0) := by
  let sExp : ℝ := (1 - αParam) / 2
  have hderiv_fn :
      deriv (fun s => amariAlphaDivergence αParam P.p (Q s).p) =
        fun t => (4 / (1 - αParam ^ 2)) *
          (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
            (dq t a * (sExp * (Q t).p a ^ (sExp - 1)))) := by
    funext t
    exact (eguchi_amariAlpha_right_hasDerivAt αParam P Q dq hd1 t).deriv
  have hd2_sum :
      HasDerivAt
        (fun t => (4 / (1 - αParam ^ 2)) *
          (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
            (dq t a * (sExp * (Q t).p a ^ (sExp - 1)))))
        (fisherMetric P (dq 0) (dq 0)) 0 := by
    have hraw :
        HasDerivAt
          (fun t => (4 / (1 - αParam ^ 2)) *
            (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
              (dq t a * (sExp * (Q t).p a ^ (sExp - 1)))))
          ((4 / (1 - αParam ^ 2)) *
            (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
              (d2q a * (sExp * (Q 0).p a ^ (sExp - 1)) +
                dq 0 a * (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a))))) 0 := by
      apply HasDerivAt.const_mul
      apply HasDerivAt.neg
      refine HasDerivAt.fun_sum ?_
      intro a _
      have hQ0_ne : (Q 0).p a ≠ 0 := ne_of_gt ((Q 0).pos a)
      have hrpow0 := ((hd1 0 a).rpow_const (Or.inl hQ0_ne) (p := sExp - 1)).const_mul sExp
      have hrpow :
          HasDerivAt (fun t => sExp * (Q t).p a ^ (sExp - 1))
            (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a)) 0 := by
        have heq :
            sExp * (dq 0 a * (sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1)) =
              sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a) := by ring
        rwa [heq] at hrpow0
      exact ((hd2 a).mul hrpow).const_mul ((P.p a) ^ ((1 + αParam) / 2))
    have hval :
        (4 / (1 - αParam ^ 2)) *
          (-∑ a, (P.p a) ^ ((1 + αParam) / 2) *
            (d2q a * (sExp * (Q 0).p a ^ (sExp - 1)) +
              dq 0 a * (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a)))) =
          fisherMetric P (dq 0) (dq 0) := by
      have hterm (a : α) :
          (P.p a) ^ ((1 + αParam) / 2) *
              (d2q a * (sExp * (Q 0).p a ^ (sExp - 1)) +
                dq 0 a * (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a))) =
            sExp * d2q a + (sExp * (sExp - 1)) * (dq 0 a * dq 0 a / P.p a) := by
        rw [hQ0]
        have h1 : (P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ (sExp - 1) = 1 := by
          rw [← Real.rpow_add (P.pos a)]
          have hexp : (1 + αParam) / 2 + (sExp - 1) = 0 := by dsimp [sExp]; ring
          rw [hexp, Real.rpow_zero]
        have h2 : (P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ (sExp - 1 - 1) = (P.p a)⁻¹ := by
          rw [← Real.rpow_add (P.pos a)]
          have hexp : (1 + αParam) / 2 + (sExp - 1 - 1) = (-1 : ℝ) := by dsimp [sExp]; ring
          rw [hexp, Real.rpow_neg_one]
        calc
          (P.p a) ^ ((1 + αParam) / 2) *
              (d2q a * (sExp * (P.p a) ^ (sExp - 1)) +
                dq 0 a * (sExp * ((sExp - 1) * (P.p a) ^ (sExp - 1 - 1) * dq 0 a)))
              = (sExp * d2q a) * ((P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ (sExp - 1)) +
                  (sExp * (sExp - 1) * (dq 0 a * dq 0 a)) *
                    ((P.p a) ^ ((1 + αParam) / 2) * (P.p a) ^ (sExp - 1 - 1)) := by ring
          _ = sExp * d2q a * 1 + (sExp * (sExp - 1) * (dq 0 a * dq 0 a)) * (P.p a)⁻¹ := by
                rw [h1, h2]
          _ = sExp * d2q a + (sExp * (sExp - 1)) * (dq 0 a * dq 0 a / P.p a) := by
                rw [div_eq_mul_inv]; ring
      have hsum_id :
          ∑ a, (P.p a) ^ ((1 + αParam) / 2) *
              (d2q a * (sExp * (Q 0).p a ^ (sExp - 1)) +
                dq 0 a * (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a))) =
            sExp * (∑ a, d2q a) + (sExp * (sExp - 1)) * fisherMetric P (dq 0) (dq 0) := by
        calc
          ∑ a, (P.p a) ^ ((1 + αParam) / 2) *
                (d2q a * (sExp * (Q 0).p a ^ (sExp - 1)) +
                  dq 0 a * (sExp * ((sExp - 1) * (Q 0).p a ^ (sExp - 1 - 1) * dq 0 a)))
              = ∑ a, (sExp * d2q a + (sExp * (sExp - 1)) * (dq 0 a * dq 0 a / P.p a)) := by
                  refine Finset.sum_congr rfl (fun a _ => hterm a)
          _ = sExp * (∑ a, d2q a) +
                (sExp * (sExp - 1)) * ∑ a, (dq 0 a * dq 0 a / P.p a) := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = sExp * (∑ a, d2q a) + (sExp * (sExp - 1)) * fisherMetric P (dq 0) (dq 0) := rfl
      rw [hsum_id, sum_d2q_eq_zero Q dq d2q hd1 hd2, mul_zero, zero_add]
      have hden : 1 - αParam ^ 2 ≠ 0 := sub_ne_zero.mpr hα.symm
      have hsExp : -(sExp * (sExp - 1)) = (1 - αParam ^ 2) / 4 := by
        dsimp [sExp]
        ring
      calc
        (4 / (1 - αParam ^ 2)) * -((sExp * (sExp - 1)) * fisherMetric P (dq 0) (dq 0))
            = (4 / (1 - αParam ^ 2)) * (-(sExp * (sExp - 1))) * fisherMetric P (dq 0) (dq 0) := by
                ring
        _ = (4 / (1 - αParam ^ 2)) * ((1 - αParam ^ 2) / 4) * fisherMetric P (dq 0) (dq 0) := by
              rw [hsExp]
        _ = fisherMetric P (dq 0) (dq 0) := by
              field_simp [hden]
    rwa [hval] at hraw
  rw [hderiv_fn]
  exact hd2_sum.deriv

/-- **2nd-Order Amari `α`-Divergence Eguchi Equation (Source Argument)**:
by `α ↔ -α` duality, differentiating `D^{(α)}(Q t ∥ P)` twice at `t = 0` also recovers
`fisherMetric P (dq 0) (dq 0)` for every `α ≠ ±1`. -/
theorem eguchi_amariAlpha_left_secondDeriv (αParam : ℝ) (hα : αParam ^ 2 ≠ 1)
    (P : ProbInterior α) (Q : ℝ → ProbInterior α) (hQ0 : Q 0 = P)
    (dq : ℝ → α → ℝ) (d2q : α → ℝ)
    (hd1 : ∀ t a, HasDerivAt (fun s => (Q s).p a) (dq t a) t)
    (hd2 : ∀ a, HasDerivAt (fun t => dq t a) (d2q a) 0) :
    deriv (deriv (fun s => amariAlphaDivergence αParam (Q s).p P.p)) 0 =
      fisherMetric P (dq 0) (dq 0) := by
  have hfn :
      (fun s => amariAlphaDivergence αParam (Q s).p P.p) =
        fun s => amariAlphaDivergence (-αParam) P.p (Q s).p := by
    funext s
    simpa [neg_neg] using amariAlphaDivergence_dual (-αParam) (Q s).p P.p
  have hα' : (-αParam) ^ 2 ≠ 1 := by simpa using hα
  rw [hfn]
  exact eguchi_amariAlpha_right_secondDeriv (-αParam) hα' P Q hQ0 dq d2q hd1 hd2

end EguchiMetrics

/-! ### 2. Exponential-Family Third Cumulant, Metric Derivative & Dual Connection Manifold -/

section ExpFamilyDualManifold

variable {α : Type*} [Fintype α] {d : ℕ}

/-- Coordinate Fisher bilinear form `uᵀ G(θ) v` on `Information.FiniteExpFamily d`. -/
def fisherBilinearForm (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * InfoGeometry.Information.fisherMetric F θ i j * v j

/-- Equivalence between `fisherBilinearForm F θ u v` and the expectation of centered score
products. -/
theorem fisherBilinearForm_eq_expectation (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v : Fin d → ℝ) :
    fisherBilinearForm F θ u v =
      InfoGeometry.Information.expectation F θ
        (fun x => InfoGeometry.Information.centeredLinearStat F θ u x *
          InfoGeometry.Information.centeredLinearStat F θ v x) := by
  unfold fisherBilinearForm InfoGeometry.Information.fisherMetric
    InfoGeometry.Information.covariance InfoGeometry.Information.expectation
  calc
    ∑ i, ∑ j, u i * (∑ x, InfoGeometry.Information.density F θ x *
        (InfoGeometry.Information.centeredStat F θ i x *
          InfoGeometry.Information.centeredStat F θ j x)) * v j
        = ∑ i, ∑ j, ∑ x, InfoGeometry.Information.density F θ x *
            ((u i * InfoGeometry.Information.centeredStat F θ i x) *
              (v j * InfoGeometry.Information.centeredStat F θ j x)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
    _ = ∑ x, ∑ i, ∑ j, InfoGeometry.Information.density F θ x *
          ((u i * InfoGeometry.Information.centeredStat F θ i x) *
            (v j * InfoGeometry.Information.centeredStat F θ j x)) := by
          have h1 (i : Fin d) :
              ∑ j, ∑ x, InfoGeometry.Information.density F θ x *
                  ((u i * InfoGeometry.Information.centeredStat F θ i x) *
                    (v j * InfoGeometry.Information.centeredStat F θ j x)) =
                ∑ x, ∑ j, InfoGeometry.Information.density F θ x *
                  ((u i * InfoGeometry.Information.centeredStat F θ i x) *
                    (v j * InfoGeometry.Information.centeredStat F θ j x)) := Finset.sum_comm
          simp_rw [h1]
          exact Finset.sum_comm
    _ = ∑ x, InfoGeometry.Information.density F θ x *
          (InfoGeometry.Information.centeredLinearStat F θ u x *
            InfoGeometry.Information.centeredLinearStat F θ v x) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat F θ u x,
            InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat F θ v x]
          calc
            ∑ i, ∑ j, InfoGeometry.Information.density F θ x *
                ((u i * InfoGeometry.Information.centeredStat F θ i x) *
                  (v j * InfoGeometry.Information.centeredStat F θ j x))
                = InfoGeometry.Information.density F θ x *
                    ∑ i, ∑ j, (u i * InfoGeometry.Information.centeredStat F θ i x) *
                      (v j * InfoGeometry.Information.centeredStat F θ j x) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro i _
                    rw [Finset.mul_sum]
            _ = InfoGeometry.Information.density F θ x *
                    ((∑ i, u i * InfoGeometry.Information.centeredStat F θ i x) *
                      (∑ j, v j * InfoGeometry.Information.centeredStat F θ j x)) := by
                    congr 1
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl ?_
                    intro i _
                    rw [Finset.mul_sum]

@[simp]
theorem fisherBilinearForm_self (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ v : Fin d → ℝ) :
    fisherBilinearForm F θ v v = InfoGeometry.Information.fisherQuadratic F θ v := rfl

theorem fisherBilinearForm_symm (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v : Fin d → ℝ) :
    fisherBilinearForm F θ u v = fisherBilinearForm F θ v u := by
  rw [fisherBilinearForm_eq_expectation, fisherBilinearForm_eq_expectation]
  unfold InfoGeometry.Information.expectation
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

theorem fisherBilinearForm_add_left (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u₁ u₂ v : Fin d → ℝ) :
    fisherBilinearForm F θ (u₁ + u₂) v =
      fisherBilinearForm F θ u₁ v + fisherBilinearForm F θ u₂ v := by
  unfold fisherBilinearForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [Pi.add_apply]
  ring

theorem fisherBilinearForm_smul_left (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) (r : ℝ) (u v : Fin d → ℝ) :
    fisherBilinearForm F θ (r • u) v = r * fisherBilinearForm F θ u v := by
  unfold fisherBilinearForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem fisherBilinearForm_add_right (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v₁ v₂ : Fin d → ℝ) :
    fisherBilinearForm F θ u (v₁ + v₂) =
      fisherBilinearForm F θ u v₁ + fisherBilinearForm F θ u v₂ := by
  rw [fisherBilinearForm_symm, fisherBilinearForm_add_left,
    fisherBilinearForm_symm F θ v₁ u, fisherBilinearForm_symm F θ v₂ u]

theorem fisherBilinearForm_smul_right (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) (r : ℝ) (u v : Fin d → ℝ) :
    fisherBilinearForm F θ u (r • v) = r * fisherBilinearForm F θ u v := by
  rw [fisherBilinearForm_symm, fisherBilinearForm_smul_left, fisherBilinearForm_symm]

/-- Totally symmetric third cumulant / Amari–Chentsov skewness tensor on `FiniteExpFamily d`:
`T(θ)(u, v, w) = E_θ[(T_u - μ_u)(T_v - μ_v)(T_w - μ_w)]`. -/
def thirdCumulant (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v w : Fin d → ℝ) : ℝ :=
  InfoGeometry.Information.expectation F θ
    (fun x => InfoGeometry.Information.centeredLinearStat F θ u x *
      InfoGeometry.Information.centeredLinearStat F θ v x *
      InfoGeometry.Information.centeredLinearStat F θ w x)

/-- Exact bridge equating the exponential-family `thirdCumulant` to
`DualConnections.chentsovTensor` evaluated on centered scores. -/
theorem thirdCumulant_eq_chentsovTensor [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d) (θ u v w : Fin d → ℝ) :
    thirdCumulant F θ u v w =
      DualConnections.chentsovTensor (DualConnections.finiteExpFamilyProbMap F) θ
        (DualConnections.centeredScore F θ u)
        (DualConnections.centeredScore F θ v)
        (DualConnections.centeredScore F θ w) := by
  unfold thirdCumulant DualConnections.chentsovTensor InfoGeometry.Information.expectation
    DualConnections.centeredScore
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [DualConnections.finiteExpFamilyProbMap_apply_toReal]

theorem thirdCumulant_symm_12 (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v w : Fin d → ℝ) :
    thirdCumulant F θ u v w = thirdCumulant F θ v u w := by
  unfold thirdCumulant InfoGeometry.Information.expectation
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

theorem thirdCumulant_symm_23 (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v w : Fin d → ℝ) :
    thirdCumulant F θ u v w = thirdCumulant F θ u w v := by
  unfold thirdCumulant InfoGeometry.Information.expectation
  refine Finset.sum_congr rfl ?_
  intro x _
  ring

lemma centeredLinearStat_add (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v : Fin d → ℝ) (x : α) :
    InfoGeometry.Information.centeredLinearStat F θ (u + v) x =
      InfoGeometry.Information.centeredLinearStat F θ u x +
        InfoGeometry.Information.centeredLinearStat F θ v x := by
  rw [InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat,
    InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat,
    InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.add_apply]
  ring

lemma centeredLinearStat_smul (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) (r : ℝ) (u : Fin d → ℝ) (x : α) :
    InfoGeometry.Information.centeredLinearStat F θ (r • u) x =
      r * InfoGeometry.Information.centeredLinearStat F θ u x := by
  rw [InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat,
    InfoGeometry.Information.centeredLinearStat_eq_sum_centeredStat, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem thirdCumulant_add_left (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u₁ u₂ v w : Fin d → ℝ) :
    thirdCumulant F θ (u₁ + u₂) v w =
      thirdCumulant F θ u₁ v w + thirdCumulant F θ u₂ v w := by
  unfold thirdCumulant InfoGeometry.Information.expectation
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  dsimp only
  rw [centeredLinearStat_add]
  ring

theorem thirdCumulant_add_mid (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v₁ v₂ w : Fin d → ℝ) :
    thirdCumulant F θ u (v₁ + v₂) w =
      thirdCumulant F θ u v₁ w + thirdCumulant F θ u v₂ w := by
  rw [thirdCumulant_symm_12, thirdCumulant_add_left,
    thirdCumulant_symm_12 F θ v₁ u w, thirdCumulant_symm_12 F θ v₂ u w]

theorem thirdCumulant_smul_mid (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u : Fin d → ℝ) (r : ℝ) (v w : Fin d → ℝ) :
    thirdCumulant F θ u (r • v) w = r * thirdCumulant F θ u v w := by
  unfold thirdCumulant InfoGeometry.Information.expectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  dsimp only
  rw [centeredLinearStat_smul]
  ring

theorem thirdCumulant_add_right (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v w₁ w₂ : Fin d → ℝ) :
    thirdCumulant F θ u v (w₁ + w₂) =
      thirdCumulant F θ u v w₁ + thirdCumulant F θ u v w₂ := by
  rw [thirdCumulant_symm_23, thirdCumulant_add_mid,
    thirdCumulant_symm_23 F θ u w₁ v, thirdCumulant_symm_23 F θ u w₂ v]

theorem thirdCumulant_smul_right (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u v : Fin d → ℝ) (r : ℝ) (w : Fin d → ℝ) :
    thirdCumulant F θ u v (r • w) = r * thirdCumulant F θ u v w := by
  rw [thirdCumulant_symm_23, thirdCumulant_smul_mid, thirdCumulant_symm_23]

lemma expectation_centeredLinearStat_eq_zero [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d) (θ v : Fin d → ℝ) :
    InfoGeometry.Information.expectation F θ
      (InfoGeometry.Information.centeredLinearStat F θ v) = 0 := by
  unfold InfoGeometry.Information.expectation InfoGeometry.Information.centeredLinearStat
  calc
    ∑ x, InfoGeometry.Information.density F θ x *
        (InfoGeometry.Information.linearStat F v x -
          InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v))
        = (∑ x, InfoGeometry.Information.density F θ x *
              InfoGeometry.Information.linearStat F v x) -
            (∑ x, InfoGeometry.Information.density F θ x) *
              InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
    _ = InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v) -
          1 * InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v) := by
          rw [InfoGeometry.Information.density_sum_one]
          rfl
    _ = 0 := by ring

/-- Directional derivative at `t = 0` of the exponential-family density `θ + t • u`. -/
theorem hasDerivAt_density_slice [Nonempty α] (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ u : Fin d → ℝ) (x : α) :
    HasDerivAt (fun t : ℝ => InfoGeometry.Information.density F (θ + t • u) x)
      (InfoGeometry.Information.density F θ x *
        InfoGeometry.Information.centeredLinearStat F θ u x) 0 := by
  let w := sliceBaseWeights F θ
  let c := InfoGeometry.Information.linearStat F u
  have hwpos : ∀ y, 0 < w y := sliceBaseWeights_pos F θ
  have hfn :
      (fun t : ℝ => InfoGeometry.Information.density F (θ + t • u) x) =
        fun t : ℝ => logSumExpWeight w c t x := by
    funext t
    unfold InfoGeometry.Information.density InfoGeometry.Information.partition
      logSumExpWeight logSumExpPartition w c sliceBaseWeights
    have hnum :
        Real.exp (InfoGeometry.Information.naturalParam F (θ + t • u) x) * F.base x =
          (Real.exp (InfoGeometry.Information.naturalParam F θ x) * F.base x) *
            Real.exp (t * InfoGeometry.Information.linearStat F u x) := by
      have hnat : InfoGeometry.Information.naturalParam F (θ + t • u) x =
          InfoGeometry.Information.naturalParam F θ x + t * InfoGeometry.Information.linearStat F u x := by
        unfold InfoGeometry.Information.naturalParam InfoGeometry.Information.linearStat
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hnat, Real.exp_add]
      ring
    have hden :
        ∑ y, Real.exp (InfoGeometry.Information.naturalParam F (θ + t • u) y) * F.base y =
          ∑ y, (Real.exp (InfoGeometry.Information.naturalParam F θ y) * F.base y) *
            Real.exp (t * InfoGeometry.Information.linearStat F u y) := by
      refine Finset.sum_congr rfl ?_
      intro y _
      have hnat : InfoGeometry.Information.naturalParam F (θ + t • u) y =
          InfoGeometry.Information.naturalParam F θ y + t * InfoGeometry.Information.linearStat F u y := by
        unfold InfoGeometry.Information.naturalParam InfoGeometry.Information.linearStat
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hnat, Real.exp_add]
      ring
    rw [hnum, hden]
  rw [hfn]
  have hpart := hasDerivAt_logSumExpPartition w c 0
  have hterm := hasDerivAt_logSumExpPartition_term w c x 0
  have hZne : logSumExpPartition w c 0 ≠ 0 := (logSumExp_sum_pos w c hwpos 0).ne'
  have hquot := hterm.div hpart hZne
  have hlogmean :
      logSumExpMean w c 0 =
        InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F u) := by
    rw [logSumExpMean_eq_weighted_sum w c hwpos 0]
    unfold InfoGeometry.Information.expectation
    refine Finset.sum_congr rfl ?_
    intro y _
    have hy : logSumExpWeight w c 0 y = InfoGeometry.Information.density F θ y := by
      unfold logSumExpWeight logSumExpPartition w sliceBaseWeights
        InfoGeometry.Information.density InfoGeometry.Information.partition
      simp
    rw [hy]
  have hval :
      (w x * (c x * Real.exp ((0 : ℝ) * c x)) * logSumExpPartition w c 0 -
          w x * Real.exp ((0 : ℝ) * c x) * logSumExpMoment1 w c 0) /
          logSumExpPartition w c 0 ^ (2 : ℕ) =
        InfoGeometry.Information.density F θ x *
          InfoGeometry.Information.centeredLinearStat F θ u x := by
    unfold InfoGeometry.Information.centeredLinearStat
    rw [← hlogmean]
    have hx0 : logSumExpWeight w c 0 x = InfoGeometry.Information.density F θ x := by
      unfold logSumExpWeight logSumExpPartition w sliceBaseWeights
        InfoGeometry.Information.density InfoGeometry.Information.partition
      simp
    rw [← hx0]
    unfold logSumExpWeight logSumExpMean logSumExpMoment1 c
    simp only [zero_mul, Real.exp_zero, mul_one]
    have hZne' : logSumExpPartition w (InfoGeometry.Information.linearStat F u) 0 ≠ 0 := hZne
    field_simp [hZne']
  rwa [hval] at hquot

/-- **Fundamental Amari Metric Derivative = Third Cumulant Theorem**:
for every finite exponential family `F`, the directional derivative of the Fisher metric along
`t ↦ θ + t • u` at `0` equals `thirdCumulant F θ u v w`. -/
theorem hasDerivAt_fisherBilinearForm_slice [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d) (θ u v w : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => fisherBilinearForm F (θ + t • u) v w)
      (thirdCumulant F θ u v w) 0 := by
  have hfn :
      (fun t : ℝ => fisherBilinearForm F (θ + t • u) v w) =
        fun t : ℝ => InfoGeometry.Information.expectation F (θ + t • u)
          (fun x => InfoGeometry.Information.centeredLinearStat F (θ + t • u) v x *
            InfoGeometry.Information.centeredLinearStat F (θ + t • u) w x) := by
    funext t
    exact fisherBilinearForm_eq_expectation F (θ + t • u) v w
  rw [hfn]
  let cV : ℝ := ∑ x, (InfoGeometry.Information.density F θ x *
      InfoGeometry.Information.centeredLinearStat F θ u x) *
    InfoGeometry.Information.linearStat F v x
  let cW : ℝ := ∑ x, (InfoGeometry.Information.density F θ x *
      InfoGeometry.Information.centeredLinearStat F θ u x) *
    InfoGeometry.Information.linearStat F w x
  have hExpV :
      HasDerivAt (fun t : ℝ =>
          InfoGeometry.Information.expectation F (θ + t • u)
            (InfoGeometry.Information.linearStat F v)) cV 0 := by
    unfold InfoGeometry.Information.expectation
    exact HasDerivAt.fun_sum (fun x _ => (hasDerivAt_density_slice F θ u x).mul_const _)
  have hExpW :
      HasDerivAt (fun t : ℝ =>
          InfoGeometry.Information.expectation F (θ + t • u)
            (InfoGeometry.Information.linearStat F w)) cW 0 := by
    unfold InfoGeometry.Information.expectation
    exact HasDerivAt.fun_sum (fun x _ => (hasDerivAt_density_slice F θ u x).mul_const _)
  have hsum :
      HasDerivAt
        (fun t : ℝ => InfoGeometry.Information.expectation F (θ + t • u)
          (fun x => InfoGeometry.Information.centeredLinearStat F (θ + t • u) v x *
            InfoGeometry.Information.centeredLinearStat F (θ + t • u) w x))
        (∑ x, ((InfoGeometry.Information.density F θ x *
            InfoGeometry.Information.centeredLinearStat F θ u x) *
              (InfoGeometry.Information.centeredLinearStat F θ v x *
                InfoGeometry.Information.centeredLinearStat F θ w x) +
            InfoGeometry.Information.density F θ x *
              ((-cV) * InfoGeometry.Information.centeredLinearStat F θ w x +
                InfoGeometry.Information.centeredLinearStat F θ v x * (-cW)))) 0 := by
    unfold InfoGeometry.Information.expectation
    refine HasDerivAt.fun_sum ?_
    intro x _
    have hV :
        HasDerivAt (fun t : ℝ => InfoGeometry.Information.centeredLinearStat F (θ + t • u) v x)
          (-cV) 0 := by
      simpa [InfoGeometry.Information.centeredLinearStat] using
        (hasDerivAt_const (0 : ℝ) (InfoGeometry.Information.linearStat F v x)).fun_sub hExpV
    have hW :
        HasDerivAt (fun t : ℝ => InfoGeometry.Information.centeredLinearStat F (θ + t • u) w x)
          (-cW) 0 := by
      simpa [InfoGeometry.Information.centeredLinearStat] using
        (hasDerivAt_const (0 : ℝ) (InfoGeometry.Information.linearStat F w x)).fun_sub hExpW
    simpa [smul_eq_mul, add_zero] using (hasDerivAt_density_slice F θ u x).fun_mul (hV.fun_mul hW)
  have hval :
      (∑ x, ((InfoGeometry.Information.density F θ x *
          InfoGeometry.Information.centeredLinearStat F θ u x) *
            (InfoGeometry.Information.centeredLinearStat F θ v x *
              InfoGeometry.Information.centeredLinearStat F θ w x) +
          InfoGeometry.Information.density F θ x *
            ((-cV) * InfoGeometry.Information.centeredLinearStat F θ w x +
              InfoGeometry.Information.centeredLinearStat F θ v x * (-cW)))) =
        thirdCumulant F θ u v w := by
    have hzV :
        ∑ x, InfoGeometry.Information.density F θ x *
            InfoGeometry.Information.centeredLinearStat F θ v x = 0 :=
      expectation_centeredLinearStat_eq_zero F θ v
    have hzW :
        ∑ x, InfoGeometry.Information.density F θ x *
            InfoGeometry.Information.centeredLinearStat F θ w x = 0 :=
      expectation_centeredLinearStat_eq_zero F θ w
    have hzero :
        ∑ x, InfoGeometry.Information.density F θ x *
            ((-cV) * InfoGeometry.Information.centeredLinearStat F θ w x +
              InfoGeometry.Information.centeredLinearStat F θ v x * (-cW)) = 0 := by
      calc
        ∑ x, InfoGeometry.Information.density F θ x *
              ((-cV) * InfoGeometry.Information.centeredLinearStat F θ w x +
                InfoGeometry.Information.centeredLinearStat F θ v x * (-cW))
            = (-cV) * (∑ x, InfoGeometry.Information.density F θ x *
                  InfoGeometry.Information.centeredLinearStat F θ w x) +
                (-cW) * (∑ x, InfoGeometry.Information.density F θ x *
                  InfoGeometry.Information.centeredLinearStat F θ v x) := by
              have hexp :
                  (fun x => InfoGeometry.Information.density F θ x *
                    ((-cV) * InfoGeometry.Information.centeredLinearStat F θ w x +
                      InfoGeometry.Information.centeredLinearStat F θ v x * (-cW))) =
                    fun x => (-cV) * (InfoGeometry.Information.density F θ x *
                        InfoGeometry.Information.centeredLinearStat F θ w x) +
                      (-cW) * (InfoGeometry.Information.density F θ x *
                        InfoGeometry.Information.centeredLinearStat F θ v x) := by
                funext x; ring
              rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = 0 := by rw [hzW, hzV, mul_zero, mul_zero, add_zero]
    rw [Finset.sum_add_distrib, hzero, add_zero]
    unfold thirdCumulant InfoGeometry.Information.expectation
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  rwa [hval] at hsum

/-- Fisher covariance linear endomorphism `v ↦ G(θ) v` on `Fin d → ℝ`. -/
def fisherLinearOp (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun v i := ∑ j, InfoGeometry.Information.fisherMetric F θ i j * v j
  map_add' u v := by
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring

theorem dot_fisherLinearOp_eq_fisherBilinearForm
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d) (θ u v : Fin d → ℝ) :
    ∑ i, u i * fisherLinearOp F θ v i = fisherBilinearForm F θ u v := by
  unfold fisherLinearOp fisherBilinearForm
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- Linear independence of sufficient statistics makes `fisherLinearOp F θ` injective. -/
theorem fisherLinearOp_injective [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (h_indep : ∀ v : Fin d → ℝ, v ≠ 0 →
      ∃ x, InfoGeometry.Information.linearStat F v x ≠
        InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v)) :
    Function.Injective (fisherLinearOp F θ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  have hpos := InfoGeometry.Information.fisher_positive_definite F θ h_indep v hv0
  have hzero : InfoGeometry.Information.fisherQuadratic F θ v = 0 := by
    rw [← fisherBilinearForm_self F θ v, ← dot_fisherLinearOp_eq_fisherBilinearForm]
    have hv' : fisherLinearOp F θ v = 0 := LinearMap.mem_ker.mp hv
    simp [hv']
  linarith

/-- Invertible Fisher metric operator `(Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)` for any non-degenerate
finite exponential family at natural parameter `θ`. -/
def fisherLinearEquiv [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (h_indep : ∀ v : Fin d → ℝ, v ≠ 0 →
      ∃ x, InfoGeometry.Information.linearStat F v x ≠
        InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v)) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearEquiv.ofBijective (fisherLinearOp F θ)
    ⟨fisherLinearOp_injective F θ h_indep,
      LinearMap.surjective_of_injective (fisherLinearOp_injective F θ h_indep)⟩

/-- Constructive non-trivial `DualConnectionManifold (Fin d → ℝ)` on the natural-parameter
tangent space of a finite exponential family `F` at `θ`, with flat exponential connection
`∇^(e) = 0`, Fisher metric `g = fisherBilinearForm F θ`, metric derivative `diff_g = thirdCumulant F θ`,
and Christoffel mixture connection `∇^(m) = G(θ)⁻¹ ∘ T(θ)` discharging `amari_duality`. -/
def expFamilyDualConnectionManifold [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d)
    (θ : Fin d → ℝ)
    (h_indep : ∀ v : Fin d → ℝ, v ≠ 0 →
      ∃ x, InfoGeometry.Information.linearStat F v x ≠
        InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v)) :
    _root_.InfoGeometry.Modular.AmariChentsovDualConnections.DualConnectionManifold (Fin d → ℝ) where
  g := fisherBilinearForm F θ
  g_add_left := fisherBilinearForm_add_left F θ
  g_add_right := fisherBilinearForm_add_right F θ
  g_smul_left r x y := fisherBilinearForm_smul_left F θ r x y
  g_smul_right r x y := fisherBilinearForm_smul_right F θ r x y
  g_symm := fisherBilinearForm_symm F θ
  g_pos_def v hv := InfoGeometry.Information.fisher_positive_definite F θ h_indep v hv
  diff_g := thirdCumulant F θ
  diff_g_symm := thirdCumulant_symm_23 F θ
  diff_g_add := thirdCumulant_add_left F θ
  nabla_e _ _ := 0
  nabla_m u z := (fisherLinearEquiv F θ h_indep).symm (fun i => thirdCumulant F θ u (Pi.single i 1) z)
  nabla_e_add_left _ _ _ := by simp
  nabla_e_add_right _ _ _ := by simp
  nabla_e_smul_left _ _ _ := by simp
  nabla_e_smul_right _ _ _ := by simp
  nabla_m_add_left x y z := by
    apply (fisherLinearEquiv F θ h_indep).injective
    rw [map_add]
    ext i
    simp [fisherLinearEquiv, thirdCumulant_add_left]
  nabla_m_add_right x y z := by
    apply (fisherLinearEquiv F θ h_indep).injective
    rw [map_add]
    ext i
    simp [fisherLinearEquiv, thirdCumulant_add_right]
  nabla_m_smul_left r x y := by
    apply (fisherLinearEquiv F θ h_indep).injective
    rw [map_smul]
    ext i
    simp [fisherLinearEquiv, thirdCumulant_symm_12, thirdCumulant_smul_mid]
  nabla_m_smul_right r x y := by
    apply (fisherLinearEquiv F θ h_indep).injective
    rw [map_smul]
    ext i
    simp [fisherLinearEquiv, thirdCumulant_smul_right]
  amari_duality x y z := by
    have hzero : fisherBilinearForm F θ 0 z = 0 := by
      unfold fisherBilinearForm
      simp
    have hinv :
        fisherLinearOp F θ
            ((fisherLinearEquiv F θ h_indep).symm (fun i => thirdCumulant F θ x (Pi.single i 1) z)) =
          fun i => thirdCumulant F θ x (Pi.single i 1) z := by
      change (fisherLinearEquiv F θ h_indep)
        ((fisherLinearEquiv F θ h_indep).symm (fun i => thirdCumulant F θ x (Pi.single i 1) z)) = _
      exact (fisherLinearEquiv F θ h_indep).apply_symm_apply _
    have hy : y = ∑ i, y i • (Pi.single i 1 : Fin d → ℝ) := by
      ext j
      simp [Pi.single_apply]
    have hm :
        fisherBilinearForm F θ y
            ((fisherLinearEquiv F θ h_indep).symm (fun i => thirdCumulant F θ x (Pi.single i 1) z)) =
          thirdCumulant F θ x y z := by
      rw [← dot_fisherLinearOp_eq_fisherBilinearForm, hinv]
      conv_rhs => rw [hy]
      clear hy hinv hzero
      have hdecomp (s : Finset (Fin d)) :
          thirdCumulant F θ x (∑ i ∈ s, y i • (Pi.single i 1 : Fin d → ℝ)) z =
            ∑ i ∈ s, y i * thirdCumulant F θ x (Pi.single i 1) z := by
        classical
        induction s using Finset.induction_on with
        | empty =>
            simp only [Finset.sum_empty]
            have h0 : (0 : Fin d → ℝ) = (0 : ℝ) • (0 : Fin d → ℝ) := by simp
            rw [h0, thirdCumulant_smul_mid, zero_mul]
        | insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha, thirdCumulant_add_mid,
              thirdCumulant_smul_mid, ih]
      exact (hdecomp Finset.univ).symm
    rw [hzero, zero_add, hm]

/-- The abstract Amari cubic form `amariCubicForm` of `expFamilyDualConnectionManifold` recovers
the statistical `thirdCumulant` identically. -/
theorem expFamily_amariCubicForm_eq_thirdCumulant [Nonempty α]
    (F : InfoGeometry.Information.FiniteExpFamily (α := α) d) (θ : Fin d → ℝ)
    (h_indep : ∀ v : Fin d → ℝ, v ≠ 0 →
      ∃ x, InfoGeometry.Information.linearStat F v x ≠
        InfoGeometry.Information.expectation F θ (InfoGeometry.Information.linearStat F v))
    (u v w : Fin d → ℝ) :
    _root_.InfoGeometry.Modular.AmariChentsovDualConnections.amariCubicForm
        (expFamilyDualConnectionManifold F θ h_indep) u v w =
      thirdCumulant F θ u v w := by
  let M := expFamilyDualConnectionManifold F θ h_indep
  have he : M.nabla_e u v = 0 := rfl
  have hm : M.nabla_m u v - M.nabla_e u v = M.nabla_m u v := by rw [he, sub_zero]
  have h2 := M.amari_duality u w v
  have hs := M.g_symm (M.nabla_m u v) w
  have hs2 := M.g_symm w (M.nabla_m u v)
  have hds := M.diff_g_symm u w v
  change M.g (M.nabla_m u v - M.nabla_e u v) w = M.diff_g u v w
  rw [hm]
  have hew : M.g (M.nabla_e u w) v = 0 := by
    have he2 : M.nabla_e u w = 0 := rfl
    rw [he2]
    unfold M expFamilyDualConnectionManifold fisherBilinearForm
    simp
  linarith [h2, hew, hs, hs2, hds]

end ExpFamilyDualManifold

/-! ### 3. Genuine Affine Connection Curvature & `CurvatureDecompositionPacket` Instance -/

section AffineCurvature

variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- Linear connection map `T →ₗ[ℝ] Module.End ℝ T` extracted from an affine connection. -/
def connEnd (nabla : T → T → T)
    (h_add_left : ∀ x y z, nabla (x + y) z = nabla x z + nabla y z)
    (h_add_right : ∀ x y z, nabla x (y + z) = nabla x y + nabla x z)
    (h_smul_left : ∀ (r : ℝ) x y, nabla (r • x) y = r • nabla x y)
    (h_smul_right : ∀ (r : ℝ) x y, nabla x (r • y) = r • nabla x y) :
    T →ₗ[ℝ] Module.End ℝ T where
  toFun x :=
    { toFun := nabla x
      map_add' := h_add_right x
      map_smul' := fun r y => h_smul_right r x y }
  map_add' x y := by
    ext z
    exact h_add_left x y z
  map_smul' r x := by
    ext z
    exact h_smul_left r x z

/-- Riemann curvature endomorphism `R^∇(X, Y) = [∇_X, ∇_Y] - ∇_[X, Y]`. -/
def connCurvature (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) : Module.End ℝ T :=
  Statistical.endComm (conn X) (conn Y) - conn (bracket X Y)

/-- Midpoint Levi-Civita connection `(1 / 2) • (∇ + ∇*)`. -/
def meanConn (conn connStar : T →ₗ[ℝ] Module.End ℝ T) : T →ₗ[ℝ] Module.End ℝ T :=
  (1 / 2 : ℝ) • (conn + connStar)

/-- Skew difference tensor `K = (1 / 2) • (∇ - ∇*)`. -/
def skewConnTensor (conn connStar : T →ₗ[ℝ] Module.End ℝ T) : T →ₗ[ℝ] Module.End ℝ T :=
  (1 / 2 : ℝ) • (conn - connStar)

/-- Covariant exterior derivative `(d^{∇⁰} K)(X, Y) = [∇⁰_X, K_Y] - [∇⁰_Y, K_X] - K_[X, Y]`. -/
def covariantExteriorDeriv (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn0 K : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) : Module.End ℝ T :=
  Statistical.endComm (conn0 X) (K Y) - Statistical.endComm (conn0 Y) (K X) - K (bracket X Y)

lemma endComm_add_left (A₁ A₂ B : Module.End ℝ T) :
    Statistical.endComm (A₁ + A₂) B = Statistical.endComm A₁ B + Statistical.endComm A₂ B := by
  ext x
  simp only [Statistical.endComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_add]
  abel

lemma endComm_add_right (A B₁ B₂ : Module.End ℝ T) :
    Statistical.endComm A (B₁ + B₂) = Statistical.endComm A B₁ + Statistical.endComm A B₂ := by
  ext x
  simp only [Statistical.endComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_add]
  abel

lemma endComm_sub_left (A₁ A₂ B : Module.End ℝ T) :
    Statistical.endComm (A₁ - A₂) B = Statistical.endComm A₁ B - Statistical.endComm A₂ B := by
  ext x
  simp only [Statistical.endComm, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

lemma endComm_sub_right (A B₁ B₂ : Module.End ℝ T) :
    Statistical.endComm A (B₁ - B₂) = Statistical.endComm A B₁ - Statistical.endComm A B₂ := by
  ext x
  simp only [Statistical.endComm, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

lemma meanConn_add_skewConn (conn connStar : T →ₗ[ℝ] Module.End ℝ T) :
    meanConn conn connStar + skewConnTensor conn connStar = conn := by
  ext x y
  change (1 / 2 : ℝ) • (conn x y + connStar x y) + (1 / 2 : ℝ) • (conn x y - connStar x y) =
    conn x y
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  calc
    (1 / 2 : ℝ) • (conn x y + connStar x y) + (1 / 2 : ℝ) • (conn x y - connStar x y)
        = ((1 / 2 : ℝ) • conn x y + (1 / 2 : ℝ) • conn x y) +
            ((1 / 2 : ℝ) • connStar x y - (1 / 2 : ℝ) • connStar x y) := by
          rw [smul_add, smul_sub]; abel
    _ = ((1 / 2 : ℝ) + 1 / 2) • conn x y + 0 := by rw [← add_smul, sub_self]
    _ = conn x y := by rw [add_zero, hhalf, one_smul]

lemma meanConn_sub_skewConn (conn connStar : T →ₗ[ℝ] Module.End ℝ T) :
    meanConn conn connStar - skewConnTensor conn connStar = connStar := by
  ext x y
  change (1 / 2 : ℝ) • (conn x y + connStar x y) - (1 / 2 : ℝ) • (conn x y - connStar x y) =
    connStar x y
  have hhalf : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  calc
    (1 / 2 : ℝ) • (conn x y + connStar x y) - (1 / 2 : ℝ) • (conn x y - connStar x y)
        = ((1 / 2 : ℝ) • conn x y - (1 / 2 : ℝ) • conn x y) +
            ((1 / 2 : ℝ) • connStar x y + (1 / 2 : ℝ) • connStar x y) := by
          rw [smul_add, smul_sub]; abel
    _ = 0 + ((1 / 2 : ℝ) + 1 / 2) • connStar x y := by rw [sub_self, ← add_smul]
    _ = connStar x y := by rw [zero_add, hhalf, one_smul]

/-- Exact decomposition `R^{∇₀ + K}(X, Y) = R^{∇₀}(X, Y) + d^{∇₀} K(X, Y) + [K_X, K_Y]`. -/
theorem connCurvature_add_decomp (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn0 K : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) :
    connCurvature bracket (conn0 + K) X Y =
      connCurvature bracket conn0 X Y +
        covariantExteriorDeriv bracket conn0 K X Y +
        Statistical.endComm (K X) (K Y) := by
  dsimp [connCurvature, covariantExteriorDeriv]
  rw [endComm_add_left, endComm_add_right, endComm_add_right, Statistical.endComm_swap (K X) (conn0 Y)]
  abel

/-- Exact decomposition `R^{∇₀ - K}(X, Y) = R^{∇₀}(X, Y) - d^{∇₀} K(X, Y) + [K_X, K_Y]`. -/
theorem connCurvature_sub_decomp (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn0 K : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) :
    connCurvature bracket (conn0 - K) X Y =
      connCurvature bracket conn0 X Y -
        covariantExteriorDeriv bracket conn0 K X Y +
        Statistical.endComm (K X) (K Y) := by
  dsimp [connCurvature, covariantExteriorDeriv]
  rw [endComm_sub_left, endComm_sub_right, endComm_sub_right, Statistical.endComm_swap (K X) (conn0 Y)]
  abel

/-- Unconditional curvature sum law `R^∇ + R^{∇*} = 2 R^{∇⁰} + 2 [K_X, K_Y]`. -/
theorem connCurvature_sum (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn connStar : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) :
    connCurvature bracket conn X Y + connCurvature bracket connStar X Y =
      (2 : ℝ) • connCurvature bracket (meanConn conn connStar) X Y +
        (2 : ℝ) • Statistical.endComm (skewConnTensor conn connStar X) (skewConnTensor conn connStar Y) := by
  let conn0 := meanConn conn connStar
  let K := skewConnTensor conn connStar
  have h1 : conn = conn0 + K := (meanConn_add_skewConn conn connStar).symm
  have h2 : connStar = conn0 - K := (meanConn_sub_skewConn conn connStar).symm
  conv_lhs => rw [h1, h2]
  rw [connCurvature_add_decomp, connCurvature_sub_decomp, two_smul, two_smul]
  abel

/-- Unconditional curvature difference law `R^∇ - R^{∇*} = 2 d^{∇⁰} K`. -/
theorem connCurvature_diff (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn connStar : T →ₗ[ℝ] Module.End ℝ T) (X Y : T) :
    connCurvature bracket conn X Y - connCurvature bracket connStar X Y =
      (2 : ℝ) • covariantExteriorDeriv bracket (meanConn conn connStar) (skewConnTensor conn connStar) X Y := by
  let conn0 := meanConn conn connStar
  let K := skewConnTensor conn connStar
  have h1 : conn = conn0 + K := (meanConn_add_skewConn conn connStar).symm
  have h2 : connStar = conn0 - K := (meanConn_sub_skewConn conn connStar).symm
  conv_lhs => rw [h1, h2]
  rw [connCurvature_add_decomp, connCurvature_sub_decomp, two_smul]
  abel

/-- Constructive `Statistical.CurvatureDecompositionPacket` instantiated from genuine affine
connections `∇, ∇*` and bracket `bracket`, discharging both curvature laws without axioms. -/
def affineCurvatureDecompositionPacket (bracket : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (conn connStar : T →ₗ[ℝ] Module.End ℝ T) :
    Statistical.CurvatureDecompositionPacket T where
  Rnabla := connCurvature bracket conn
  RnablaStar := connCurvature bracket connStar
  Rzero := connCurvature bracket (meanConn conn connStar)
  K := skewConnTensor conn connStar
  dK := covariantExteriorDeriv bracket (meanConn conn connStar) (skewConnTensor conn connStar)
  curvature_sum := connCurvature_sum bracket conn connStar
  curvature_diff := connCurvature_diff bracket conn connStar

/-- Constructive `CurvatureDecompositionPacket` attached to any coordinate
`AmariChentsovDualConnections.DualConnectionManifold`. -/
def dualManifoldCurvaturePacket
    (M : _root_.InfoGeometry.Modular.AmariChentsovDualConnections.DualConnectionManifold T) :
    Statistical.CurvatureDecompositionPacket T :=
  affineCurvatureDecompositionPacket (0 : T →ₗ[ℝ] T →ₗ[ℝ] T)
    (connEnd M.nabla_e M.nabla_e_add_left M.nabla_e_add_right M.nabla_e_smul_left
      M.nabla_e_smul_right)
    (connEnd M.nabla_m M.nabla_m_add_left M.nabla_m_add_right M.nabla_m_smul_left
      M.nabla_m_smul_right)

/-- When a dual-connection manifold is dually flat (`R^{(e)} = R^{(m)} = 0`), the Levi-Civita
midpoint curvature obeys `R⁰(X, Y) = -[K_X, K_Y]` identically. -/
theorem dualManifold_leviCivita_curvature_of_flat
    (M : _root_.InfoGeometry.Modular.AmariChentsovDualConnections.DualConnectionManifold T)
    (hflat : ∀ X Y,
      (dualManifoldCurvaturePacket M).Rnabla X Y = 0 ∧
        (dualManifoldCurvaturePacket M).RnablaStar X Y = 0)
    (X Y : T) :
    (dualManifoldCurvaturePacket M).Rzero X Y =
      -Statistical.endComm ((dualManifoldCurvaturePacket M).K X)
        ((dualManifoldCurvaturePacket M).K Y) :=
  (dualManifoldCurvaturePacket M).dual_flat_curvature hflat X Y

end AffineCurvature

end InfoGeometry.InformationGeometry.EguchiMetricsAndDualFlatCurvature
