/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
import InfoGeometry.Canonical.TomitaArakiBKMKreinSoldering
import InfoGeometry.Projective.LegendreProjectiveDuality
import InfoGeometry.Projective.ProjectiveFenchelLegendreBridge
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Koszul–Souriau–Barbaresco Legendre–Projective Duality & Noncommutative BKM Cramér–Rao Soldering

This module supplies **Soldering Way III**, welding three previously disconnected
repository lanes:
- noncommutative Gibbs log-partition derivatives and centered BKM covariance
  (`NoncommutativeGibbsBKMHessianBridge`, `FiniteSelfAdjointGibbsStateBridge`),
- the real Hilbert–Schmidt carrier `HSRealSelfAdjoint n`
  (`TomitaArakiBKMKreinSoldering`), and
- Koszul–Hessian Bregman divergences, Fenchel–Legendre duality, and `SL2 ℝ`
  projective contragredient duality (`HessianThermodynamicManifold`,
  `LegendreProjectiveDuality`, `ProjectiveFenchelLegendreBridge`).

1. **Noncommutative Operator BKM Cauchy–Schwarz, Saturation, & Gibbs Cramér–Rao:**
   Proves `centeredBKMRealCovariance_sq_le`, exact affine-fluctuation saturation
   `centeredBKMRealCovariance_sq_eq_iff`, scalar BKM Cramér–Rao (`bkm_cramer_rao_bound`,
   `bkm_cramer_rao_unbiased`), and the unconditional Hessian-form Gibbs Cramér–Rao
   bounds (`gibbs_bkm_cramer_rao`, `gibbs_bkm_cramer_rao_unbiased`).
2. **Multivariate Noncommutative Matrix Cramér–Rao Inequality in Loewner Order:**
   Constructs `bkmCovMatrix` and `bkmCrossMatrix` and proves
   `bkmCovMatrix_posSemidef`, `multivariate_bkm_cramer_rao_posSemidef`
   (`Σ - J I⁻¹ Jᵀ ≥ 0`), and `multivariate_bkm_cramer_rao_unbiased` (`Σ - I⁻¹ ≥ 0`).
3. **Koszul–Souriau–Barbaresco Real Gibbs Slice Convexity & Strict Convexity:**
   Establishes everywhere differentiability of `realLogPartitionLine H A` and
   `gibbsMomentSlice H A`, monotonicity and strict monotonicity (for non-scalar `A`),
   exact first-order subgradient inequalities, and global `ConvexOn` / `StrictConvexOn`.
4. **Fenchel–Legendre Duality & `SL2 ℝ` Projective Contragredient Soldering:**
   Evaluates `gibbsFenchelDual H A` on the moment image, welds the Legendre contact
   sum to `Projective.MobiusDual.pairing` and `projectiveFenchelGap`, and builds the
   globally finite quadratic regularization `regGibbsFenchelDualPair : FenchelDualPair`.
5. **Full Noncommutative Operator Gibbs Potential, Moment Map, & Operator Bregman Law:**
   Equips `HSRealSelfAdjoint n` with `HessianThermodynamicManifold.InnerSpace`, defines
   `gibbsLogPartition` and `gibbsMomentMap`, and proves unconditional nonnegativity and
   strict positivity of `bregman_divergence gibbsLogPartition gibbsMomentMap` across
   arbitrary noncommuting `H₁, H₂ : HSRealSelfAdjoint n`.
-/

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace InfoGeometry.Canonical.KoszulSouriauLegendreCramerRaoSoldering

open Finset Matrix
open scoped BigOperators MatrixOrder
open SouriauOnsagerBKM
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsTwoPointFrechetBridge
open InfoGeometry.Canonical.NoncommutativeGibbsFaithfulNormalizationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredBKMCovariance
open InfoGeometry.Canonical.NoncommutativeGibbsCenteredFrechetBKMBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open InfoGeometry.Canonical.FiniteSelfAdjointGibbsStateBridge
open InfoGeometry.Canonical.TomitaArakiBKMKreinSoldering
open InfoGeometry.Algebra.HessianThermodynamicManifold
open InfoGeometry.Projective.MobiusDual
open InfoGeometry.Projective.LegendreProjectiveDuality
open InfoGeometry.Projective.ProjectiveFenchelLegendreBridge

/-! ## Scalar Arithmetic Helpers -/

private theorem scalar_quadratic_nonneg_bound {a ab b : ℝ}
    (hb : 0 < b) (hmin : 0 ≤ a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b) :
    ab ^ 2 ≤ a * b := by
  have hbne : b ≠ 0 := hb.ne'
  have h1 : 0 ≤ b * (a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b) :=
    mul_nonneg hb.le hmin
  have hid :
      b * (a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b) = a * b - ab ^ 2 := by
    field_simp [hbne]
    ring
  rw [hid] at h1
  exact sub_nonneg.mp h1

private theorem scalar_quadratic_zero_of_eq {a ab b : ℝ}
    (hb : 0 < b) (heq : ab ^ 2 = a * b) :
    a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b = 0 := by
  have hbne : b ≠ 0 := hb.ne'
  have h1 : a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b = (a * b - ab ^ 2) / b := by
    field_simp [hbne]
    ring
  rw [h1, heq, sub_self, zero_div]

private theorem scalar_div_sq_le {a ab b : ℝ}
    (hb : 0 < b) (hcs : ab ^ 2 ≤ a * b) :
    ab ^ 2 / b ≤ a :=
  (div_le_iff₀ hb).mpr hcs

private theorem scalar_inv_le_of_one_sq {a b : ℝ}
    (hb : 0 < b) (hcs : (1 : ℝ) ^ 2 ≤ a * b) :
    1 / b ≤ a := by
  have h := scalar_div_sq_le hb hcs
  rwa [one_pow] at h

private theorem scalar_fenchel_reg_upper {η η0 ψ0 ε s : ℝ} (hε : 0 < ε) :
    (η - η0) * s - ε / 2 * s ^ 2 - ψ0 ≤ -ψ0 + (η - η0) ^ 2 / (2 * ε) := by
  have hεne : ε ≠ 0 := hε.ne'
  have hsq : 0 ≤ ε / 2 * (s - (η - η0) / ε) ^ 2 :=
    mul_nonneg (div_nonneg hε.le (by norm_num)) (sq_nonneg _)
  have hid :
      (-ψ0 + (η - η0) ^ 2 / (2 * ε)) - ((η - η0) * s - ε / 2 * s ^ 2 - ψ0) =
        ε / 2 * (s - (η - η0) / ε) ^ 2 := by
    field_simp [hεne]
    ring
  exact sub_nonneg.mp (hid ▸ hsq)

private theorem scalar_subgradient_convex {ψ_ab ψ_a ψ_b g_ab x y a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : ψ_ab + g_ab * (x - (a * x + b * y)) ≤ ψ_a)
    (hy : ψ_ab + g_ab * (y - (a * x + b * y)) ≤ ψ_b) :
    ψ_ab ≤ a * ψ_a + b * ψ_b := by
  have h1 := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  have hl :
      a * (ψ_ab + g_ab * (x - (a * x + b * y))) +
          b * (ψ_ab + g_ab * (y - (a * x + b * y))) =
        ψ_ab := by
    calc
      a * (ψ_ab + g_ab * (x - (a * x + b * y))) +
          b * (ψ_ab + g_ab * (y - (a * x + b * y)))
          = (a + b) * ψ_ab + g_ab * ((a * x + b * y) - (a + b) * (a * x + b * y)) := by ring
      _ = ψ_ab := by rw [hab]; ring
  exact hl ▸ h1

private theorem scalar_subgradient_strict_convex {ψ_ab ψ_a ψ_b g_ab x y a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : ψ_ab + g_ab * (x - (a * x + b * y)) < ψ_a)
    (hy : ψ_ab + g_ab * (y - (a * x + b * y)) < ψ_b) :
    ψ_ab < a * ψ_a + b * ψ_b := by
  have h1 := add_lt_add (mul_lt_mul_of_pos_left hx ha) (mul_lt_mul_of_pos_left hy hb)
  have hl :
      a * (ψ_ab + g_ab * (x - (a * x + b * y))) +
          b * (ψ_ab + g_ab * (y - (a * x + b * y))) =
        ψ_ab := by
    calc
      a * (ψ_ab + g_ab * (x - (a * x + b * y))) +
          b * (ψ_ab + g_ab * (y - (a * x + b * y)))
          = (a + b) * ψ_ab + g_ab * ((a * x + b * y) - (a + b) * (a * x + b * y)) := by ring
      _ = ψ_ab := by rw [hab]; ring
  exact hl ▸ h1

private theorem scalar_two_mul_add_sq {a ab b t : ℝ} :
    a + 2 * t * ab + t ^ 2 * b = a + t * ab + (t * ab + t ^ 2 * b) := by
  ring

private theorem scalar_quadratic_eval {a ab b : ℝ} (hb : b ≠ 0) :
    a + 2 * (-ab / b) * ab + (-ab / b) ^ 2 * b = (a * b - ab ^ 2) / b := by
  field_simp [hb]
  ring

private theorem scalar_add_neg_add_neg {x y : ℝ} :
    x + -y + (-y + y) = x - y := by
  ring

private theorem scalar_subgradient_left {a b g s t : ℝ} (hts : a - b ≤ g * (t - s)) :
    a + g * (s - t) ≤ b := by
  linarith [hts]

private theorem scalar_sub_sub_nonneg {a b g s t : ℝ} (h : b + g * (s - t) ≤ a) :
    0 ≤ a - b - g * (s - t) := by
  linarith [h]

private theorem scalar_sub_sub_pos {a b g s t : ℝ} (h : b + g * (s - t) < a) :
    0 < a - b - g * (s - t) := by
  linarith [h]

private theorem scalar_fenchel_young_step {a b g s t : ℝ} (h : b + g * (s - t) ≤ a) :
    g * s ≤ a + (g * t - b) := by
  linarith [h]

private theorem scalar_fenchel_reg_upper_step {a b g s c t : ℝ} (h : b + g * s ≤ a) :
    c * s - (a + t * s ^ 2) ≤ (c - g) * s - t * s ^ 2 - b := by
  linarith [h]

private theorem scalar_le_add_of_sub_le {a b c : ℝ} (h : a - b ≤ c) :
    a ≤ b + c := by
  linarith [h]

private theorem scalar_fenchel_dual_bound {a b g s t : ℝ} (h : b + g * (s - t) ≤ a) :
    g * s - a ≤ g * t - b := by
  linarith [h]

/-! ## Section 1: Noncommutative Operator BKM Cauchy–Schwarz & Cramér–Rao -/

section NoncommutativeBKMCramerRao

private theorem expectationReal_add {n : ℕ}
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) :
    expectationReal D (A + B) = expectationReal D A + expectationReal D B := by
  unfold expectationReal
  rw [mul_add]
  exact congrArg Complex.re (map_add (finiteOperatorTraceLinear n) (D.rho * A) (D.rho * B))

private theorem expectationReal_real_smul {n : ℕ}
    (D : FaithfulDensityOperator n) (t : ℝ) (A : FiniteOperatorAlgebra n) :
    expectationReal D ((t : ℂ) • A) = t * expectationReal D A := by
  unfold expectationReal
  rw [mul_smul_comm (t : ℂ) D.rho A,
    show finiteOperatorTrace ((t : ℂ) • (D.rho * A)) =
        (t : ℂ) * finiteOperatorTrace (D.rho * A) from
      (finiteOperatorTraceLinear n).map_smul (t : ℂ) (D.rho * A),
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem centeredStatistic_add {n : ℕ}
    (D : FaithfulDensityOperator n) (A B : FiniteOperatorAlgebra n) :
    centeredStatistic D (A + B) = centeredStatistic D A + centeredStatistic D B := by
  unfold centeredStatistic
  rw [expectationReal_add]
  have hsmul :
      (expectationReal D A + expectationReal D B) • (1 : FiniteOperatorAlgebra n) =
        expectationReal D A • (1 : FiniteOperatorAlgebra n) +
          expectationReal D B • (1 : FiniteOperatorAlgebra n) :=
    add_smul (expectationReal D A) (expectationReal D B) (1 : FiniteOperatorAlgebra n)
  rw [hsmul, add_sub_add_comm]

private theorem centeredStatistic_real_smul {n : ℕ}
    (D : FaithfulDensityOperator n) (t : ℝ) (A : FiniteOperatorAlgebra n) :
    centeredStatistic D ((t : ℂ) • A) = (t : ℂ) • centeredStatistic D A := by
  unfold centeredStatistic
  rw [expectationReal_real_smul]
  rw [← real_smul_eq_complex_smul (n := n) t A,
    ← real_smul_eq_complex_smul (n := n) t (A - expectationReal D A • (1 : FiniteOperatorAlgebra n)),
    smul_sub t A (expectationReal D A • (1 : FiniteOperatorAlgebra n)),
    smul_smul t (expectationReal D A) (1 : FiniteOperatorAlgebra n)]

private theorem centeredStatistic_real_smul' {n : ℕ}
    (D : FaithfulDensityOperator n) (t : ℝ) (A : FiniteOperatorAlgebra n) :
    centeredStatistic D (t • A) = t • centeredStatistic D A := by
  rw [real_smul_eq_complex_smul (n := n) t A,
    real_smul_eq_complex_smul (n := n) t (centeredStatistic D A)]
  exact centeredStatistic_real_smul D t A

theorem centeredStatistic_eq_zero_iff {n : ℕ}
    (D : FaithfulDensityOperator n) (A : FiniteOperatorAlgebra n) :
    centeredStatistic D A = 0 ↔ A = (expectationReal D A : ℂ) • (1 : FiniteOperatorAlgebra n) := by
  unfold centeredStatistic
  rw [sub_eq_zero, real_smul_eq_complex_smul (n := n) (expectationReal D A) 1]

theorem centeredBKMRealCovariance_nonneg {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (A : FiniteOperatorAlgebra n) :
    0 ≤ centeredBKMRealCovariance D hpow A A :=
  D.kuboMoriPairing_self_re_nonneg (centeredStatistic D A) hpow

theorem centeredBKMRealCovariance_pos_iff {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (A : FiniteOperatorAlgebra n) :
    0 < centeredBKMRealCovariance D hpow A A ↔ centeredStatistic D A ≠ 0 :=
  D.bkmRealBilinForm_self_pos_iff hpow (centeredStatistic D A)

theorem centeredBKMRealCovariance_eq_zero_iff {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow) (A : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow A A = 0 ↔ centeredStatistic D A = 0 := by
  constructor
  · intro h0
    by_contra hne
    exact (centeredBKMRealCovariance_pos_iff D hpow A).mpr hne |>.ne' h0
  · intro hz
    change D.bkmRealBilinForm hpow (centeredStatistic D A) (centeredStatistic D A) = 0
    rw [hz, map_zero]

theorem centeredBKMRealCovariance_add_left {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A₁ A₂ B : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow (A₁ + A₂) B =
      centeredBKMRealCovariance D hpow A₁ B + centeredBKMRealCovariance D hpow A₂ B := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_add, map_add, LinearMap.add_apply]

theorem centeredBKMRealCovariance_add_right {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B₁ B₂ : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow A (B₁ + B₂) =
      centeredBKMRealCovariance D hpow A B₁ + centeredBKMRealCovariance D hpow A B₂ := by
  unfold centeredBKMRealCovariance
  rw [centeredStatistic_add, map_add]

theorem centeredBKMRealCovariance_smul_left {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (t : ℝ) (A B : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow ((t : ℂ) • A) B =
      t * centeredBKMRealCovariance D hpow A B := by
  unfold centeredBKMRealCovariance
  rw [← real_smul_eq_complex_smul (n := n) t A, centeredStatistic_real_smul',
    map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem centeredBKMRealCovariance_smul_right {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (t : ℝ) (A B : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow A ((t : ℂ) • B) =
      t * centeredBKMRealCovariance D hpow A B := by
  unfold centeredBKMRealCovariance
  rw [← real_smul_eq_complex_smul (n := n) t B, centeredStatistic_real_smul',
    map_smul, smul_eq_mul]

/-- Exact quadratic expansion of centered BKM variance along `A + t • B`. -/
theorem centeredBKMRealCovariance_add_smul {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) (t : ℝ) :
    centeredBKMRealCovariance D hpow (A + (t : ℂ) • B) (A + (t : ℂ) • B) =
      centeredBKMRealCovariance D hpow A A +
        2 * t * centeredBKMRealCovariance D hpow A B +
        t ^ 2 * centeredBKMRealCovariance D hpow B B := by
  rw [centeredBKMRealCovariance_add_left, centeredBKMRealCovariance_add_right,
    centeredBKMRealCovariance_add_right, centeredBKMRealCovariance_smul_left,
    centeredBKMRealCovariance_smul_right, centeredBKMRealCovariance_smul_right,
    centeredBKMRealCovariance_smul_left, centeredBKMRealCovariance_symm D hpow B A]
  ring

/-- **Noncommutative BKM Cauchy–Schwarz Inequality**:
`Cov_BKM(A, B)^2 ≤ Cov_BKM(A, A) * Cov_BKM(B, B)`. -/
theorem centeredBKMRealCovariance_sq_le {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) :
    (centeredBKMRealCovariance D hpow A B) ^ 2 ≤
      centeredBKMRealCovariance D hpow A A * centeredBKMRealCovariance D hpow B B := by
  by_cases hBz : centeredStatistic D B = 0
  · have hB0 : centeredBKMRealCovariance D hpow B B = 0 :=
      (centeredBKMRealCovariance_eq_zero_iff D hpow B).mpr hBz
    have hAB0 : centeredBKMRealCovariance D hpow A B = 0 := by
      change D.bkmRealBilinForm hpow (centeredStatistic D A) (centeredStatistic D B) = 0
      rw [hBz, map_zero]
    rw [hB0, hAB0, mul_zero, sq, mul_zero]
  · have hBpos : 0 < centeredBKMRealCovariance D hpow B B :=
      (centeredBKMRealCovariance_pos_iff D hpow B).mpr hBz
    let t : ℝ := -(centeredBKMRealCovariance D hpow A B) / centeredBKMRealCovariance D hpow B B
    have hmin := centeredBKMRealCovariance_nonneg D hpow (A + (t : ℂ) • B)
    rw [centeredBKMRealCovariance_add_smul] at hmin
    exact scalar_quadratic_nonneg_bound hBpos hmin

/-- **Exact Saturation Characterization of Noncommutative BKM Cauchy–Schwarz**:
when `Cov_BKM(B, B) > 0`, equality holds iff `A° = (Cov_BKM(A, B) / Cov_BKM(B, B)) • B°`. -/
theorem centeredBKMRealCovariance_sq_eq_iff {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) (hBpos : 0 < centeredBKMRealCovariance D hpow B B) :
    (centeredBKMRealCovariance D hpow A B) ^ 2 =
        centeredBKMRealCovariance D hpow A A * centeredBKMRealCovariance D hpow B B ↔
      centeredStatistic D A =
        ((centeredBKMRealCovariance D hpow A B / centeredBKMRealCovariance D hpow B B : ℝ) : ℂ) •
          centeredStatistic D B := by
  let c : ℝ := centeredBKMRealCovariance D hpow A B / centeredBKMRealCovariance D hpow B B
  let t : ℝ := -centeredBKMRealCovariance D hpow A B / centeredBKMRealCovariance D hpow B B
  have hneg : (-c : ℂ) = (t : ℂ) := by
    dsimp [c, t]
    push_cast
    rw [neg_div]
  constructor
  · intro heq
    have hquad : centeredBKMRealCovariance D hpow (A + (t : ℂ) • B) (A + (t : ℂ) • B) = 0 := by
      rw [centeredBKMRealCovariance_add_smul]
      exact scalar_quadratic_zero_of_eq hBpos heq
    have hz := (centeredBKMRealCovariance_eq_zero_iff D hpow (A + (t : ℂ) • B)).mp hquad
    rw [centeredStatistic_add, centeredStatistic_real_smul, ← hneg,
      neg_smul (c : ℂ) (centeredStatistic D B), ← sub_eq_add_neg] at hz
    exact sub_eq_zero.mp hz
  · intro hs
    have hz : centeredStatistic D (A + (t : ℂ) • B) = 0 := by
      rw [centeredStatistic_add, centeredStatistic_real_smul, ← hneg, hs,
        neg_smul (c : ℂ) (centeredStatistic D B), add_neg_cancel]
    have hquad : centeredBKMRealCovariance D hpow (A + (t : ℂ) • B) (A + (t : ℂ) • B) = 0 :=
      (centeredBKMRealCovariance_eq_zero_iff D hpow _).mpr hz
    rw [centeredBKMRealCovariance_add_smul] at hquad
    have heval :
        centeredBKMRealCovariance D hpow A A +
            2 * t * centeredBKMRealCovariance D hpow A B +
            t ^ 2 * centeredBKMRealCovariance D hpow B B =
          (centeredBKMRealCovariance D hpow A A * centeredBKMRealCovariance D hpow B B -
            (centeredBKMRealCovariance D hpow A B) ^ 2) / centeredBKMRealCovariance D hpow B B := by
      dsimp [t]
      exact scalar_quadratic_eval hBpos.ne'
    have hzero :
        (centeredBKMRealCovariance D hpow A A * centeredBKMRealCovariance D hpow B B -
          (centeredBKMRealCovariance D hpow A B) ^ 2) / centeredBKMRealCovariance D hpow B B = 0 :=
      heval.symm.trans hquad
    have hnum := (div_eq_zero_iff.mp hzero).resolve_right hBpos.ne'
    exact (sub_eq_zero.mp hnum).symm

/-- **Noncommutative BKM Cramér–Rao Inequality (General Covariance Form)**:
`(Cov_BKM(A, B))^2 / Cov_BKM(B, B) ≤ Cov_BKM(A, A)` for `Cov_BKM(B, B) > 0`. -/
theorem bkm_cramer_rao_bound {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n) (hBpos : 0 < centeredBKMRealCovariance D hpow B B) :
    (centeredBKMRealCovariance D hpow A B) ^ 2 / centeredBKMRealCovariance D hpow B B ≤
      centeredBKMRealCovariance D hpow A A :=
  scalar_div_sq_le hBpos (centeredBKMRealCovariance_sq_le D hpow A B)

/-- **Unbiased Noncommutative BKM Cramér–Rao Inequality**:
under unit local sensitivity `Cov_BKM(A, B) = 1`,
`1 / Cov_BKM(B, B) ≤ Cov_BKM(A, A)`. -/
theorem bkm_cramer_rao_unbiased {n : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (A B : FiniteOperatorAlgebra n)
    (hunit : centeredBKMRealCovariance D hpow A B = 1)
    (hBpos : 0 < centeredBKMRealCovariance D hpow B B) :
    1 / centeredBKMRealCovariance D hpow B B ≤ centeredBKMRealCovariance D hpow A A :=
  scalar_inv_le_of_one_sq hBpos (by
    rw [← hunit]
    exact centeredBKMRealCovariance_sq_le D hpow A B)

/-- **Unconditional Gibbs Hessian Cramér–Rao Inequality**:
expresses the Fisher lower bound directly in terms of the actual mixed second Fréchet
derivative `secondFDerivLogPartitionReadout` of `log Tr(exp(H))`. -/
theorem gibbs_bkm_cramer_rao {n : ℕ} [Nonempty (Fin n)]
    (H A B : FiniteOperatorAlgebra n)
    (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B)
    (hI : 0 < (secondFDerivLogPartitionReadout H B B).re) :
    ((secondFDerivLogPartitionReadout H B A).re) ^ 2 /
        (secondFDerivLogPartitionReadout H B B).re ≤
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH (tracedExponential_re_pos_of_isSelfAdjoint H hH))
        (continuous_faithfulGibbsDensity_rpow H hH (tracedExponential_re_pos_of_isSelfAdjoint H hH))
        A A := by
  have hZ := tracedExponential_re_pos_of_isSelfAdjoint H hH
  let D := faithfulGibbsDensity H hH hZ
  let hpow := continuous_faithfulGibbsDensity_rpow H hH hZ
  have hBA := secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ B A hB
  have hBB := secondFDeriv_logPartition_apply_eq_centeredBKM H hH hZ B B hB
  rw [hBA, hBB, centeredBKMRealCovariance_symm D hpow B A]
  rw [hBB] at hI
  exact bkm_cramer_rao_bound D hpow A B hI

/-- Unbiased Gibbs Hessian Cramér–Rao bound under unit Fréchet mixed response. -/
theorem gibbs_bkm_cramer_rao_unbiased {n : ℕ} [Nonempty (Fin n)]
    (H A B : FiniteOperatorAlgebra n)
    (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B)
    (hunit : (secondFDerivLogPartitionReadout H B A).re = 1)
    (hI : 0 < (secondFDerivLogPartitionReadout H B B).re) :
    1 / (secondFDerivLogPartitionReadout H B B).re ≤
      centeredBKMRealCovariance
        (faithfulGibbsDensity H hH (tracedExponential_re_pos_of_isSelfAdjoint H hH))
        (continuous_faithfulGibbsDensity_rpow H hH (tracedExponential_re_pos_of_isSelfAdjoint H hH))
        A A := by
  have hcr := gibbs_bkm_cramer_rao H A B hH hB hI
  rwa [hunit, one_pow] at hcr

end NoncommutativeBKMCramerRao

/-! ## Section 2: Multivariate Matrix Cramér–Rao Inequality in the Loewner Order -/

section MultivariateMatrixCramerRao

/-- Centered BKM covariance matrix `Σ_{i j} = Cov_BKM(A_i, A_j)`. -/
def bkmCovMatrix {n p : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => centeredBKMRealCovariance D hpow (As i) (As j)

/-- Centered BKM cross-sensitivity matrix `J_{i a} = Cov_BKM(A_i, B_a)`. -/
def bkmCrossMatrix {n p q : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) (Bs : Fin q → FiniteOperatorAlgebra n) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i a => centeredBKMRealCovariance D hpow (As i) (Bs a)

theorem bkmCovMatrix_isHermitian {n p : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) :
    (bkmCovMatrix D hpow As).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, bkmCovMatrix]
  exact centeredBKMRealCovariance_symm D hpow (As j) (As i)

private theorem centeredBKMRealCovariance_sum_left {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (f : Fin m → FiniteOperatorAlgebra n) (Y : FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow (∑ i : Fin m, f i) Y =
      ∑ i : Fin m, centeredBKMRealCovariance D hpow (f i) Y := by
  unfold centeredBKMRealCovariance
  have hstat : centeredStatistic D (∑ i : Fin m, f i) = ∑ i : Fin m, centeredStatistic D (f i) := by
    induction m with
    | zero =>
        rw [Fin.sum_univ_zero, Fin.sum_univ_zero]
        have h0 : centeredStatistic D 0 = centeredStatistic D 0 + centeredStatistic D 0 := by
          have hadd := centeredStatistic_add D 0 0
          rwa [add_zero] at hadd
        have h1 := congrArg (fun x => x - centeredStatistic D 0) h0
        simpa only [sub_self, add_sub_cancel_right] using h1.symm
    | succ k ih =>
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, centeredStatistic_add]
        congr 1
        exact ih (fun i => f i.succ)
  rw [hstat]
  clear hstat
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, map_add, LinearMap.add_apply]
      congr 1
      exact ih (fun i => f i.succ)

private theorem centeredBKMRealCovariance_sum_right {n m : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (X : FiniteOperatorAlgebra n) (g : Fin m → FiniteOperatorAlgebra n) :
    centeredBKMRealCovariance D hpow X (∑ j : Fin m, g j) =
      ∑ j : Fin m, centeredBKMRealCovariance D hpow X (g j) := by
  rw [centeredBKMRealCovariance_symm]
  rw [centeredBKMRealCovariance_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact centeredBKMRealCovariance_symm D hpow (g j) X

theorem dotProduct_bkmCovMatrix_eq {n p : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) (v : Fin p → ℝ) :
    v ⬝ᵥ (bkmCovMatrix D hpow As *ᵥ v) =
      centeredBKMRealCovariance D hpow
        (∑ i : Fin p, (v i : ℂ) • As i) (∑ j : Fin p, (v j : ℂ) • As j) := by
  rw [centeredBKMRealCovariance_sum_left]
  simp only [centeredBKMRealCovariance_sum_right, centeredBKMRealCovariance_smul_left,
    centeredBKMRealCovariance_smul_right]
  unfold dotProduct Matrix.mulVec bkmCovMatrix
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dotProduct_bkmCrossMatrix_eq {n p q : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) (Bs : Fin q → FiniteOperatorAlgebra n)
    (v : Fin p → ℝ) (w : Fin q → ℝ) :
    v ⬝ᵥ (bkmCrossMatrix D hpow As Bs *ᵥ w) =
      centeredBKMRealCovariance D hpow
        (∑ i : Fin p, (v i : ℂ) • As i) (∑ a : Fin q, (w a : ℂ) • Bs a) := by
  rw [centeredBKMRealCovariance_sum_left]
  simp only [centeredBKMRealCovariance_sum_right, centeredBKMRealCovariance_smul_left,
    centeredBKMRealCovariance_smul_right]
  unfold dotProduct Matrix.mulVec bkmCrossMatrix
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem bkmCovMatrix_posSemidef {n p : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) :
    (bkmCovMatrix D hpow As).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bkmCovMatrix_isHermitian D hpow As) ?_
  intro v
  simp only [star_trivial]
  rw [dotProduct_bkmCovMatrix_eq]
  exact centeredBKMRealCovariance_nonneg D hpow _

/-- **Multivariate Noncommutative Matrix Cramér–Rao Inequality**:
for arbitrary observable estimators `As : Fin p → FiniteOperatorAlgebra n` and
score perturbations `Bs : Fin q → FiniteOperatorAlgebra n` with positive-definite
information matrix `I = bkmCovMatrix D hpow Bs`,
`bkmCovMatrix D hpow As ≥ J * I⁻¹ * Jᵀ` in the Loewner semidefinite order. -/
theorem multivariate_bkm_cramer_rao_posSemidef {n p q : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As : Fin p → FiniteOperatorAlgebra n) (Bs : Fin q → FiniteOperatorAlgebra n)
    (hI : (bkmCovMatrix D hpow Bs).PosDef) :
    (bkmCovMatrix D hpow As -
      bkmCrossMatrix D hpow As Bs * (bkmCovMatrix D hpow Bs)⁻¹ *
        (bkmCrossMatrix D hpow As Bs)ᵀ).PosSemidef := by
  set covMat := bkmCovMatrix D hpow As
  set I := bkmCovMatrix D hpow Bs
  set J := bkmCrossMatrix D hpow As Bs
  have hIherm : I.IsHermitian := bkmCovMatrix_isHermitian D hpow Bs
  have hIT : Iᵀ = I := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hIherm.eq
  have hIinv_herm : I⁻¹.IsHermitian := hI.inv.isHermitian
  have hIinvT : I⁻¹ᵀ = I⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hIinv_herm.eq
  have hJ_herm : (J * I⁻¹ * Jᵀ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hIinvT,
      Matrix.mul_assoc]
  have hdiff_herm : (covMat - J * I⁻¹ * Jᵀ).IsHermitian :=
    (bkmCovMatrix_isHermitian D hpow As).sub hJ_herm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hdiff_herm ?_
  intro v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  set u : Fin q → ℝ := Jᵀ *ᵥ v
  set w : Fin q → ℝ := -(I⁻¹ *ᵥ u)
  let Z : FiniteOperatorAlgebra n :=
    (∑ i : Fin p, (v i : ℂ) • As i) + (∑ a : Fin q, (w a : ℂ) • Bs a)
  have hZnn : 0 ≤ centeredBKMRealCovariance D hpow Z Z :=
    centeredBKMRealCovariance_nonneg D hpow Z
  have hIu : I *ᵥ (I⁻¹ *ᵥ u) = u := by
    have hIdet : IsUnit I.det := isUnit_iff_ne_zero.mpr hI.det_pos.ne'
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv I hIdet, Matrix.one_mulVec]
  have hwIw : w ⬝ᵥ (I *ᵥ w) = u ⬝ᵥ (I⁻¹ *ᵥ u) := by
    dsimp [w]
    rw [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg, hIu, dotProduct_comm]
  have hvJw : v ⬝ᵥ (J *ᵥ w) = -(u ⬝ᵥ (I⁻¹ *ᵥ u)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    change (Jᵀ *ᵥ v) ⬝ᵥ w = _
    dsimp [u, w]
    rw [dotProduct_neg]
  have hZeq :
      centeredBKMRealCovariance D hpow Z Z =
        v ⬝ᵥ (covMat *ᵥ v) - v ⬝ᵥ ((J * I⁻¹ * Jᵀ) *ᵥ v) := by
    dsimp [Z]
    rw [centeredBKMRealCovariance_add_left, centeredBKMRealCovariance_add_right,
      centeredBKMRealCovariance_add_right, centeredBKMRealCovariance_symm D hpow
        (∑ a, (w a : ℂ) • Bs a) (∑ i, (v i : ℂ) • As i)]
    rw [← dotProduct_bkmCovMatrix_eq, ← dotProduct_bkmCrossMatrix_eq,
      ← dotProduct_bkmCovMatrix_eq, hvJw, hwIw]
    have hQuad : v ⬝ᵥ ((J * I⁻¹ * Jᵀ) *ᵥ v) = u ⬝ᵥ (I⁻¹ *ᵥ u) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec v J (I⁻¹ * Jᵀ),
        ← Matrix.mulVec_mulVec v I⁻¹ Jᵀ, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [hQuad]
    exact scalar_add_neg_add_neg
  exact hZeq ▸ hZnn

/-- **Multivariate Unbiased BKM Cramér–Rao Inequality**:
for an unbiased vector estimator (`J = 1`), `Σ ≥ I⁻¹` in the Loewner order. -/
theorem multivariate_bkm_cramer_rao_unbiased {n p : ℕ}
    (D : FaithfulDensityOperator n) (hpow : Continuous D.rpow)
    (As Bs : Fin p → FiniteOperatorAlgebra n)
    (hI : (bkmCovMatrix D hpow Bs).PosDef)
    (hunbiased : bkmCrossMatrix D hpow As Bs = 1) :
    (bkmCovMatrix D hpow As - (bkmCovMatrix D hpow Bs)⁻¹).PosSemidef := by
  have h := multivariate_bkm_cramer_rao_posSemidef D hpow As Bs hI
  rwa [hunbiased, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at h

end MultivariateMatrixCramerRao

/-! ## Section 3: Koszul–Souriau–Barbaresco Real Gibbs Slice Convexity & Strict Convexity -/

section KoszulSouriauConvexity

/-- Moment slice (first derivative of `realLogPartitionLine H A`) at `t : ℝ`. -/
def gibbsMomentSlice {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (t : ℝ) : ℝ :=
  realOperatorExpectation (H + (t : ℂ) • A) A

theorem isSelfAdjoint_shift {n : ℕ}
    {H A : FiniteOperatorAlgebra n} (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) (t : ℝ) :
    IsSelfAdjoint (H + (t : ℂ) • A) := by
  change star (H + (t : ℂ) • A) = H + (t : ℂ) • A
  rw [star_add H ((t : ℂ) • A), star_smul (t : ℂ) A, Complex.star_def, Complex.conj_ofReal,
    hH.star_eq, hA.star_eq]

private theorem shift_add_sub {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (t x : ℝ) :
    H + (t : ℂ) • A + ((x - t : ℝ) : ℂ) • A = H + (x : ℂ) • A := by
  push_cast
  rw [sub_smul (x : ℂ) (t : ℂ) A]
  abel

private theorem realLogPartitionLine_shift {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (t : ℝ) :
    (fun x : ℝ => realLogPartitionLine (H + (t : ℂ) • A) A (x - t)) =
      realLogPartitionLine H A := by
  funext x
  dsimp [realLogPartitionLine, logPartitionLine, partitionLine]
  rw [shift_add_sub H A t x]

private theorem gradientLine_re_eq_gibbsMomentSlice {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (t x : ℝ) :
    (logPartitionGradientLine (H + (t : ℂ) • A) A A ((x - t : ℝ) : ℂ)).re =
      gibbsMomentSlice H A x := by
  unfold logPartitionGradientLine normalizedTwoPointLine gibbsMomentSlice realOperatorExpectation
  rw [shift_add_sub H A t x]
  congr 1
  exact (operatorExpectation_eq_trace_div (H + (x : ℂ) • A) A).symm

/-- First derivative everywhere along a self-adjoint thermodynamic line:
`d/dt ψ(H + t A) = E_{H + t A}[A]`. -/
theorem hasDerivAt_realLogPartitionLine_at {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) (t : ℝ) :
    HasDerivAt (realLogPartitionLine H A) (gibbsMomentSlice H A t) t := by
  have hbase := hasDerivAt_realLogPartitionLine_eq_expectation
    (H + (t : ℂ) • A) A (isSelfAdjoint_shift hH hA t)
  have hbase' :
      HasDerivAt (realLogPartitionLine (H + (t : ℂ) • A) A)
        (realOperatorExpectation (H + (t : ℂ) • A) A) (t - t) := by
    simpa only [sub_self] using hbase
  have hsub : HasDerivAt (fun x : ℝ => x - t) 1 t := (hasDerivAt_id t).sub_const t
  have hcomp := HasDerivAt.comp (h := fun x : ℝ => x - t) t hbase' hsub
  change HasDerivAt (fun x : ℝ => realLogPartitionLine (H + (t : ℂ) • A) A (x - t)) _ t at hcomp
  simpa only [mul_one, realLogPartitionLine_shift, gibbsMomentSlice] using hcomp

/-- Second derivative everywhere along a self-adjoint thermodynamic line:
`d/dt E_{H + t A}[A] = Cov_BKM^{H + t A}(A, A) ≥ 0`. -/
theorem hasDerivAt_gibbsMomentSlice_at {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) (t : ℝ) :
    HasDerivAt (gibbsMomentSlice H A)
      (centeredBKMRealCovariance
        (faithfulGibbsDensity (H + (t : ℂ) • A) (isSelfAdjoint_shift hH hA t)
          (tracedExponential_re_pos_of_isSelfAdjoint _ (isSelfAdjoint_shift hH hA t)))
        (continuous_faithfulGibbsDensity_rpow (H + (t : ℂ) • A) (isSelfAdjoint_shift hH hA t)
          (tracedExponential_re_pos_of_isSelfAdjoint _ (isSelfAdjoint_shift hH hA t)))
        A A) t := by
  have hHt := isSelfAdjoint_shift hH hA t
  have hZt := tracedExponential_re_pos_of_isSelfAdjoint (H + (t : ℂ) • A) hHt
  have hZc : tracedExponential (H + (t : ℂ) • A) ≠ 0 := by
    rw [tracedExponential_eq_gibbsPartitionReal _ hHt]
    exact_mod_cast hZt.ne'
  have hcomplex := hasDerivAt_logPartitionGradientLine (H + (t : ℂ) • A) A A hZc
  have hreal :
      HasDerivAt (fun s : ℝ => (logPartitionGradientLine (H + (t : ℂ) • A) A A (s : ℂ)).re)
        (complexGibbsHessianResponse (H + (t : ℂ) • A) A A).re (t - t) := by
    simpa only [sub_self] using hcomplex.real_of_complex
  have hsub : HasDerivAt (fun x : ℝ => x - t) 1 t := (hasDerivAt_id t).sub_const t
  have hcomp := HasDerivAt.comp (h := fun x : ℝ => x - t) t hreal hsub
  change HasDerivAt
    (fun x : ℝ => (logPartitionGradientLine (H + (t : ℂ) • A) A A ((x - t : ℝ) : ℂ)).re)
    _ t at hcomp
  have hfn :
      (fun x : ℝ => (logPartitionGradientLine (H + (t : ℂ) • A) A A ((x - t : ℝ) : ℂ)).re) =
        gibbsMomentSlice H A :=
    funext fun x => gradientLine_re_eq_gibbsMomentSlice H A t x
  rw [mul_one, hfn,
    complexGibbsHessianResponse_re_eq_centeredFrechetResponse _ hHt hZt A A hA,
    centeredFrechetResponse_eq_centeredBKMRealCovariance _ hHt hZt A A hA] at hcomp
  exact hcomp

/-- Monotonicity of the Gibbs moment map along every self-adjoint direction. -/
theorem monotone_gibbsMomentSlice {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) :
    Monotone (gibbsMomentSlice H A) := by
  refine monotone_of_deriv_nonneg
    (fun t => (hasDerivAt_gibbsMomentSlice_at H A hH hA t).differentiableAt) ?_
  intro t
  rw [(hasDerivAt_gibbsMomentSlice_at H A hH hA t).deriv]
  exact centeredBKMRealCovariance_nonneg _ _ A

/-- Strict monotonicity of the Gibbs moment map along every non-scalar direction. -/
theorem strictMono_gibbsMomentSlice {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (hAnons : ∀ c : ℝ, A ≠ (c : ℂ) • (1 : FiniteOperatorAlgebra n)) :
    StrictMono (gibbsMomentSlice H A) := by
  refine strictMono_of_deriv_pos ?_
  intro t
  rw [(hasDerivAt_gibbsMomentSlice_at H A hH hA t).deriv]
  rw [centeredBKMRealCovariance_pos_iff, ne_eq, centeredStatistic_eq_zero_iff]
  exact hAnons _

/-- Exact global first-order convexity subgradient inequality for the log-partition slice:
`ψ(t) + ψ'(t) (s - t) ≤ ψ(s)`. -/
theorem gibbsLogPartitionSlice_subgradient {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (s t : ℝ) :
    realLogPartitionLine H A t + gibbsMomentSlice H A t * (s - t) ≤
      realLogPartitionLine H A s := by
  have hdiff : ∀ x : ℝ, HasDerivAt (realLogPartitionLine H A) (gibbsMomentSlice H A x) x :=
    fun x => hasDerivAt_realLogPartitionLine_at H A hH hA x
  have hmono := monotone_gibbsMomentSlice H A hH hA
  rcases lt_trichotomy t s with hts | rfl | hst
  · obtain ⟨c, hcIoo, hc⟩ := exists_hasDerivAt_eq_slope (realLogPartitionLine H A)
      (gibbsMomentSlice H A) hts
      (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
      (fun x _ => hdiff x)
    have hmc : gibbsMomentSlice H A t ≤ gibbsMomentSlice H A c := hmono hcIoo.1.le
    have hslope :
        (realLogPartitionLine H A s - realLogPartitionLine H A t) / (s - t) =
          gibbsMomentSlice H A c := hc.symm
    have hst_pos : 0 < s - t := sub_pos.mpr hts
    have h1 : gibbsMomentSlice H A t * (s - t) ≤
        realLogPartitionLine H A s - realLogPartitionLine H A t := by
      rw [← hslope] at hmc
      exact (le_div_iff₀ hst_pos).mp hmc
    exact add_le_of_le_sub_left h1
  · simp
  · obtain ⟨c, hcIoo, hc⟩ := exists_hasDerivAt_eq_slope (realLogPartitionLine H A)
      (gibbsMomentSlice H A) hst
      (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
      (fun x _ => hdiff x)
    have hmc : gibbsMomentSlice H A c ≤ gibbsMomentSlice H A t := hmono hcIoo.2.le
    have hslope :
        (realLogPartitionLine H A t - realLogPartitionLine H A s) / (t - s) =
          gibbsMomentSlice H A c := hc.symm
    have hts_pos : 0 < t - s := sub_pos.mpr hst
    have h1 : realLogPartitionLine H A t - realLogPartitionLine H A s ≤
        gibbsMomentSlice H A t * (t - s) := by
      rw [← hslope] at hmc
      exact (div_le_iff₀ hts_pos).mp hmc
    exact scalar_subgradient_left h1

/-- Strict subgradient inequality along any non-scalar self-adjoint direction for `s ≠ t`. -/
theorem gibbsLogPartitionSlice_strict_subgradient {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (hAnons : ∀ c : ℝ, A ≠ (c : ℂ) • (1 : FiniteOperatorAlgebra n))
    {s t : ℝ} (hne : s ≠ t) :
    realLogPartitionLine H A t + gibbsMomentSlice H A t * (s - t) <
      realLogPartitionLine H A s := by
  have hdiff : ∀ x : ℝ, HasDerivAt (realLogPartitionLine H A) (gibbsMomentSlice H A x) x :=
    fun x => hasDerivAt_realLogPartitionLine_at H A hH hA x
  have hsmono := strictMono_gibbsMomentSlice H A hH hA hAnons
  rcases hne.lt_or_gt with hst | hts
  · obtain ⟨c, hcIoo, hc⟩ := exists_hasDerivAt_eq_slope (realLogPartitionLine H A)
      (gibbsMomentSlice H A) hst
      (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
      (fun x _ => hdiff x)
    have hmc : gibbsMomentSlice H A c < gibbsMomentSlice H A t := hsmono hcIoo.2
    have hslope :
        (realLogPartitionLine H A t - realLogPartitionLine H A s) / (t - s) =
          gibbsMomentSlice H A c := hc.symm
    have hts_pos : 0 < t - s := sub_pos.mpr hst
    have h1 : realLogPartitionLine H A t - realLogPartitionLine H A s <
        gibbsMomentSlice H A t * (t - s) := by
      rw [← hslope] at hmc
      exact (div_lt_iff₀ hts_pos).mp hmc
    have heq : gibbsMomentSlice H A t * (s - t) = -(gibbsMomentSlice H A t * (t - s)) := by
      ring
    rw [heq]
    have h2 : realLogPartitionLine H A t <
        gibbsMomentSlice H A t * (t - s) + realLogPartitionLine H A s :=
      sub_lt_iff_lt_add.mp h1
    exact sub_lt_iff_lt_add.mpr (by rw [add_comm] at h2; exact h2)
  · obtain ⟨c, hcIoo, hc⟩ := exists_hasDerivAt_eq_slope (realLogPartitionLine H A)
      (gibbsMomentSlice H A) hts
      (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
      (fun x _ => hdiff x)
    have hmc : gibbsMomentSlice H A t < gibbsMomentSlice H A c := hsmono hcIoo.1
    have hslope :
        (realLogPartitionLine H A s - realLogPartitionLine H A t) / (s - t) =
          gibbsMomentSlice H A c := hc.symm
    have hst_pos : 0 < s - t := sub_pos.mpr hts
    have h1 : gibbsMomentSlice H A t * (s - t) <
        realLogPartitionLine H A s - realLogPartitionLine H A t := by
      rw [← hslope] at hmc
      exact (lt_div_iff₀ hst_pos).mp hmc
    exact add_lt_of_lt_sub_left h1

/-- **Global Koszul–Souriau Convexity**: `t ↦ log Tr(exp(H + t A))` is convex on `ℝ`. -/
theorem convexOn_realLogPartitionLine {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) :
    ConvexOn ℝ Set.univ (realLogPartitionLine H A) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  exact scalar_subgradient_convex ha hb hab
    (gibbsLogPartitionSlice_subgradient H A hH hA x (a * x + b * y))
    (gibbsLogPartitionSlice_subgradient H A hH hA y (a * x + b * y))

/-- **Global Strict Convexity** along every non-scalar self-adjoint direction. -/
theorem strictConvexOn_realLogPartitionLine {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (hAnons : ∀ c : ℝ, A ≠ (c : ℂ) • (1 : FiniteOperatorAlgebra n)) :
    StrictConvexOn ℝ Set.univ (realLogPartitionLine H A) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hne1 : x ≠ a * x + b * y := by
    intro heq
    have h0 : b * (x - y) = 0 := by
      calc
        b * (x - y) = (1 - a) * x - b * y := by rw [← hab]; ring
        _ = x - (a * x + b * y) := by ring
        _ = 0 := sub_eq_zero.mpr heq
    rcases mul_eq_zero.mp h0 with hb0 | hxy0
    · exact hb.ne' hb0
    · exact hxy (sub_eq_zero.mp hxy0)
  have hne2 : y ≠ a * x + b * y := by
    intro heq
    have h0 : a * (y - x) = 0 := by
      calc
        a * (y - x) = (1 - b) * y - a * x := by rw [← hab]; ring
        _ = y - (a * x + b * y) := by ring
        _ = 0 := sub_eq_zero.mpr heq
    rcases mul_eq_zero.mp h0 with ha0 | hyx0
    · exact ha.ne' ha0
    · exact hxy (sub_eq_zero.mp hyx0).symm
  exact scalar_subgradient_strict_convex ha hb hab
    (gibbsLogPartitionSlice_strict_subgradient H A hH hA hAnons hne1)
    (gibbsLogPartitionSlice_strict_subgradient H A hH hA hAnons hne2)

end KoszulSouriauConvexity

/-! ## Section 4: Fenchel–Legendre Duality & `SL2 ℝ` Projective Contragredient Soldering -/

section LegendreProjectiveSoldering

/-- Fenchel–Legendre conjugate of the Gibbs log-partition slice:
`ψ*(η) = sup_{s ∈ ℝ} (η s - ψ(s))`. -/
def gibbsFenchelDual {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (η : ℝ) : ℝ :=
  sSup (Set.range fun s : ℝ => η * s - realLogPartitionLine H A s)

/-- **Exact Legendre Contact Identity on the Moment Map**:
at `η = gibbsMomentSlice H A t`, the supremum is attained at `t`:
`ψ*(η) = η * t - ψ(t)`. -/
theorem gibbsFenchelDual_at_moment {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) (t : ℝ) :
    gibbsFenchelDual H A (gibbsMomentSlice H A t) =
      gibbsMomentSlice H A t * t - realLogPartitionLine H A t := by
  unfold gibbsFenchelDual
  apply IsGreatest.csSup_eq
  refine ⟨⟨t, rfl⟩, ?_⟩
  rintro y ⟨s, rfl⟩
  exact scalar_fenchel_dual_bound (gibbsLogPartitionSlice_subgradient H A hH hA s t)

/-- Fenchel–Young inequality at every moment parameter `t : ℝ`. -/
theorem gibbs_fenchel_young_at_moment {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (s t : ℝ) :
    gibbsMomentSlice H A t * s ≤
      realLogPartitionLine H A s + gibbsFenchelDual H A (gibbsMomentSlice H A t) := by
  rw [gibbsFenchelDual_at_moment H A hH hA t]
  exact scalar_fenchel_young_step (gibbsLogPartitionSlice_subgradient H A hH hA s t)

/-- **Gibbs–Barbaresco Projective Pairing Identity**:
`ψ(t) + ψ*(∇ψ(t)) = pairing (dualLine (∇ψ(t))) (primalPoint t)`. -/
theorem gibbs_legendre_contact_eq_projective_pairing {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A) (t : ℝ) :
    realLogPartitionLine H A t + gibbsFenchelDual H A (gibbsMomentSlice H A t) =
      InfoGeometry.Projective.MobiusDual.pairing
        (dualLine (gibbsMomentSlice H A t)) (primalPoint t) := by
  rw [gibbsFenchelDual_at_moment H A hH hA t, pairing_dualLine_primalPoint]
  ring

/-- **`SL2 ℝ` Projective Contragredient Invariance of the Gibbs Legendre Contact Term**:
coinciding `actLine M (dualLine (∇ψ t))` and `actPoint M (primalPoint t)` preserves
`ψ(t) + ψ*(∇ψ(t))` identically for all `M : SL2 ℝ`. -/
theorem gibbs_legendre_contact_contragredient_invariant {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (M : SL2 ℝ) (t : ℝ) :
    InfoGeometry.Projective.MobiusDual.pairing
        (actLine M (dualLine (gibbsMomentSlice H A t)))
        (actPoint M (primalPoint t)) =
      realLogPartitionLine H A t + gibbsFenchelDual H A (gibbsMomentSlice H A t) := by
  rw [contragredient_pairing_invariant]
  exact (gibbs_legendre_contact_eq_projective_pairing H A hH hA t).symm

/-- **Gibbs Bregman = Fenchel–Young Loss = Projective Fenchel Gap**:
welds the real Gibbs slice Bregman divergence to `ProjectiveFenchelLegendreBridge.projectiveFenchelGap`. -/
theorem gibbs_bregman_eq_fenchel_young_loss {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (s t : ℝ) :
    bregman_divergence (realLogPartitionLine H A) (gibbsMomentSlice H A) s t =
      realLogPartitionLine H A s + gibbsFenchelDual H A (gibbsMomentSlice H A t) -
        gibbsMomentSlice H A t * s := by
  dsimp [bregman_divergence, InnerSpace.inner]
  rw [gibbsFenchelDual_at_moment H A hH hA t]
  ring

theorem gibbs_bregman_nonneg {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (s t : ℝ) :
    0 ≤ bregman_divergence (realLogPartitionLine H A) (gibbsMomentSlice H A) s t := by
  dsimp [bregman_divergence, InnerSpace.inner]
  exact scalar_sub_sub_nonneg (gibbsLogPartitionSlice_subgradient H A hH hA s t)

theorem gibbs_bregman_pos_of_nonscalar {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (hAnons : ∀ c : ℝ, A ≠ (c : ℂ) • (1 : FiniteOperatorAlgebra n))
    {s t : ℝ} (hne : s ≠ t) :
    0 < bregman_divergence (realLogPartitionLine H A) (gibbsMomentSlice H A) s t := by
  dsimp [bregman_divergence, InnerSpace.inner]
  exact scalar_sub_sub_pos (gibbsLogPartitionSlice_strict_subgradient H A hH hA hAnons hne)

theorem gibbs_bregman_eq_projectiveFenchelGap {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    (s t : ℝ) :
    bregman_divergence (realLogPartitionLine H A) (gibbsMomentSlice H A) s t =
      projectiveFenchelGap
        (fun θ => realLogPartitionLine H A (θ 0 0))
        (fun η => gibbsFenchelDual H A (η 0 0))
        (dualLine (gibbsMomentSlice H A t)) (primalPoint s) := by
  rw [gibbs_bregman_eq_fenchel_young_loss H A hH hA s t]
  unfold projectiveFenchelGap
  rw [pairing_dualLine_primalPoint]
  rfl

/-- Quadratically regularized Gibbs log-partition potential (`ε > 0`), guaranteeing a globally
finite Fenchel conjugate for ALL `η ∈ ℝ`. -/
def regGibbsPotential {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (ε t : ℝ) : ℝ :=
  realLogPartitionLine H A t + (ε / 2) * t ^ 2

/-- Gradient of the regularized Gibbs potential: `∇ψ_ε(t) = E_{H + t A}[A] + ε t`. -/
def regGibbsGrad {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (ε t : ℝ) : ℝ :=
  gibbsMomentSlice H A t + ε * t

/-- Fenchel conjugate of the regularized Gibbs potential. -/
def regGibbsDual {n : ℕ}
    (H A : FiniteOperatorAlgebra n) (ε η : ℝ) : ℝ :=
  sSup (Set.range fun s : ℝ => η * s - regGibbsPotential H A ε s)

theorem bddAbove_regGibbsDual_range {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) (η : ℝ) :
    BddAbove (Set.range fun s : ℝ => η * s - regGibbsPotential H A ε s) := by
  refine ⟨-realLogPartitionLine H A 0 +
      (η - gibbsMomentSlice H A 0) ^ 2 / (2 * ε), ?_⟩
  rintro y ⟨s, rfl⟩
  have hsub0 := gibbsLogPartitionSlice_subgradient H A hH hA s 0
  rw [sub_zero] at hsub0
  dsimp [regGibbsPotential]
  have hle :
      η * s - (realLogPartitionLine H A s + ε / 2 * s ^ 2) ≤
        (η - gibbsMomentSlice H A 0) * s - ε / 2 * s ^ 2 - realLogPartitionLine H A 0 :=
    scalar_fenchel_reg_upper_step hsub0
  exact le_trans hle (scalar_fenchel_reg_upper hε)

/-- **Global Regularized `FenchelDualPair` Witness**:
constructs an honest `HessianThermodynamicManifold.FenchelDualPair` on all of `ℝ`
without any assumed convexity or Legendre axioms. -/
theorem regGibbsFenchelDualPair {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    FenchelDualPair (regGibbsPotential H A ε) (regGibbsDual H A ε) (regGibbsGrad H A ε) where
  fenchel_young x y := by
    change InnerSpace.inner y x ≤ regGibbsPotential H A ε x + regGibbsDual H A ε y
    dsimp [InnerSpace.inner]
    have hle : y * x - regGibbsPotential H A ε x ≤ regGibbsDual H A ε y :=
      le_csSup (bddAbove_regGibbsDual_range H A hH hA hε y) ⟨x, rfl⟩
    exact scalar_le_add_of_sub_le hle
  legendre_identity x := by
    change regGibbsPotential H A ε x + regGibbsDual H A ε (regGibbsGrad H A ε x) =
      InnerSpace.inner (regGibbsGrad H A ε x) x
    dsimp [InnerSpace.inner]
    have hsup :
        regGibbsDual H A ε (regGibbsGrad H A ε x) =
          regGibbsGrad H A ε x * x - regGibbsPotential H A ε x := by
      unfold regGibbsDual
      apply IsGreatest.csSup_eq
      refine ⟨⟨x, rfl⟩, ?_⟩
      rintro z ⟨s, rfl⟩
      have hsub := gibbsLogPartitionSlice_subgradient H A hH hA s x
      have hquad : 0 ≤ (ε / 2) * (s - x) ^ 2 :=
        mul_nonneg (div_nonneg hε.le (by norm_num)) (sq_nonneg _)
      have hdiff :
          (regGibbsGrad H A ε x * x - regGibbsPotential H A ε x) -
              (regGibbsGrad H A ε x * s - regGibbsPotential H A ε s) =
            (realLogPartitionLine H A s -
              (realLogPartitionLine H A x + gibbsMomentSlice H A x * (s - x))) +
            (ε / 2) * (s - x) ^ 2 := by
        dsimp [regGibbsGrad, regGibbsPotential]
        ring
      exact sub_nonneg.mp (by rw [hdiff]; exact add_nonneg (sub_nonneg.mpr hsub) hquad)
    rw [hsup]
    ring

/-- The regularized `FenchelDualPair` inherits `SL2 ℝ` contragredient projective invariance
directly via `LegendreProjectiveDuality.legendre_contact_contragredient_invariant`. -/
theorem regGibbs_legendre_contact_contragredient_invariant {n : ℕ} [Nonempty (Fin n)]
    (H A : FiniteOperatorAlgebra n) (hH : IsSelfAdjoint H) (hA : IsSelfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) (M : SL2 ℝ) (t : ℝ) :
    InfoGeometry.Projective.MobiusDual.pairing
        (actLine M (dualLine (regGibbsGrad H A ε t))) (actPoint M (primalPoint t)) =
      regGibbsPotential H A ε t + regGibbsDual H A ε (regGibbsGrad H A ε t) :=
  legendre_contact_contragredient_invariant
    (regGibbsPotential H A ε) (regGibbsDual H A ε) (regGibbsGrad H A ε)
    (regGibbsFenchelDualPair H A hH hA hε) M t

end LegendreProjectiveSoldering

/-! ## Section 5: Operator Gibbs Potential, Moment Map, & Operator Bregman Law on `HSRealSelfAdjoint n` -/

section OperatorBregmanSoldering

/-- Equip the complete finite-dimensional real Hilbert space `HSRealSelfAdjoint n`
with `HessianThermodynamicManifold.InnerSpace`. -/
instance instInnerSpaceHSRealSelfAdjoint {n : ℕ} :
    InnerSpace (HSRealSelfAdjoint n) ℝ where
  inner A B := inner ℝ A B
  inner_zero_right A := inner_zero_right A

/-- Real operator Gibbs log-partition potential on `HSRealSelfAdjoint n`:
`ψ(H) = log Tr(exp(H))`. -/
def gibbsLogPartition {n : ℕ} (H : HSRealSelfAdjoint n) : ℝ :=
  Real.log (tracedExponential H.op).re

/-- Souriau–Barbaresco Legendre dual moment map `H ↦ ρ_H ∈ HSRealSelfAdjoint n`. -/
def gibbsMomentMap {n : ℕ} [Nonempty (Fin n)] (H : HSRealSelfAdjoint n) :
    HSRealSelfAdjoint n where
  op := (faithfulGibbsDensityOperator H.op H.isSelfAdjoint).rho
  isSelfAdjoint := (faithfulGibbsDensityOperator H.op H.isSelfAdjoint).strictlyPositive.isSelfAdjoint

theorem realLogPartitionLine_eq_gibbsLogPartition {n : ℕ} [Nonempty (Fin n)]
    (H A : HSRealSelfAdjoint n) (t : ℝ) :
    realLogPartitionLine H.op A.op t = gibbsLogPartition (H + t • A) := by
  dsimp [realLogPartitionLine, logPartitionLine, partitionLine, gibbsLogPartition]
  have hHt : IsSelfAdjoint (H + t • A).op := (H + t • A).isSelfAdjoint
  have hre_pos : 0 < (tracedExponential (H + t • A).op).re :=
    tracedExponential_re_pos_of_isSelfAdjoint _ hHt
  have him_zero : (tracedExponential (H + t • A).op).im = 0 :=
    tracedExponential_im_eq_zero_of_isSelfAdjoint _ hHt
  have hop : H.op + (t : ℂ) • A.op = (H + t • A).op := rfl
  rw [hop, Complex.log_re]
  have hnorm : ‖tracedExponential (H + t • A).op‖ = (tracedExponential (H + t • A).op).re := by
    have hz : tracedExponential (H + t • A).op = ((tracedExponential (H + t • A).op).re : ℂ) :=
      Complex.ext (by simp) (by simpa using him_zero)
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_of_nonneg hre_pos.le]
  rw [hnorm]

theorem inner_gibbsMomentMap_eq_realOperatorExpectation {n : ℕ} [Nonempty (Fin n)]
    (H A : HSRealSelfAdjoint n) :
    inner ℝ (gibbsMomentMap H) A = realOperatorExpectation H.op A.op := by
  rw [HSRealSelfAdjoint.inner_eq]
  dsimp [gibbsMomentMap, realOperatorExpectation]
  rw [operatorExpectation_eq_faithfulGibbsTrace H.op A.op H.isSelfAdjoint]

/-- **Full Noncommutative Operator Gibbs Bregman Nonnegativity**:
for ANY two noncommuting self-adjoint Hamiltonians `H₁, H₂ : HSRealSelfAdjoint n`,
`D_ψ(H₁, H₂) = ψ(H₁) - ψ(H₂) - ⟨ρ_{H₂}, H₁ - H₂⟩_HS ≥ 0`. -/
theorem gibbsOperatorBregman_nonneg {n : ℕ} [Nonempty (Fin n)]
    (H₁ H₂ : HSRealSelfAdjoint n) :
    0 ≤ bregman_divergence gibbsLogPartition gibbsMomentMap H₁ H₂ := by
  unfold bregman_divergence
  let D := H₁ - H₂
  change 0 ≤ gibbsLogPartition H₁ - gibbsLogPartition H₂ - inner ℝ (gibbsMomentMap H₂) D
  have h1 : H₁ = H₂ + (1 : ℝ) • D := by
    dsimp [D]
    rw [one_smul, add_sub_cancel]
  have h0 : H₂ = H₂ + (0 : ℝ) • D := by
    rw [zero_smul, add_zero]
  rw [show gibbsLogPartition H₁ = realLogPartitionLine H₂.op D.op 1 by
        rw [realLogPartitionLine_eq_gibbsLogPartition, ← h1],
      show gibbsLogPartition H₂ = realLogPartitionLine H₂.op D.op 0 by
        rw [realLogPartitionLine_eq_gibbsLogPartition, ← h0],
      inner_gibbsMomentMap_eq_realOperatorExpectation H₂ D]
  have hmom : gibbsMomentSlice H₂.op D.op 0 = realOperatorExpectation H₂.op D.op := by
    dsimp [gibbsMomentSlice]
    rw [zero_smul ℂ D.op, add_zero]
  have hsub := gibbsLogPartitionSlice_subgradient H₂.op D.op H₂.isSelfAdjoint D.isSelfAdjoint 1 0
  rw [hmom, sub_zero, mul_one] at hsub
  rw [sub_sub]
  exact sub_nonneg.mpr hsub

/-- **Full Noncommutative Operator Gibbs Bregman Strict Positivity**:
whenever `H₁ - H₂` is not a real scalar multiple of the identity,
`D_ψ(H₁, H₂) > 0` without any commutation assumption between `H₁` and `H₂`. -/
theorem gibbsOperatorBregman_pos_of_nonscalar {n : ℕ} [Nonempty (Fin n)]
    (H₁ H₂ : HSRealSelfAdjoint n)
    (hnonscalar : ∀ c : ℝ, (H₁ - H₂).op ≠ (c : ℂ) • (1 : FiniteOperatorAlgebra n)) :
    0 < bregman_divergence gibbsLogPartition gibbsMomentMap H₁ H₂ := by
  unfold bregman_divergence
  let D := H₁ - H₂
  change 0 < gibbsLogPartition H₁ - gibbsLogPartition H₂ - inner ℝ (gibbsMomentMap H₂) D
  have h1 : H₁ = H₂ + (1 : ℝ) • D := by
    dsimp [D]
    rw [one_smul, add_sub_cancel]
  have h0 : H₂ = H₂ + (0 : ℝ) • D := by
    rw [zero_smul, add_zero]
  rw [show gibbsLogPartition H₁ = realLogPartitionLine H₂.op D.op 1 by
        rw [realLogPartitionLine_eq_gibbsLogPartition, ← h1],
      show gibbsLogPartition H₂ = realLogPartitionLine H₂.op D.op 0 by
        rw [realLogPartitionLine_eq_gibbsLogPartition, ← h0],
      inner_gibbsMomentMap_eq_realOperatorExpectation H₂ D]
  have hmom : gibbsMomentSlice H₂.op D.op 0 = realOperatorExpectation H₂.op D.op := by
    dsimp [gibbsMomentSlice]
    rw [zero_smul ℂ D.op, add_zero]
  have hsub := gibbsLogPartitionSlice_strict_subgradient H₂.op D.op
    H₂.isSelfAdjoint D.isSelfAdjoint hnonscalar one_ne_zero
  rw [hmom, sub_zero, mul_one] at hsub
  rw [sub_sub]
  exact sub_pos.mpr hsub

end OperatorBregmanSoldering

end InfoGeometry.Canonical.KoszulSouriauLegendreCramerRaoSoldering
