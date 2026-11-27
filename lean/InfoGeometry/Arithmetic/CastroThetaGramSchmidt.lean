/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.CastroPerelmanCTAudit
import InfoGeometry.Physics.CastroFirstOrderFactorization
import InfoGeometry.Arithmetic.RiemannZetaEquivalences
import InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
import InfoGeometry.Arithmetic.CompletedZetaApollonianV4Bridge
import InfoGeometry.Arithmetic.CastroThetaScalingBridge
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Castro Mellin–Theta Representation, `Z(1/2) < 0`, Critical-Line Reality, and Finite Gram–Schmidt

This module formalizes Section 3 (Eqs. 25–44) of Carlos Castro (May 2006),
*On strategies towards the Riemann Hypothesis: Fractal SUSY-QM and a Trace Formula*,
connecting `CastroPerelmanCTAudit.pairingArgument` directly to Mathlib's actual
`completedRiemannZeta` and `completedRiemannZeta₀`.

## Mathematical Scope and Honesty Caveats

1. **Preservation of the Eq. (24) defect theorem**:
   `InfoGeometry.Physics.CastroFirstOrderFactorization` already proves the exact
   defect theorem (`D2_D1_psi_defect`, `D2_D1_psi_eq_casimir_iff`,
   `D2_D1_psi_eigenfunction_iff`) showing that `D2 ∘ D1` fails to yield
   `casimirEigenvalue s * psi` unless `s = 0` or `deriv W u = 1 / 2 - k`, whereas
   `inversionDual ∘ D1 = (1 - D1) ∘ D1` satisfies `inversionDual_D1_psi`
   unconditionally. Section 3's Mellin–theta pairing and Hermitian kernel depend
   only on `psi`, `theta_psi_reflection`, and `completedRiemannZeta`, never on
   `D2 ∘ D1`.

2. **Elizalde–Moretti–Zerbini [11] caveat**:
   Because Eq. (27) analytically continues the Mellin pairing by removing the
   divergent `n = 0` term of the Gauss–Jacobi theta series, Castro's kernel
   `castroKernel k ell` is NOT globally a positive-definite inner product
   (for `ell < 0`, e.g., `ell = -2` in Eq. 39, the diagonal value is strictly
   negative). Accordingly, finite `N`-step Gram–Schmidt orthonormalization and
   finite-matrix trace completeness in Section 4 are explicitly conditioned on a
   positive-definite `N × N` Gram matrix `(castroGramMatrix N k ell lambdas).PosDef`.
   No claim is made about global positive-definiteness at arbitrary spectral sets
   or about the Riemann Hypothesis.

## Main Results

1. **Critical-line reality**: `completedRiemannZeta_criticalLine_im_eq_zero`,
   `completedRiemannZeta_criticalLine_eq_ofReal`, and
   `completedRiemannZeta_criticalLine_conj_eq_self`.
2. **Mellin–theta Eq. (27) representation**: `jacobiOmega`, `hasSum_jacobiOmega`,
   `completedRiemannZeta₀_eq_integral_Ioi_one`,
   `completedRiemannZeta_eq_mellin_theta_split`, and
   `completedRiemannZeta_eq_mellin_theta_of_one_lt_re`.
3. **Strict negativity `Z(1/2) < 0`**: `completedRiemannZeta₀_half_re_lt_four`
   and `completedRiemannZeta_half_re_neg`.
4. **Hermitian kernel & Eqs. (29)–(31), (39)–(40)**: `castroKernel`,
   `castroKernel_conj`, `pairingArgument_criticalLine`,
   `castroKernel_criticalLine_diag_pos`, `castroKernel_criticalLine_diag_neg`,
   and `castroKernel_vacuum_neg_two`.
5. **Conditional finite `N`-step Gram–Schmidt & trace completeness**:
   `castroGramMatrix_isHermitian`, `CastroFiniteGramSystem`,
   `canonicalCastroFiniteGramSystem`, `castroGramSchmidtVecs`,
   `castroGramSchmidt_orthonormal`, `castroGramSchmidt_span`,
   `castroGramSchmidt_triangular`, `castroGramSchmidtMatrix_orthonormal`,
   `castroGramSchmidtMatrix_completeness_inv`, and
   `castroGramSchmidt_whitened_completeness`.
6. **Non-commutativity witnesses**: `pauliX2_mul_pauliZ2_ne`,
   `complex_matrix2_noncommutative`, and `complex_matrixN_noncommutative`.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Arithmetic.CastroThetaGramSchmidt

open Complex MeasureTheory Set Filter Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius ComplexOrder

/-! ## Section 1: Critical-Line Reality of `completedRiemannZeta` -/

/-- Along the critical line `1 / 2 + t * I`, `completedRiemannZeta` has zero
imaginary part. -/
theorem completedRiemannZeta_criticalLine_im_eq_zero (t : ℝ) :
    (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by
  rw [mul_comm (t : ℂ) Complex.I]
  exact (CompletedZetaApollonianV4Bridge.actualCompletedZeta_criticalLine_real 0 t).1

/-- Along the critical line `1 / 2 + t * I`, `completedRiemannZeta` equals the
complex coercion of its real part. -/
theorem completedRiemannZeta_criticalLine_eq_ofReal (t : ℝ) :
    completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) =
      ((completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).re : ℂ) := by
  rw [mul_comm (t : ℂ) Complex.I]
  exact (CompletedZetaApollonianV4Bridge.actualCompletedZeta_criticalLine_real 0 t).2.1

/-- Along the critical line `1 / 2 + t * I`, `completedRiemannZeta` is fixed by
complex conjugation. -/
theorem completedRiemannZeta_criticalLine_conj_eq_self (t : ℝ) :
    star (completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) =
      completedRiemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) := by
  have hre := completedRiemannZeta_criticalLine_eq_ofReal t
  rw [hre]
  simp

/-- Along the critical line `1 / 2 + t * I`, `completedRiemannZeta₀` also has
zero imaginary part. -/
theorem completedRiemannZeta₀_criticalLine_im_eq_zero (t : ℝ) :
    (completedRiemannZeta₀ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)).im = 0 := by
  rw [mul_comm (t : ℂ) Complex.I]
  exact (CompletedZetaApollonianV4Bridge.actualCompletedZeta_criticalLine_real 0 t).2.2.1

/-! ## Section 2: Mellin–Theta Eq. (27) Representation and `Z(1/2) < 0` -/

/-- Jacobi's theta series `ω(x) = ∑_{n=1}^∞ exp(-π n^2 x)` expressed via
Mathlib's `HurwitzZeta.evenKernel 0 x = 2 * ω(x) + 1`. -/
def jacobiOmega (x : ℝ) : ℝ :=
  (HurwitzZeta.evenKernel 0 x - 1) / 2

/-- For `0 < x`, `jacobiOmega x` is the exact sum of the Gaussian series
`∑_{n=0}^∞ exp(-π (n + 1)^2 x)`. -/
theorem hasSum_jacobiOmega {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x))
      (jacobiOmega x) := by
  have hcos := HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx
  have hcos' :
      HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x))
        (HurwitzZeta.evenKernel 0 x - 1) := by
    rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
    refine hcos.congr_fun fun n => ?_
    simp [Nat.cast_add, Nat.cast_one]
  simpa [jacobiOmega, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] using hcos'.div_const 2

/-- `jacobiOmega x` is strictly positive for all `x > 0`. -/
theorem jacobiOmega_pos {x : ℝ} (hx : 0 < x) : 0 < jacobiOmega x := by
  have hs := hasSum_jacobiOmega hx
  rw [← hs.tsum_eq]
  exact hs.summable.tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- `jacobiOmega x` is nonnegative for all `x > 0`. -/
theorem jacobiOmega_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ jacobiOmega x :=
  (jacobiOmega_pos hx).le

/-- Geometric series upper bound `ω(x) ≤ exp(-π x) / (1 - exp(-π x))` for `0 < x`. -/
theorem jacobiOmega_le_geom {x : ℝ} (hx : 0 < x) :
    jacobiOmega x ≤ Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) := by
  set r : ℝ := Real.exp (-Real.pi * x)
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt : r < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hgeom : HasSum (fun n : ℕ => r * r ^ n) (r / (1 - r)) := by
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr_pos.le hr_lt).mul_left r
  have hterm : ∀ n : ℕ,
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x) ≤ r * r ^ n := by
    intro n
    have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    have hpx : 0 < Real.pi * x := mul_pos Real.pi_pos hx
    have hexp_le : -Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x ≤
        -Real.pi * ((n + 1 : ℕ) : ℝ) * x := by
      nlinarith [hpx, hsq]
    calc
      Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2 * x)
          ≤ Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * x) := Real.exp_le_exp.mpr hexp_le
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * (-Real.pi * x)) := by
          congr 1
          ring
      _ = r ^ (n + 1) := by
          rw [Real.exp_nat_mul]
      _ = r * r ^ n := by
          rw [pow_succ']
  exact hasSum_le hterm (hasSum_jacobiOmega hx) hgeom

/-- For `1 ≤ x`, `ω(x) ≤ 2 * exp(-x)`. -/
theorem jacobiOmega_le_two_exp_neg {x : ℝ} (hx : 1 ≤ x) :
    jacobiOmega x ≤ 2 * Real.exp (-x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have h_pix : 1 ≤ Real.pi * x := by nlinarith
  have hexp_pi : Real.exp (-Real.pi * x) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hexp_one_half : Real.exp (-Real.pi * x) ≤ 1 / 2 := by
    have h1 : Real.exp (-Real.pi * x) ≤ Real.exp (-1) := by
      apply Real.exp_le_exp.mpr
      linarith
    have h2 : Real.exp (-1 : ℝ) < 1 / 2 := by
      have hmul : 1 < (1 / 2 : ℝ) * Real.exp 1 := by linarith [Real.exp_one_gt_two]
      rw [Real.exp_neg]
      exact (inv_lt_iff_one_lt_mul₀ (Real.exp_pos 1)).mpr hmul
    exact le_trans h1 h2.le
  have hden : 1 / 2 ≤ 1 - Real.exp (-Real.pi * x) := by linarith
  have hdiv : Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) ≤
      Real.exp (-Real.pi * x) / (1 / 2) := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hden
  calc
    jacobiOmega x ≤ Real.exp (-Real.pi * x) / (1 - Real.exp (-Real.pi * x)) :=
      jacobiOmega_le_geom hx_pos
    _ ≤ Real.exp (-Real.pi * x) / (1 / 2) := hdiv
    _ = 2 * Real.exp (-Real.pi * x) := by ring
    _ ≤ 2 * Real.exp (-x) := by linarith

private def jacobiOmegaTrunc (x : ℝ) : ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (fun t => (jacobiOmega t : ℂ)) x

private lemma hurwitzEvenFEPair_zero_fmodif_div_two_eqOn :
    EqOn (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2)
      (fun x => jacobiOmegaTrunc x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹)
      (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  rcases lt_trichotomy x 1 with hx1 | rfl | hx1
  · have hnot1 : x ∉ Set.Ioi (1 : ℝ) := Set.notMem_Ioi.mpr hx1.le
    have hmem01 : x ∈ Set.Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
    have hinv_gt : 1 < x⁻¹ := (one_lt_inv₀ hx0).2 hx1
    have hinv_mem : x⁻¹ ∈ Set.Ioi (1 : ℝ) := hinv_gt
    have hfe : HurwitzZeta.evenKernel 0 x =
        x ^ (-(1 / 2 : ℝ)) * HurwitzZeta.evenKernel 0 x⁻¹ := by
      have h := HurwitzZeta.evenKernel_functional_equation 0 x
      rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, one_div] at h
      rw [h, Real.rpow_neg hx0.le]
      simp only [one_div]
    have hcp : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      push_cast
      rfl
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, jacobiOmegaTrunc,
      Pi.add_apply, Function.comp_apply, ite_true, one_mul, smul_eq_mul, mul_one,
      Set.indicator_of_notMem hnot1, Set.indicator_of_mem hmem01,
      Set.indicator_of_mem hinv_mem, zero_add]
    rw [hcp, hfe]
    simp only [jacobiOmega]
    push_cast
    ring
  · simp [WeakFEPair.f_modif, jacobiOmegaTrunc]
  · have hmem1 : x ∈ Set.Ioi (1 : ℝ) := hx1
    have hnot01 : x ∉ Set.Ioo (0 : ℝ) 1 := Set.notMem_Ioo_of_ge hx1.le
    have hinv_lt : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1
    have hinv_not1 : x⁻¹ ∉ Set.Ioi (1 : ℝ) := Set.notMem_Ioi.mpr hinv_lt.le
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, jacobiOmegaTrunc,
      Pi.add_apply, Function.comp_apply, ite_true, Set.indicator_of_mem hmem1,
      Set.indicator_of_notMem hnot01, Set.indicator_of_notMem hinv_not1,
      add_zero, mul_zero]
    simp [jacobiOmega]

private lemma mellinConvergent_jacobiOmegaTrunc (z : ℂ) :
    MellinConvergent jacobiOmegaTrunc z := by
  have hm : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif z :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin z).1
  have hm2 : MellinConvergent (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2) z :=
    hm.div_const 2
  have hsub : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (z - 1) • ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2))
      (Set.Ioi (1 : ℝ)) :=
    hm2.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  have hind : IntegrableOn
      ((Set.Ioi (1 : ℝ)).indicator
        (fun x : ℝ => (x : ℂ) ^ (z - 1) • ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2)))
      (Set.Ioi (0 : ℝ)) :=
    (hsub.integrable_indicator measurableSet_Ioi).integrableOn
  refine hind.congr_fun (fun x hx => ?_) measurableSet_Ioi
  by_cases hx1 : x ∈ Set.Ioi (1 : ℝ)
  · have hnot01 : x ∉ Set.Ioo (0 : ℝ) 1 := Set.notMem_Ioo_of_ge (le_of_lt hx1)
    simp only [jacobiOmegaTrunc, Set.indicator_of_mem hx1, WeakFEPair.f_modif,
      HurwitzZeta.hurwitzEvenFEPair, Pi.add_apply, Function.comp_apply, ite_true,
      Set.indicator_of_notMem hnot01, add_zero, jacobiOmega]
    push_cast
    rfl
  · simp [jacobiOmegaTrunc, Set.indicator_of_notMem hx1]

/-- Integrability of `(x : ℂ) ^ (z - 1) * (jacobiOmega x : ℂ)` on `Set.Ioi 1`
for every `z : ℂ`. -/
lemma integrableOn_cpow_mul_jacobiOmega_Ioi_one (z : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (z - 1) * (jacobiOmega x : ℂ)) (Set.Ioi (1 : ℝ)) := by
  have hm := (mellinConvergent_jacobiOmegaTrunc z).mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine hm.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [jacobiOmegaTrunc, Set.indicator_of_mem hx]

/-- Exact `(1, ∞)` Mellin–theta integral representation of the entire function
`completedRiemannZeta₀ s` for all `s : ℂ` (Castro Eq. 27, entire part). -/
theorem completedRiemannZeta₀_eq_integral_Ioi_one (s : ℂ) :
    completedRiemannZeta₀ s =
      ∫ x in Set.Ioi (1 : ℝ),
        ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * (jacobiOmega x : ℂ) := by
  have hbase : completedRiemannZeta₀ s =
      mellin (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2) (s / 2) := by
    change HurwitzZeta.completedHurwitzZetaEven₀ 0 s = _
    rw [HurwitzZeta.completedHurwitzZetaEven₀, WeakFEPair.Λ₀, mellin_div_const]
  have hm_sum : MellinConvergent
      (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2) (s / 2) :=
    (((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1).div_const 2
  have hm1 : MellinConvergent jacobiOmegaTrunc (s / 2) :=
    mellinConvergent_jacobiOmegaTrunc (s / 2)
  have hm_eq : MellinConvergent
      (fun x => jacobiOmegaTrunc x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹) (s / 2) := by
    refine hm_sum.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, hurwitzEvenFEPair_zero_fmodif_div_two_eqOn hx]
  have hm2 : MellinConvergent
      (fun x => (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹) (s / 2) := by
    have hsub := hm_eq.sub hm1
    refine hsub.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul, Pi.sub_apply]
    ring
  have hmellin_split :
      mellin (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2) (s / 2) =
        mellin jacobiOmegaTrunc (s / 2) +
          mellin (fun x => (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹) (s / 2) := by
    have h1 : mellin (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x / 2) (s / 2) =
        mellin (fun x => jacobiOmegaTrunc x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹)
          (s / 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp only [smul_eq_mul, hurwitzEvenFEPair_zero_fmodif_div_two_eqOn hx]
    rw [h1, (hasMellin_add hm1 hm2).2]
  have hm2_eval :
      mellin (fun x => (x : ℂ) ^ (-(1 / 2 : ℂ)) * jacobiOmegaTrunc x⁻¹) (s / 2) =
        mellin jacobiOmegaTrunc ((1 - s) / 2) := by
    have hcpow :
        mellin (fun x => (x : ℂ) ^ (-(1 / 2 : ℂ)) • jacobiOmegaTrunc x⁻¹) (s / 2) =
          mellin (fun x => jacobiOmegaTrunc x⁻¹) (s / 2 + (-(1 / 2 : ℂ))) :=
      mellin_cpow_smul (fun x => jacobiOmegaTrunc x⁻¹) (s / 2) (-(1 / 2 : ℂ))
    simp only [smul_eq_mul] at hcpow
    rw [hcpow, mellin_comp_inv]
    congr 1
    ring
  have hmellin_trunc : ∀ z : ℂ,
      mellin jacobiOmegaTrunc z =
        ∫ x in Set.Ioi (1 : ℝ), (x : ℂ) ^ (z - 1) * (jacobiOmega x : ℂ) := by
    intro z
    have hcongr :
        mellin jacobiOmegaTrunc z =
          ∫ x in Set.Ioi (0 : ℝ),
            (Set.Ioi (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * (jacobiOmega t : ℂ)) x := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      by_cases hx1 : x ∈ Set.Ioi (1 : ℝ)
      · simp [jacobiOmegaTrunc, Set.indicator_of_mem hx1]
      · simp [jacobiOmegaTrunc, Set.indicator_of_notMem hx1]
    rw [hcongr, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  rw [hbase, hmellin_split, hm2_eval, hmellin_trunc (s / 2), hmellin_trunc ((1 - s) / 2)]
  rw [← integral_add (integrableOn_cpow_mul_jacobiOmega_Ioi_one (s / 2))
    (integrableOn_cpow_mul_jacobiOmega_Ioi_one ((1 - s) / 2))]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  ring

/-- Castro's Mellin–theta representation Eq. (27) for the analytic continuation
of `completedRiemannZeta s` away from the poles `s = 0, 1`. -/
theorem completedRiemannZeta_eq_mellin_theta_split {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedRiemannZeta s =
      1 / (s * (s - 1)) +
        ∫ x in Set.Ioi (1 : ℝ),
          ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) * (jacobiOmega x : ℂ) := by
  have hs1' : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [completedRiemannZeta_eq, completedRiemannZeta₀_eq_integral_Ioi_one s]
  have hrat : -(1 / s) - 1 / (1 - s) = 1 / (s * (s - 1)) := by
    field_simp [hs0, hs1']
    ring
  linear_combination hrat

/-- Castro's Mellin–theta Eq. (27) LHS integral on `(0, ∞)` for `1 < s.re`. -/
theorem completedRiemannZeta_eq_mellin_theta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s =
      ∫ x in Set.Ioi (0 : ℝ), (x : ℂ) ^ (s / 2 - 1) * (jacobiOmega x : ℂ) := by
  have hre : (HurwitzZeta.hurwitzEvenFEPair 0).k < (s / 2).re := by
    change (1 / 2 : ℝ) < (s / 2).re
    have hs2 : (s / 2).re = s.re / 2 := by simp
    linarith [hs, hs2]
  have hm := ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin hre).2
  have hm2 :
      mellin (fun x => ((HurwitzZeta.hurwitzEvenFEPair 0).f x -
          (HurwitzZeta.hurwitzEvenFEPair 0).f₀) / 2) (s / 2) =
        completedRiemannZeta s := by
    rw [mellin_div_const, hm]
    rfl
  rw [← hm2]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  simp [HurwitzZeta.hurwitzEvenFEPair, jacobiOmega]

/-- Strict upper bound `(completedRiemannZeta₀ (1 / 2)).re < 4`, proved analytically
via `jacobiOmega_le_two_exp_neg` and `Real.integral_exp_neg_Ioi`. -/
theorem completedRiemannZeta₀_half_re_lt_four :
    (completedRiemannZeta₀ (1 / 2 : ℂ)).re < 4 := by
  have h0 : completedRiemannZeta₀ (1 / 2 : ℂ) =
      ∫ x in Set.Ioi (1 : ℝ), ((2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x : ℝ) : ℂ) := by
    rw [completedRiemannZeta₀_eq_integral_Ioi_one]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx_nonneg : 0 ≤ x := (lt_trans zero_lt_one hx).le
    have hexp1 : (1 / 2 : ℂ) / 2 - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    have hexp2 : (1 - (1 / 2 : ℂ)) / 2 - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hexp1, hexp2, ← Complex.ofReal_cpow hx_nonneg]
    push_cast
    ring
  have hre_eq : (completedRiemannZeta₀ (1 / 2 : ℂ)).re =
      ∫ x in Set.Ioi (1 : ℝ), 2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x := by
    rw [h0, integral_complex_ofReal]
    simp
  have hint_complex : IntegrableOn
      (fun x : ℝ => ((2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x : ℝ) : ℂ)) (Set.Ioi (1 : ℝ)) := by
    have hm := (integrableOn_cpow_mul_jacobiOmega_Ioi_one ((1 / 2 : ℂ) / 2)).const_mul 2
    refine IntegrableOn.congr_fun hm (fun x hx => ?_) measurableSet_Ioi
    have hx_nonneg : 0 ≤ x := (lt_trans zero_lt_one hx).le
    have hexp1 : (1 / 2 : ℂ) / 2 - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hexp1, ← Complex.ofReal_cpow hx_nonneg]
    push_cast
    ring
  have hint_real :
      IntegrableOn (fun x : ℝ => 2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x) (Set.Ioi (1 : ℝ)) :=
    hint_complex.re
  have hmono :
      ∫ x in Set.Ioi (1 : ℝ), 2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x ≤
        ∫ x in Set.Ioi (1 : ℝ), 4 * Real.exp (-x) := by
    refine setIntegral_mono_on hint_real ((integrableOn_exp_neg_Ioi 1).const_mul 4)
      measurableSet_Ioi (fun x hx => ?_)
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hpow_le : x ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hpow_nonneg : 0 ≤ x ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_nonneg (lt_trans zero_lt_one hx).le _
    have homega_le : jacobiOmega x ≤ 2 * Real.exp (-x) :=
      jacobiOmega_le_two_exp_neg hx1
    have homega_nonneg : 0 ≤ jacobiOmega x :=
      jacobiOmega_nonneg (lt_trans zero_lt_one hx)
    calc
      2 * x ^ (-(3 / 4 : ℝ)) * jacobiOmega x
          ≤ 2 * 1 * jacobiOmega x := by
            gcongr
      _ = 2 * jacobiOmega x := by ring
      _ ≤ 2 * (2 * Real.exp (-x)) := by linarith
      _ = 4 * Real.exp (-x) := by ring
  have hexp_int : (∫ x in Set.Ioi (1 : ℝ), 4 * Real.exp (-x)) = 4 * Real.exp (-1) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi 1]
  have hexp_lt : 4 * Real.exp (-1 : ℝ) < 2 := by
    have h2 : Real.exp (-1 : ℝ) < 1 / 2 := by
      have hmul : 1 < (1 / 2 : ℝ) * Real.exp 1 := by linarith [Real.exp_one_gt_two]
      rw [Real.exp_neg]
      exact (inv_lt_iff_one_lt_mul₀ (Real.exp_pos 1)).mpr hmul
    linarith
  linarith

/-- Strict negativity of `completedRiemannZeta` at `s = 1 / 2`:
`Z(1 / 2) < 0` (Castro §3, Eq. 31 / Eq. 39). -/
theorem completedRiemannZeta_half_re_neg :
    (completedRiemannZeta (1 / 2 : ℂ)).re < 0 := by
  have heq : completedRiemannZeta (1 / 2 : ℂ) = completedRiemannZeta₀ (1 / 2 : ℂ) - 4 := by
    rw [completedRiemannZeta_eq]
    norm_num
    ring
  have hre : (completedRiemannZeta (1 / 2 : ℂ)).re = (completedRiemannZeta₀ (1 / 2 : ℂ)).re - 4 := by
    rw [heq]
    simp
  linarith [completedRiemannZeta₀_half_re_lt_four]

/-- At `s = 1 / 2`, `completedRiemannZeta (1 / 2)` is real-valued. -/
theorem completedRiemannZeta_half_im_zero :
    (completedRiemannZeta (1 / 2 : ℂ)).im = 0 := by
  simpa using completedRiemannZeta_criticalLine_im_eq_zero 0

/-! ## Section 3: Pairing Argument Connection and Hermitian Kernel (Eqs. 29–31, 39–40) -/

/-- Castro's regularized kernel map `S(s₁, s₂) = -(2 / ℓ) * Z(pairingArgument k ℓ s₁ s₂)`
from Eq. (29), directly evaluated at Mathlib's actual `completedRiemannZeta`. -/
def castroKernel (k ell : ℝ) (s₁ s₂ : ℂ) : ℂ :=
  -(2 / (ell : ℂ)) * completedRiemannZeta (CastroPerelmanCTAudit.pairingArgument k ell s₁ s₂)

/-- On conjugate-reflected labels `(s, 1 - star s)`, `castroKernel` evaluates to
`-(2 / ℓ) * Z(1 / 2)`, instantiating `CastroPerelmanCTAudit.pairingArgument_ct`. -/
theorem castroKernel_eq_pairingArgument_ct (k ell : ℝ) (hell : ell ≠ 0)
    (hscale : ell = 4 * (2 * k - 1)) (s : ℂ) :
    castroKernel k ell s (1 - star s) = -(2 / (ell : ℂ)) * completedRiemannZeta (1 / 2) := by
  unfold castroKernel
  rw [CastroPerelmanCTAudit.pairingArgument_ct k ell hell hscale s]

/-- Unconditional Hermitian symmetry of `castroKernel`:
`star (castroKernel k ell s₁ s₂) = castroKernel k ell s₂ s₁`. -/
theorem castroKernel_conj (k ell : ℝ) (s₁ s₂ : ℂ) :
    star (castroKernel k ell s₁ s₂) = castroKernel k ell s₂ s₁ := by
  have harg : star (CastroPerelmanCTAudit.pairingArgument k ell s₁ s₂) =
      CastroPerelmanCTAudit.pairingArgument k ell s₂ s₁ := by
    unfold CastroPerelmanCTAudit.pairingArgument
    simp [star_mul, star_sub, star_add, add_comm, mul_comm]
  unfold castroKernel
  rw [star_mul, ← ActualRiemannXiSchwarzBridge.completedRiemannZeta_conj, harg]
  have hpref : star (-(2 / (ell : ℂ))) = -(2 / (ell : ℂ)) := by
    simp
  rw [hpref, mul_comm]

/-- Exact critical-line argument formula (Castro Eq. 30): for `sⱼ = 1 / 2 + i λⱼ`
and `ℓ = 4 * (2 * k - 1) ≠ 0`, `pairingArgument k ℓ s₁ s₂ = 1 / 2 + 2 i (λ₁ - λ₂) / ℓ`. -/
theorem pairingArgument_criticalLine (k ell : ℝ) (hell : ell ≠ 0)
    (hscale : ell = 4 * (2 * k - 1)) (lam₁ lam₂ : ℝ) :
    CastroPerelmanCTAudit.pairingArgument k ell
        ((1 / 2 : ℂ) + (lam₁ : ℂ) * Complex.I)
        ((1 / 2 : ℂ) + (lam₂ : ℂ) * Complex.I) =
      (1 / 2 : ℂ) + ((2 * (lam₁ - lam₂) / ell : ℝ) : ℂ) * Complex.I := by
  have hellC : (ell : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell
  have hscaleC : (ell : ℂ) = 4 * (2 * (k : ℂ) - 1) := by exact_mod_cast hscale
  have hstar : star ((1 / 2 : ℂ) + (lam₁ : ℂ) * Complex.I) =
      (1 / 2 : ℂ) - (lam₁ : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  unfold CastroPerelmanCTAudit.pairingArgument
  rw [hstar]
  have hdiff : (2 : ℂ) * (k : ℂ) -
      (((1 / 2 : ℂ) - (lam₁ : ℂ) * Complex.I) + ((1 / 2 : ℂ) + (lam₂ : ℂ) * Complex.I)) =
      (2 * (k : ℂ) - 1) + ((lam₁ : ℂ) - (lam₂ : ℂ)) * Complex.I := by
    ring
  have hhalf : (2 / (ell : ℂ)) * (2 * (k : ℂ) - 1) = (1 / 2 : ℂ) := by
    field_simp [hellC]
    linear_combination -hscaleC
  rw [hdiff, mul_add, hhalf]
  push_cast
  ring

/-- On the critical line `s = 1 / 2 + λ * I`, the diagonal value of `castroKernel`
is `-(2 / ℓ) * Z(1 / 2)` (Castro Eq. 31). -/
theorem castroKernel_criticalLine_diag (k ell : ℝ) (hell : ell ≠ 0)
    (hscale : ell = 4 * (2 * k - 1)) (lam : ℝ) :
    castroKernel k ell ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)
        ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I) =
      -(2 / (ell : ℂ)) * completedRiemannZeta (1 / 2) := by
  unfold castroKernel
  rw [pairingArgument_criticalLine k ell hell hscale lam lam]
  simp

/-- Diagonal positivity on the critical line for `ℓ > 0`: since `Z(1 / 2) < 0`,
`Re (castroKernel k ℓ (1/2 + iλ) (1/2 + iλ)) > 0` and its imaginary part is zero. -/
theorem castroKernel_criticalLine_diag_pos {k ell : ℝ} (hell : 0 < ell)
    (hscale : ell = 4 * (2 * k - 1)) (lam : ℝ) :
    0 < (castroKernel k ell ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)
      ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)).re ∧
    (castroKernel k ell ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)
      ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)).im = 0 := by
  rw [castroKernel_criticalLine_diag k ell hell.ne' hscale lam]
  have hZ : completedRiemannZeta (1 / 2 : ℂ) = ((completedRiemannZeta (1 / 2 : ℂ)).re : ℂ) := by
    simpa using completedRiemannZeta_criticalLine_eq_ofReal 0
  rw [hZ]
  have hre : (-(2 / (ell : ℂ)) * ((completedRiemannZeta (1 / 2 : ℂ)).re : ℂ)).re =
      -(2 / ell) * (completedRiemannZeta (1 / 2 : ℂ)).re := by
    norm_cast
  have him : (-(2 / (ell : ℂ)) * ((completedRiemannZeta (1 / 2 : ℂ)).re : ℂ)).im = 0 := by
    norm_cast
  refine ⟨?_, him⟩
  rw [hre]
  have hneg_pref : -(2 / ell) < 0 := by
    linarith [div_pos (by norm_num : (0 : ℝ) < 2) hell]
  exact mul_pos_of_neg_of_neg hneg_pref completedRiemannZeta_half_re_neg

/-- Diagonal negativity on the critical line for `ℓ < 0` (Castro Eq. 39 at `ℓ = -2`,
`k = 1 / 4`), reflecting the Elizalde–Moretti–Zerbini [11] non-positivity regime. -/
theorem castroKernel_criticalLine_diag_neg {k ell : ℝ} (hell : ell < 0)
    (hscale : ell = 4 * (2 * k - 1)) (lam : ℝ) :
    (castroKernel k ell ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)
      ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I)).re < 0 := by
  rw [castroKernel_criticalLine_diag k ell hell.ne hscale lam]
  have hZ : completedRiemannZeta (1 / 2 : ℂ) = ((completedRiemannZeta (1 / 2 : ℂ)).re : ℂ) := by
    simpa using completedRiemannZeta_criticalLine_eq_ofReal 0
  rw [hZ]
  have hre : (-(2 / (ell : ℂ)) * ((completedRiemannZeta (1 / 2 : ℂ)).re : ℂ)).re =
      -(2 / ell) * (completedRiemannZeta (1 / 2 : ℂ)).re := by
    norm_cast
  rw [hre]
  have hpos_pref : 0 < -(2 / ell) := by
    have : 2 / ell < 0 := div_neg_of_pos_of_neg (by norm_num) hell
    linarith
  exact mul_neg_of_pos_of_neg hpos_pref completedRiemannZeta_half_re_neg

/-- Vacuum-state kernel evaluation at `ℓ = -2, k = 1 / 4` (Castro Eq. 40):
orthogonality of `Ψ_{1/2 + iλ}` to the vacuum state `Ψ_{1/2}` occurs iff
`completedRiemannZeta (1 / 2 + iλ) = 0`. -/
theorem castroKernel_vacuum_neg_two (lam : ℝ) :
    castroKernel (1 / 4) (-2) (1 / 2) ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I) =
      completedRiemannZeta ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I) := by
  have harg : CastroPerelmanCTAudit.pairingArgument (1 / 4) (-2) (1 / 2)
      ((1 / 2 : ℂ) + (lam : ℂ) * Complex.I) = (1 / 2 : ℂ) + (lam : ℂ) * Complex.I := by
    have h := pairingArgument_criticalLine (1 / 4) (-2) (by norm_num) (by norm_num) 0 lam
    simpa using h
  unfold castroKernel
  rw [harg]
  norm_num

/-! ## Section 4: Conditional Finite `N`-Step Gram–Schmidt & Trace Completeness -/

/-- Finite `N × N` Gram matrix `G_{ij} = castroKernel k ℓ (1/2 + i λ_i) (1/2 + i λ_j)`
along a supplied `N`-tuple of critical-line frequencies `lambdas : Fin N → ℝ`. -/
def castroGramMatrix (N : ℕ) (k ell : ℝ) (lambdas : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    castroKernel k ell
      ((1 / 2 : ℂ) + (lambdas i : ℂ) * Complex.I)
      ((1 / 2 : ℂ) + (lambdas j : ℂ) * Complex.I)

/-- Unconditional Hermitian symmetry of `castroGramMatrix`. -/
theorem castroGramMatrix_isHermitian (N : ℕ) (k ell : ℝ) (lambdas : Fin N → ℝ) :
    (castroGramMatrix N k ell lambdas).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, castroGramMatrix, castroKernel_conj]

/-- Conditional finite `N`-step Gram–Schmidt data for Castro's kernel on `N`
critical-line spectral labels, explicitly requiring positive-definiteness of the
finite `N × N` Gram matrix (respecting Elizalde–Moretti–Zerbini [11]). -/
structure CastroFiniteGramSystem (N : ℕ) where
  k : ℝ
  ell : ℝ
  hell : 0 < ell
  hscale : ell = 4 * (2 * k - 1)
  lambdas : Fin N → ℝ
  posDef : (castroGramMatrix N k ell lambdas).PosDef

/-- T17 constructive inhabitant at `N = 1`, `k = 1`, `ell = 4`, `lambdas = 0`,
proved unconditionally from `completedRiemannZeta_half_re_neg`. -/
def canonicalCastroFiniteGramSystem : CastroFiniteGramSystem 1 where
  k := 1
  ell := 4
  hell := by norm_num
  hscale := by norm_num
  lambdas := fun _ => 0
  posDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (castroGramMatrix_isHermitian 1 1 4 (fun _ => 0)) ?_
    intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hzero
      apply hx
      ext i
      fin_cases i
      exact hzero
    have hdiag := castroKernel_criticalLine_diag_pos (k := 1) (ell := 4)
      (by norm_num) (by norm_num) 0
    have hEntry : castroGramMatrix 1 1 4 (fun _ => 0) 0 0 =
        ((castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa [castroGramMatrix] using hdiag.2
    have hEntry_pos : 0 < (castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re := by
      simpa [castroGramMatrix] using hdiag.1
    have hdot : star x ⬝ᵥ (castroGramMatrix 1 1 4 (fun _ => 0) *ᵥ x) =
        ((Complex.normSq (x 0) * (castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_one, Fin.isValue]
      rw [hEntry]
      have hmul : star (x 0) * x 0 = (Complex.normSq (x 0) : ℂ) := by
        rw [mul_comm]
        simpa [Complex.star_def] using Complex.mul_conj (x 0)
      calc
        star (x 0) * ((castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re * x 0)
            = (star (x 0) * x 0) * ((castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re : ℂ) := by ring
        _ = (Complex.normSq (x 0) : ℂ) *
              ((castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re : ℂ) := by rw [hmul]
        _ = ((Complex.normSq (x 0) *
              (castroGramMatrix 1 1 4 (fun _ => 0) 0 0).re : ℝ) : ℂ) := by push_cast; rfl
    rw [hdot, RCLike.pos_iff]
    refine ⟨?_, by simp⟩
    exact mul_pos (Complex.normSq_pos.mpr hx0) hEntry_pos

instance : Inhabited (CastroFiniteGramSystem 1) := ⟨canonicalCastroFiniteGramSystem⟩

/-- Orthonormal coefficient vectors `φ n : Fin N → ℂ` produced by Mathlib's
`InnerProductSpace.gramSchmidtNormed` in the finite inner-product space
induced by `S.posDef`. -/
def castroGramSchmidtVecs {N : ℕ} (S : CastroFiniteGramSystem N) : Fin N → (Fin N → ℂ) :=
  let G := castroGramMatrix N S.k S.ell S.lambdas
  @InnerProductSpace.gramSchmidtNormed ℂ (Fin N → ℂ) _
    (G.toNormedAddCommGroup S.posDef)
    (G.toInnerProductSpace S.posDef.posSemidef)
    (Fin N) _ _ _ (Pi.basisFun ℂ (Fin N))

/-- Matrix `U : Matrix (Fin N) (Fin N) ℂ` whose `n`-th column is `castroGramSchmidtVecs S n`
(corresponding to Castro Eq. 37 coefficients `a_{mn} = U m n`). -/
def castroGramSchmidtMatrix {N : ℕ} (S : CastroFiniteGramSystem N) : Matrix (Fin N) (Fin N) ℂ :=
  fun m n => castroGramSchmidtVecs S n m

/-- Exact orthonormality of `castroGramSchmidtVecs S` with respect to the Gram
form `star v ⬝ᵥ (G *ᵥ w)` (Castro Eqs. 33–36). -/
theorem castroGramSchmidt_orthonormal {N : ℕ} (S : CastroFiniteGramSystem N) :
    ∀ m n : Fin N,
      star (castroGramSchmidtVecs S m) ⬝ᵥ
          (castroGramMatrix N S.k S.ell S.lambdas *ᵥ castroGramSchmidtVecs S n) =
        if m = n then 1 else 0 := by
  let G := castroGramMatrix N S.k S.ell S.lambdas
  let hn := G.toNormedAddCommGroup S.posDef
  let hi := G.toInnerProductSpace S.posDef.posSemidef
  have hli : LinearIndependent ℂ (Pi.basisFun ℂ (Fin N)) :=
    (Pi.basisFun ℂ (Fin N)).linearIndependent
  have horth : @Orthonormal ℂ (Fin N → ℂ) _ hn.toSeminormedAddCommGroup hi (Fin N)
      (castroGramSchmidtVecs S) :=
    @InnerProductSpace.gramSchmidtNormed_orthonormal ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
      (Pi.basisFun ℂ (Fin N)) hli
  intro m n
  by_cases hmn : m = n
  · subst hmn
    simp only [↓reduceIte, dotProduct_comm]
    have hnorm := horth.1 m
    have hinner : @inner ℂ (Fin N → ℂ) _
        (castroGramSchmidtVecs S m) (castroGramSchmidtVecs S m) =
        ((@norm (Fin N → ℂ) hn.toNorm (castroGramSchmidtVecs S m) : ℂ) ^ 2) := by
      exact @inner_self_eq_norm_sq_to_K ℂ (Fin N → ℂ) _ hn.toSeminormedAddCommGroup hi
        (castroGramSchmidtVecs S m)
    change @inner ℂ (Fin N → ℂ) _
        (castroGramSchmidtVecs S m) (castroGramSchmidtVecs S m) = 1
    rw [hinner, hnorm]
    norm_num
  · simp only [hmn, ↓reduceIte, dotProduct_comm]
    exact horth.2 hmn

/-- Full span of `castroGramSchmidtVecs S` in `Fin N → ℂ`. -/
theorem castroGramSchmidt_span {N : ℕ} (S : CastroFiniteGramSystem N) :
    Submodule.span ℂ (Set.range (castroGramSchmidtVecs S)) = ⊤ := by
  let G := castroGramMatrix N S.k S.ell S.lambdas
  let hn := G.toNormedAddCommGroup S.posDef
  let hi := G.toInnerProductSpace S.posDef.posSemidef
  change Submodule.span ℂ (Set.range (@InnerProductSpace.gramSchmidtNormed ℂ (Fin N → ℂ) _
      hn hi (Fin N) _ _ _ (Pi.basisFun ℂ (Fin N)))) = ⊤
  rw [@InnerProductSpace.span_gramSchmidtNormed_range ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
      (Pi.basisFun ℂ (Fin N)),
    @InnerProductSpace.span_gramSchmidt ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
      (Pi.basisFun ℂ (Fin N)),
    (Pi.basisFun ℂ (Fin N)).span_eq]

/-- Triangularity of the Gram–Schmidt coefficients (Castro Eq. 37):
`a_{mn} = 0` whenever `n < m`. -/
theorem castroGramSchmidt_triangular {N : ℕ} (S : CastroFiniteGramSystem N)
    {m n : Fin N} (hnm : n < m) :
    castroGramSchmidtMatrix S m n = 0 := by
  let G := castroGramMatrix N S.k S.ell S.lambdas
  let hn := G.toNormedAddCommGroup S.posDef
  let hi := G.toInnerProductSpace S.posDef.posSemidef
  have htri :
      (Pi.basisFun ℂ (Fin N)).repr
        (@InnerProductSpace.gramSchmidt ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
          (Pi.basisFun ℂ (Fin N)) n) m = 0 :=
    @InnerProductSpace.gramSchmidt_triangular ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
      n m hnm (Pi.basisFun ℂ (Fin N))
  rw [Pi.basisFun_repr] at htri
  change (@norm (Fin N → ℂ) hn.toNorm
      (@InnerProductSpace.gramSchmidt ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
        (Pi.basisFun ℂ (Fin N)) n) : ℂ)⁻¹ *
      (@InnerProductSpace.gramSchmidt ℂ (Fin N → ℂ) _ hn hi (Fin N) _ _ _
        (Pi.basisFun ℂ (Fin N)) n m) = 0
  rw [htri, mul_zero]

/-- Matrix orthonormality equation `Uᴴ * G * U = 1` for `U = castroGramSchmidtMatrix S`. -/
theorem castroGramSchmidtMatrix_orthonormal {N : ℕ} (S : CastroFiniteGramSystem N) :
    (castroGramSchmidtMatrix S)ᴴ * castroGramMatrix N S.k S.ell S.lambdas *
        castroGramSchmidtMatrix S = 1 := by
  ext m n
  have hmul :
      ((castroGramSchmidtMatrix S)ᴴ * castroGramMatrix N S.k S.ell S.lambdas *
          castroGramSchmidtMatrix S) m n =
        star (castroGramSchmidtVecs S m) ⬝ᵥ
          (castroGramMatrix N S.k S.ell S.lambdas *ᵥ castroGramSchmidtVecs S n) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, castroGramSchmidtMatrix,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hmul, castroGramSchmidt_orthonormal S m n]
  simp [Matrix.one_apply]

/-- Finite-matrix inverse completeness and trace identity (finite counterpart of
Castro Eqs. 41–44): `U * Uᴴ = G⁻¹`, `G * (U * Uᴴ) = 1`, and
`Matrix.trace (G * (U * Uᴴ)) = N`. -/
theorem castroGramSchmidtMatrix_completeness_inv {N : ℕ} (S : CastroFiniteGramSystem N) :
    castroGramSchmidtMatrix S * (castroGramSchmidtMatrix S)ᴴ =
        (castroGramMatrix N S.k S.ell S.lambdas)⁻¹ ∧
      castroGramMatrix N S.k S.ell S.lambdas *
          (castroGramSchmidtMatrix S * (castroGramSchmidtMatrix S)ᴴ) = 1 ∧
      Matrix.trace (castroGramMatrix N S.k S.ell S.lambdas *
          (castroGramSchmidtMatrix S * (castroGramSchmidtMatrix S)ᴴ)) = (N : ℂ) := by
  set G := castroGramMatrix N S.k S.ell S.lambdas
  set U := castroGramSchmidtMatrix S
  have hU : Uᴴ * G * U = 1 := castroGramSchmidtMatrix_orthonormal S
  have hG_det : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp S.posDef.isUnit
  have hG_inv : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG_det
  have hright : (G * U) * Uᴴ = 1 := by
    rw [← _root_.mul_eq_one_comm]
    simpa [Matrix.mul_assoc] using hU
  have hGU : G * (U * Uᴴ) = 1 := by
    simpa [Matrix.mul_assoc] using hright
  have hUU : U * Uᴴ = G⁻¹ := by
    calc
      U * Uᴴ = (G⁻¹ * G) * (U * Uᴴ) := by rw [hG_inv, Matrix.one_mul]
      _ = G⁻¹ * (G * (U * Uᴴ)) := by rw [Matrix.mul_assoc]
      _ = G⁻¹ * 1 := by rw [hGU]
      _ = G⁻¹ := by rw [Matrix.mul_one]
  have htr : Matrix.trace (G * (U * Uᴴ)) = (N : ℂ) := by
    rw [hGU, Matrix.trace_one, Fintype.card_fin]
  exact ⟨hUU, hGU, htr⟩

/-- Canonical whitening factor `C` satisfying `Cᴴ * C = G`, constructed from
the spectral theorem of `G.PosDef`. -/
def canonicalWhiteningFactor {N : ℕ} (S : CastroFiniteGramSystem N) : Matrix (Fin N) (Fin N) ℂ :=
  let hH := S.posDef.isHermitian
  Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) *
    (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ

/-- Verification that `canonicalWhiteningFactor S` satisfies `Cᴴ * C = G`. -/
theorem canonicalWhiteningFactor_conjTranspose_mul {N : ℕ} (S : CastroFiniteGramSystem N) :
    (canonicalWhiteningFactor S)ᴴ * canonicalWhiteningFactor S =
      castroGramMatrix N S.k S.ell S.lambdas := by
  let G := castroGramMatrix N S.k S.ell S.lambdas
  let hH := S.posDef.isHermitian
  let U₀ : Matrix (Fin N) (Fin N) ℂ := hH.eigenvectorUnitary
  have heig : ∀ i, 0 ≤ hH.eigenvalues i := fun i => (S.posDef.eigenvalues_pos i).le
  have hdiag :
      (Matrix.diagonal fun i : Fin N => (Real.sqrt (hH.eigenvalues i) : ℂ))ᴴ *
          Matrix.diagonal (fun i : Fin N => (Real.sqrt (hH.eigenvalues i) : ℂ)) =
        Matrix.diagonal (fun i : Fin N => (hH.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
      rw [Finset.sum_eq_single i]
      · simp [Complex.conj_ofReal]
        norm_cast
        exact Real.mul_self_sqrt (heig i)
      · intro k _ hki
        simp [Matrix.diagonal_apply_ne _ hki]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ hij]
      rw [Finset.sum_eq_zero]
      intro k _
      by_cases hki : k = i
      · subst hki
        simp [Matrix.diagonal_apply_ne _ hij]
      · simp [Matrix.diagonal_apply_ne _ hki]
  calc
    (canonicalWhiteningFactor S)ᴴ * canonicalWhiteningFactor S
        = (U₀ * (Matrix.diagonal fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))ᴴ) *
            (Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * U₀ᴴ) := by
            simp [canonicalWhiteningFactor, U₀, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_conjTranspose]
    _ = U₀ * ((Matrix.diagonal fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))ᴴ *
            Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))) * U₀ᴴ := by
            simp only [Matrix.mul_assoc]
    _ = U₀ * Matrix.diagonal (fun i : Fin N => (hH.eigenvalues i : ℂ)) * U₀ᴴ := by
            rw [hdiag]
    _ = G := by
            have hst := hH.spectral_theorem.symm
            rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at hst
            simpa [U₀, G, Function.comp_def] using hst

/-- Whitened finite completeness and trace formula (bridging Castro Eqs. 41–44,
`ExtraJordanNormalForm.corthogonalMatrix`, and `CastroThetaScalingBridge.kronecker`):
for any whitening factor `C` with `Cᴴ * C = G`, `W := C * castroGramSchmidtMatrix S`
is unitary (`Wᴴ * W = 1` and `W * Wᴴ = 1`), satisfies the rank-1 projector sum
`∑ n, W i n * star (W j n) = if i = j then 1 else 0`, has `Matrix.trace (W * Wᴴ) = N`,
and satisfies `ExtraJordanNormalForm.corthogonalInverse W * W = 1`. -/
theorem castroGramSchmidt_whitened_completeness {N : ℕ} (S : CastroFiniteGramSystem N)
    (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : Cᴴ * C = castroGramMatrix N S.k S.ell S.lambdas) :
    let W := C * castroGramSchmidtMatrix S
    Wᴴ * W = 1 ∧
      W * Wᴴ = 1 ∧
      Matrix.trace (W * Wᴴ) = (N : ℂ) ∧
      (∀ i j : Fin N,
        (∑ n : Fin N, W i n * star (W j n)) =
          (CastroThetaScalingBridge.kronecker i j : ℂ)) ∧
      InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalInverse W * W = 1 := by
  intro W
  have hWhW : Wᴴ * W = 1 := by
    calc
      Wᴴ * W = ((castroGramSchmidtMatrix S)ᴴ * Cᴴ) * (C * castroGramSchmidtMatrix S) := by
        simp [W, Matrix.conjTranspose_mul]
      _ = (castroGramSchmidtMatrix S)ᴴ * (Cᴴ * C) * castroGramSchmidtMatrix S := by
        simp [Matrix.mul_assoc]
      _ = (castroGramSchmidtMatrix S)ᴴ * castroGramMatrix N S.k S.ell S.lambdas *
            castroGramSchmidtMatrix S := by
        rw [hC]
      _ = 1 := castroGramSchmidtMatrix_orthonormal S
  have hWWh : W * Wᴴ = 1 := _root_.mul_eq_one_comm.mp hWhW
  have htr : Matrix.trace (W * Wᴴ) = (N : ℂ) := by
    rw [hWWh, Matrix.trace_one, Fintype.card_fin]
  have hproj : ∀ i j : Fin N,
      (∑ n : Fin N, W i n * star (W j n)) =
        (CastroThetaScalingBridge.kronecker i j : ℂ) := by
    intro i j
    have hij := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hWWh
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      CastroThetaScalingBridge.kronecker] at hij ⊢
    by_cases hij' : i = j <;> simp [hij'] at hij ⊢ <;> exact hij
  have hcorth :
      InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalMatrix W := by
    constructor
    · intro i j hij
      have hij' := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hWhW
      simpa [InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.cDot,
        dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hij] using hij'
    · intro i
      have hii := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i i) hWhW
      have heq :
          InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.cDot
              (fun k => W k i) (fun k => W k i) = 1 := by
        simpa [InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.cDot,
          dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hii
      rw [heq]
      exact one_ne_zero
  exact ⟨hWhW, hWWh, htr, hproj,
    InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.ExtraJordanNormalForm.corthogonalInverse_mul hcorth⟩

/-! ## Section 5: Non-Commutativity Witnesses (T16 Compliance) -/

/-- Explicit `2 × 2` Pauli-X matrix over `ℂ`. -/
def pauliX2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Explicit `2 × 2` Pauli-Z matrix over `ℂ`. -/
def pauliZ2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Concrete non-commutativity of `Matrix (Fin 2) (Fin 2) ℂ`: `pauliX2 * pauliZ2 ≠ pauliZ2 * pauliX2`. -/
theorem pauliX2_mul_pauliZ2_ne : pauliX2 * pauliZ2 ≠ pauliZ2 * pauliX2 := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [pauliX2, pauliZ2, Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- Explicit existential non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem complex_matrix2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨pauliX2, pauliZ2, pauliX2_mul_pauliZ2_ne⟩

/-- Generic non-commutativity witness for `Matrix (Fin N) (Fin N) ℂ` whenever `2 ≤ N`. -/
theorem complex_matrixN_noncommutative {N : ℕ} (hN : 2 ≤ N) :
    ∃ A B : Matrix (Fin N) (Fin N) ℂ, A * B ≠ B * A := by
  have h0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have h1 : 1 < N := lt_of_lt_of_le (by norm_num) hN
  let i0 : Fin N := ⟨0, h0⟩
  let i1 : Fin N := ⟨1, h1⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    norm_num [i0, i1] at this
  let A : Matrix (Fin N) (Fin N) ℂ := Matrix.single i0 i1 (1 : ℂ)
  let B : Matrix (Fin N) (Fin N) ℂ := Matrix.single i0 i0 (1 : ℂ)
  refine ⟨A, B, ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i0 i1) h
  have hAB : (A * B) i0 i1 = 0 := by
    simp [A, B, Matrix.mul_apply, Matrix.single_apply, hi01]
  have hBA : (B * A) i0 i1 = 1 := by
    simp [A, B, Matrix.mul_apply, Matrix.single_apply]
  rw [hAB, hBA] at h01
  norm_num at h01

end InfoGeometry.Arithmetic.CastroThetaGramSchmidt

end
