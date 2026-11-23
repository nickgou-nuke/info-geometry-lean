/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge

/-!
# InfoGeometry.Arithmetic.TwoSidedHorizonMellinCutoffObstruction

Constructive formalization of the two-sided horizon vs. one-sided cutoff dichotomy
for `ERRATA R2` / §1.4.3 (p. 29) and §1.4.4 (`endgame.md`):

1. **One-Sided Horizon Cutoff Divergence (`1_{t > 1}` at `t = 1`)**:
   - `not_intervalIntegrable_oneSidedHorizonKernel`: `(t - 1)⁻¹` is not interval
     integrable on `[1, 2]`.
   - `integral_oneSidedHorizonCutoff` and `integral_scaledOneSidedHorizonCutoff`:
     `∫ t in (1 + ε)..2, c * (t - 1)⁻¹ = c * Real.log (1 / ε)`.
   - `weightedOneSidedHorizonCutoff_lowerBound` and `oneSidedHorizonCutoff_unbounded`:
     any integrand bounded below on `[1 + ε, 2]` by `c * (t - 1)⁻¹` (`c > 0`) grows
     without bound as `ε → 0⁺`, refuting uniform cutoff boundedness.
2. **Two-Sided Symmetric Horizon Cancellation (`t ↔ t⁻¹`, `τ = log t ↔ -τ`)**:
   - `twoSidedLogHorizonPrincipalValue_eq_zero`: symmetric principal-value integrals
     on `[-δ, -ε] ∪ [ε, δ]` cancel identically to `0`.
   - `archimedeanHorizonKernel_inv`: `Real.sqrt t / (t - 1)` is odd under `t ↦ t⁻¹`
     (`archimedeanHorizonKernel t⁻¹ = -archimedeanHorizonKernel t`), so pairing any
     inversion-even state `Φ t⁻¹ = Φ t` produces exact horizon cancellation.
   - `twoSided_antisymmetrized_horizonPole_removable`: antisymmetrizing `t - t⁻¹`
     across `t = 1` yields `(t - t⁻¹) / (t - 1) = 1 + t⁻¹`, eliminating the `t = 1` pole.
3. **§1.4.4 Prime-Power Sign Check (`endgame.md`, p. 29)**:
   - `sec144_vonMangoldt_LSeries_at_five_halves`: the R1 Maurer–Cartan Dirichlet
     series at `s = 5 / 2` equals `-deriv riemannZeta (5 / 2) / riemannZeta (5 / 2)`
     (opposite sign to the printed `+ζ'(5/2)/ζ(5/2)`).
-/

noncomputable section

open MeasureTheory Set
open scoped LSeries.notation

namespace InfoGeometry.Arithmetic.TwoSidedHorizonMellinCutoffObstruction

open InfoGeometry.Arithmetic.MaurerCartanVonMangoldtBridge
open InfoGeometry.OperatorAlgebra.MaurerCartanTower

/-- The one-sided archimedean horizon kernel `(t - 1)⁻¹` is not interval integrable
on `[1, 2]`, confirming the logarithmic singularity at the `t = 1` cutoff horizon. -/
theorem not_intervalIntegrable_oneSidedHorizonKernel :
    ¬ IntervalIntegrable (fun t : ℝ ↦ (t - 1)⁻¹) volume 1 2 := by
  intro hint
  have hmem := (intervalIntegrable_sub_inv_iff (a := 1) (b := 2) (c := 1)).mp hint
  rcases hmem with h12 | hnotin
  · norm_num at h12
  · apply hnotin
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact ⟨le_rfl, by norm_num⟩

/-- Exact truncated one-sided horizon integral on `[1 + ε, 2]`:
`∫ t in (1 + ε)..2, (t - 1)⁻¹ = Real.log (1 / ε)`. -/
theorem integral_oneSidedHorizonCutoff {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (1 + ε)..2, (t - 1)⁻¹) = Real.log (1 / ε) := by
  rw [intervalIntegral.integral_comp_sub_right (a := 1 + ε) (b := 2) (f := fun x : ℝ ↦ x⁻¹) 1]
  rw [show (1 + ε - 1 : ℝ) = ε by ring, show (2 - 1 : ℝ) = 1 by ring]
  exact integral_inv_of_pos hε one_pos

/-- Exact scaled one-sided horizon cutoff integral `∫ t in (1 + ε)..2, c * (t - 1)⁻¹`. -/
theorem integral_scaledOneSidedHorizonCutoff (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∫ t in (1 + ε)..2, c * (t - 1)⁻¹) = c * Real.log (1 / ε) := by
  rw [intervalIntegral.integral_const_mul, integral_oneSidedHorizonCutoff hε]

/-- Any interval-integrable archimedean integrand `g` bounded below by `c * (t - 1)⁻¹`
on `[1 + ε, 2]` inherits the explicit logarithmic lower bound `c * log (1 / ε)`. -/
theorem weightedOneSidedHorizonCutoff_lowerBound {g : ℝ → ℝ} {c ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hg : IntervalIntegrable g volume (1 + ε) 2)
    (hlow : ∀ t ∈ Set.Icc (1 + ε) 2, c * (t - 1)⁻¹ ≤ g t) :
    c * Real.log (1 / ε) ≤ ∫ t in (1 + ε)..2, g t := by
  have hle : 1 + ε ≤ 2 := by linarith [hε1]
  have hcont : ContinuousOn (fun t : ℝ ↦ c * (t - 1)⁻¹) (Set.uIcc (1 + ε) 2) := by
    refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ ?_)
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    change t - 1 ≠ 0
    linarith [ht.1, hε]
  calc
    c * Real.log (1 / ε) = ∫ t in (1 + ε)..2, c * (t - 1)⁻¹ :=
      (integral_scaledOneSidedHorizonCutoff c hε).symm
    _ ≤ ∫ t in (1 + ε)..2, g t :=
      intervalIntegral.integral_mono_on hle hcont.intervalIntegrable hg hlow

/-- Unboundedness of the one-sided cutoff as `ε → 0⁺`: for every positive scale `c > 0`
and every bound `M : ℝ`, there exists `ε ∈ (0, 1)` with `∫ (1 + ε)..2, c * (t - 1)⁻¹ > M`. -/
theorem oneSidedHorizonCutoff_unbounded {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∃ ε ∈ Set.Ioo (0 : ℝ) 1, M < ∫ t in (1 + ε)..2, c * (t - 1)⁻¹ := by
  let ε : ℝ := Real.exp (-(|M| / c + 1))
  have hpos_arg : 0 < |M| / c + 1 :=
    add_pos_of_nonneg_of_pos (div_nonneg (abs_nonneg M) hc.le) one_pos
  have hε : 0 < ε := Real.exp_pos _
  have hε_lt : ε < 1 := Real.exp_lt_one_iff.mpr (by linarith [hpos_arg])
  refine ⟨ε, ⟨hε, hε_lt⟩, ?_⟩
  rw [integral_scaledOneSidedHorizonCutoff c hε, one_div, Real.log_inv]
  dsimp [ε]
  rw [Real.log_exp, neg_neg]
  have hmul : c * (|M| / c + 1) = |M| + c := by
    field_simp [hc.ne']
  rw [hmul]
  linarith [le_abs_self M, hc]

/-- Two-sided logarithmic principal-value cancellation around `τ = 0`:
pairing `[-R, -r]` against `[r, R]` cancels identically to `0` for all `r, R > 0`. -/
theorem twoSidedLogHorizonPrincipalValue_eq_zero (c : ℝ) {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) :
    (∫ τ in (-R)..(-r), c * τ⁻¹) + (∫ τ in r..R, c * τ⁻¹) = 0 := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_inv_of_neg (neg_lt_zero.mpr hR) (neg_lt_zero.mpr hr), integral_inv_of_pos hr hR]
  rw [neg_div_neg_eq, ← mul_add]
  have hprod : (r / R) * (R / r) = 1 := by
    field_simp [hr.ne', hR.ne']
  rw [← Real.log_mul (div_pos hr hR).ne' (div_pos hR hr).ne', hprod, Real.log_one, mul_zero]

/-- Multiplicative Weil–Rindler archimedean horizon kernel `Real.sqrt t / (t - 1)`. -/
def archimedeanHorizonKernel (t : ℝ) : ℝ :=
  Real.sqrt t / (t - 1)

/-- Exact UV↔IR inversion antisymmetry across the `t = 1` horizon:
`archimedeanHorizonKernel t⁻¹ = -archimedeanHorizonKernel t` for all `t > 0`. -/
theorem archimedeanHorizonKernel_inv {t : ℝ} (ht : 0 < t) :
    archimedeanHorizonKernel t⁻¹ = -archimedeanHorizonKernel t := by
  by_cases ht1 : t = 1
  · subst ht1
    simp [archimedeanHorizonKernel]
  · have ht0 : t ≠ 0 := ht.ne'
    have hsub1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    have hsub_inv : t⁻¹ - 1 ≠ 0 := by
      intro h
      apply hsub1
      have h' : t⁻¹ = 1 := sub_eq_zero.mp h
      exact sub_eq_zero.mpr (inv_eq_one.mp h')
    have hsq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have hsq_ne : Real.sqrt t ≠ 0 := hsq_pos.ne'
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    unfold archimedeanHorizonKernel
    rw [Real.sqrt_inv]
    field_simp [hsq_ne, ht0, hsub1, hsub_inv]
    rw [hsq]
    ring

/-- Pointwise cancellation when pairing an inversion-even test state `Φ t⁻¹ = Φ t`
with the multiplicative archimedean horizon kernel at `(t, t⁻¹)`. -/
theorem twoSided_evenState_archimedeanHorizon_cancels (Φ : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (heven : Φ t⁻¹ = Φ t) :
    Φ t * archimedeanHorizonKernel t + Φ t⁻¹ * archimedeanHorizonKernel t⁻¹ = 0 := by
  rw [heven, archimedeanHorizonKernel_inv ht]
  ring

/-- Antisymmetrizing `t - t⁻¹` removes the simple `t = 1` pole algebraically on `t ≠ 0, t ≠ 1`. -/
theorem twoSided_antisymmetrized_horizonPole_removable {t : ℝ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (t - t⁻¹) / (t - 1) = 1 + t⁻¹ := by
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  field_simp [ht0, hsub]
  ring

local instance instDirichletIsScalarTower :
    IsScalarTower ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

local instance instDirichletSMulCommClass :
    SMulCommClass ℝ (ArithmeticFunction ℝ) (ArithmeticFunction ℝ) :=
  ⟨fun r f g => by
    ext n
    simp [ArithmeticFunction.mul_apply, Finset.mul_sum]⟩

/-- Exact §1.4.4 sign verification (`endgame.md`, p. 29) at `s = 5 / 2`:
the Dirichlet series of `actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)]` equals
`-deriv riemannZeta (5 / 2) / riemannZeta (5 / 2)`. -/
theorem sec144_vonMangoldt_LSeries_at_five_halves :
    L ↗(actionThetaL dirichletLogLane zetaUnit ![(1 : ℝ)]) (5 / 2 : ℂ) =
      -deriv riemannZeta (5 / 2 : ℂ) / riemannZeta (5 / 2 : ℂ) := by
  have hs : (1 : ℝ) < (5 / 2 : ℂ).re := by norm_num
  exact (maurerCartan_zetaLogDerivative_mobius_synthesis hs 1).2.1

end InfoGeometry.Arithmetic.TwoSidedHorizonMellinCutoffObstruction
