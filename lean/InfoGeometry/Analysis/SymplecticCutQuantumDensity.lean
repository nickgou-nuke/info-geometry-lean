/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.LogisticBetaTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The exact real quantum cut density for `C³`

For real parameters `a`, `b`, `d`, the function in §3, equations (3.12)--(3.15),
of Cassia, Longhi and Zabzine, *Symplectic Cuts and Open/Closed Strings I*, is

`Γ(a) Γ(b + d) exp(d c) / (1 + exp c)^(b + d)`.

This module proves its actual real derivative, the first-order
Picard--Fuchs equation, smoothness, positivity for positive parameters,
phase reflection, Bochner integrability, and the Gamma-product total
integral.  The integral is obtained by transporting the native beta
distribution through the existing real logistic chart.

These are the exact real analytic identities of the displayed period.
They do not assert a construction of Gromov--Witten invariants, a quantum
symplectic quotient, or an identification with the classical cut density.
-/

noncomputable section

open MeasureTheory Set
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.LogisticBetaTransport

namespace InfoGeometry.Analysis.SymplecticCutQuantumDensity

/-- The exact real quantum cut density of §3, with
`(a, b, d) = (ε₁, ε₂, ε₃)`. -/
def quantumDensity (a b d c : ℝ) : ℝ :=
  Real.Gamma a * Real.Gamma (b + d) * Real.exp (d * c) /
    (1 + Real.exp c) ^ (b + d)

/-- The real closed Gamma volume recovered by integrating the cut level. -/
def quantumVolume (a b d : ℝ) : ℝ :=
  Real.Gamma a * Real.Gamma b * Real.Gamma d

theorem quantumDensity_eq_exp (a b d c : ℝ) :
    quantumDensity a b d c =
      Real.Gamma a * Real.Gamma (b + d) *
        Real.exp (d * c - (b + d) * Real.log (1 + Real.exp c)) := by
  unfold quantumDensity
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + Real.exp c), Real.exp_sub,
    mul_comm (Real.log (1 + Real.exp c)) (b + d)]
  ring

/-- Smoothness is in the cut coordinate and does not require positive
parameters.  Positivity is needed for normalization below. -/
theorem contDiff_quantumDensity (a b d : ℝ) :
    ContDiff ℝ ⊤ (quantumDensity a b d) := by
  have hlog : ContDiff ℝ ⊤ (fun c : ℝ => Real.log (1 + Real.exp c)) :=
    (contDiff_const.add Real.contDiff_exp).log (fun c => by positivity)
  have hlin : ContDiff ℝ ⊤ (fun c : ℝ => d * c) :=
    contDiff_const.mul contDiff_id
  have hexp : ContDiff ℝ ⊤
      (fun c : ℝ => Real.exp (d * c - (b + d) * Real.log (1 + Real.exp c))) :=
    (hlin.sub (contDiff_const.mul hlog)).exp
  have hf : quantumDensity a b d = fun c =>
      Real.Gamma a * Real.Gamma (b + d) *
        Real.exp (d * c - (b + d) * Real.log (1 + Real.exp c)) :=
    funext (quantumDensity_eq_exp a b d)
  rw [hf]
  exact contDiff_const.mul hexp

/-- The actual derivative of the exact quantum period. -/
theorem hasDerivAt_quantumDensity (a b d c : ℝ) :
    HasDerivAt (quantumDensity a b d)
      ((d - (b + d) * logistic c) * quantumDensity a b d c) c := by
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp x))
      (logistic c) c := by
    simpa only [logistic] using
      ((Real.hasDerivAt_exp c).const_add 1).log (by positivity)
  have hlin : HasDerivAt (fun x : ℝ => d * x) d c :=
    hasDerivAt_const_mul d
  have h := ((hlin.sub (hlog.const_mul (b + d))).exp).const_mul
    (Real.Gamma a * Real.Gamma (b + d))
  have hf : quantumDensity a b d = fun x =>
      Real.Gamma a * Real.Gamma (b + d) *
        Real.exp (d * x - (b + d) * Real.log (1 + Real.exp x)) :=
    funext (quantumDensity_eq_exp a b d)
  rw [hf]
  convert h using 1 <;> ring

theorem deriv_quantumDensity (a b d c : ℝ) :
    deriv (quantumDensity a b d) c =
      (d - (b + d) * logistic c) * quantumDensity a b d c :=
  (hasDerivAt_quantumDensity a b d c).deriv

/-- The real Picard--Fuchs equation `(b + ∂c)H = exp(-c)(d - ∂c)H`.
The derivative here is Mathlib's derivative of the displayed function. -/
theorem picardFuchs_quantumDensity (a b d c : ℝ) :
    b * quantumDensity a b d c + deriv (quantumDensity a b d) c =
      Real.exp (-c) *
        (d * quantumDensity a b d c - deriv (quantumDensity a b d) c) := by
  rw [deriv_quantumDensity, Real.exp_neg]
  unfold logistic
  field_simp [(Real.exp_pos c).ne',
    (show 0 < 1 + Real.exp c by positivity).ne'] <;> ring

theorem quantumDensity_pos {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (c : ℝ) : 0 < quantumDensity a b d c := by
  unfold quantumDensity
  exact div_pos
    (mul_pos (mul_pos (Real.Gamma_pos_of_pos ha)
      (Real.Gamma_pos_of_pos (add_pos hb hd))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by positivity) _)

theorem quantumVolume_pos {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) : 0 < quantumVolume a b d :=
  mul_pos (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
    (Real.Gamma_pos_of_pos hd)

/-- Reversing the cut level exchanges the second and third equivariant
parameters, as in the phase symmetry of §3. -/
theorem quantumDensity_phase_reflection (a b d c : ℝ) :
    quantumDensity a b d (-c) = quantumDensity a d b c := by
  have hc : 0 < 1 + Real.exp c := by positivity
  have hbase : 1 + Real.exp (-c) = (1 + Real.exp c) / Real.exp c := by
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos c).ne'] <;> ring
  have hlog : Real.log (1 + Real.exp (-c)) = Real.log (1 + Real.exp c) - c := by
    rw [hbase, Real.log_div hc.ne' (Real.exp_pos c).ne', Real.log_exp]
  rw [quantumDensity_eq_exp, quantumDensity_eq_exp, hlog, add_comm d b]
  congr 1
  congr 1
  ring

/-- The exact period is the closed Gamma volume times a genuine normalized
beta density in the logit coordinate.  Only the two beta shape parameters
need to be positive for this identity and the ensuing integrability. -/
theorem quantumDensity_eq_volume_mul_betaLogitDensity (a : ℝ) {b d : ℝ}
    (hb : 0 < b) (hd : 0 < d) (c : ℝ) :
    quantumDensity a b d c = quantumVolume a b d * betaLogitDensity d b c := by
  have hgb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hgd : Real.Gamma d ≠ 0 := (Real.Gamma_pos_of_pos hd).ne'
  have hgs : Real.Gamma (b + d) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos hb hd)).ne'
  have hp : (1 + Real.exp c) ^ (b + d) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity : 0 < 1 + Real.exp c) (b + d)).ne'
  rw [betaLogitDensity_eq_exp_div]
  unfold quantumDensity quantumVolume ProbabilityTheory.beta
  rw [add_comm d b]
  field_simp [hgb, hgd, hgs, hp] <;> ring

theorem integrable_quantumDensity (a : ℝ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    Integrable (quantumDensity a b d) := by
  have hf : quantumDensity a b d =
      fun c => quantumVolume a b d * betaLogitDensity d b c :=
    funext (quantumDensity_eq_volume_mul_betaLogitDensity a hb hd)
  rw [hf]
  exact (integrable_betaLogitDensity hd hb).const_mul _

/-- The whole real cut line recovers the closed Gamma volume, equation
(3.15).  All integrability is proved; there is no decay premise. -/
theorem integral_quantumDensity (a : ℝ) {b d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    (∫ c, quantumDensity a b d c) = Real.Gamma a * Real.Gamma b * Real.Gamma d := by
  calc
    (∫ c, quantumDensity a b d c) =
        ∫ c, quantumVolume a b d * betaLogitDensity d b c := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (quantumDensity_eq_volume_mul_betaLogitDensity a hb hd))
    _ = quantumVolume a b d * ∫ c, betaLogitDensity d b c :=
      integral_const_mul _ _
    _ = Real.Gamma a * Real.Gamma b * Real.Gamma d := by
      rw [integral_betaLogitDensity hd hb, mul_one]
      rfl

/-- The two genuine half-line volumes add to the closed volume for every
cut level, the analytic statement behind equation (3.18). -/
theorem integral_quantumDensity_halves (a : ℝ) {b d : ℝ} (hb : 0 < b)
    (hd : 0 < d) (c : ℝ) :
    (∫ x in Set.Iic c, quantumDensity a b d x) +
        (∫ x in Set.Ioi c, quantumDensity a b d x) =
      Real.Gamma a * Real.Gamma b * Real.Gamma d := by
  rw [← integral_quantumDensity a hb hd]
  simpa only [Set.compl_Iic] using
    integral_add_compl (s := Set.Iic c) measurableSet_Iic
      (integrable_quantumDensity a hb hd)

end InfoGeometry.Analysis.SymplecticCutQuantumDensity
