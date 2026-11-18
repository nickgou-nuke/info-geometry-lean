/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.RealMatrixGibbs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith

/-! # A reversible Carnot cycle of real matrix Gibbs states

The isothermal heat and work currents are the ordered matrix traces
`Tr(rho' H)` and `Tr(rho H')`. Their first law and entropy differential are
derived from the full matrix Gibbs calculus. Integral readbacks justify the
endpoint budgets used by the four-stroke cycle.

Two arbitrary self-adjoint Hamiltonians specify the hot isotherm endpoints.
The cold endpoints are their scalar multiples. Simultaneously dividing beta
by that scale preserves the complete density on each connecting adiabat.
The two hot Hamiltonians need not commute. No dissipative equation, finite-time
engine, spacetime interpretation, or Gromov--Witten identification is assumed.
-/

noncomputable section

namespace InfoGeometry.Thermo.RealMatrixCarnot

open MeasureTheory RealMatrixGibbs
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Interval

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℝ

/-- Inverse temperature times the negative Hamiltonian. -/
def exponent (β : ℝ) (H : Mat) : Mat := (-β) • H

def state (β : ℝ) (H : Mat) : Mat := density (exponent β H)

def stateEntropy (β : ℝ) (H : Mat) : ℝ := entropy (exponent β H)

def internalEnergy (β : ℝ) (H : Mat) : ℝ := expectation (exponent β H) H

theorem exponent_selfAdjoint (β : ℝ) (H : Mat) (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (exponent β H) := by
  rw [isSelfAdjoint_iff]
  simp [exponent, star_smul, hH.star_eq]

/-- The normalized Gibbs curve is differentiable whenever its Hamiltonian is. -/
theorem differentiableAt_state_curve [Nonempty n]
    (β : ℝ) (H : ℝ → Mat) (t : ℝ)
    (hself : IsSelfAdjoint (H t)) (hH : DifferentiableAt ℝ H t) :
    DifferentiableAt ℝ (fun s => state β (H s)) t :=
  (differentiableAt_density (exponent β (H t))
    (partition_pos _ (exponent_selfAdjoint β (H t) hself)).ne').comp t
      (hH.const_smul (-β))

/-- Product differentiation is the matrix first law. Both currents retain
their ordered noncommutative products. -/
theorem hasDerivAt_internalEnergy_curve
    (β : ℝ) (H : ℝ → Mat) (Hdot R : Mat) (t : ℝ)
    (hH : HasDerivAt H Hdot t)
    (hR : HasDerivAt (fun s => state β (H s)) R t) :
    HasDerivAt (fun s => internalEnergy β (H s))
      (Matrix.trace (R * H t) + Matrix.trace (state β (H t) * Hdot)) t := by
  have h := traceCLM.hasFDerivAt.comp_hasDerivAt t (hR.mul hH)
  simpa only [Function.comp_def, Pi.mul_apply, internalEnergy, expectation, state, traceCLM_apply,
    Matrix.trace_add] using h

/-- Reversible isothermal heat equals temperature times the actual entropy
differential, even when `Hdot` does not commute with `H t`. -/
theorem hasDerivAt_stateEntropy_curve [Nonempty n]
    (β : ℝ) (H : ℝ → Mat) (Hdot R : Mat) (t : ℝ)
    (hself : ∀ s, IsSelfAdjoint (H s))
    (hH : HasDerivAt H Hdot t)
    (hR : HasDerivAt (fun s => state β (H s)) R t) :
    HasDerivAt (fun s => stateEntropy β (H s))
      (β * Matrix.trace (R * H t)) t := by
  have h := hasDerivAt_entropy_curve (fun s => exponent β (H s))
    ((-β) • Hdot) R t (fun s => exponent_selfAdjoint β (H s) (hself s))
    (hH.const_smul (-β)) hR
  simpa only [stateEntropy, exponent, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, neg_mul, neg_neg] using h

/-- The heat endpoint formula is a consequence of the proved entropy
derivative and the native fundamental theorem of calculus. -/
theorem isothermal_heat_integral [Nonempty n]
    (β : ℝ) (H Hdot R : ℝ → Mat) (a b : ℝ)
    (hself : ∀ t, IsSelfAdjoint (H t))
    (hH : ∀ t ∈ Set.uIcc a b, HasDerivAt H (Hdot t) t)
    (hR : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => state β (H s)) (R t) t)
    (hheat : IntervalIntegrable (fun t => Matrix.trace (R t * H t)) volume a b) :
    β * (∫ t in a..b, Matrix.trace (R t * H t)) =
      stateEntropy β (H b) - stateEntropy β (H a) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_stateEntropy_curve β H (Hdot t) (R t) t
      hself (hH t ht) (hR t ht)) (hheat.const_mul β)
  simpa only [intervalIntegral.integral_const_mul] using hFTC

/-- Integrated first law with independently specified heat and work currents. -/
theorem isothermal_firstLaw_integral
    (β : ℝ) (H Hdot R : ℝ → Mat) (a b : ℝ)
    (hH : ∀ t ∈ Set.uIcc a b, HasDerivAt H (Hdot t) t)
    (hR : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => state β (H s)) (R t) t)
    (hheat : IntervalIntegrable (fun t => Matrix.trace (R t * H t)) volume a b)
    (hwork : IntervalIntegrable
      (fun t => Matrix.trace (state β (H t) * Hdot t)) volume a b) :
    (∫ t in a..b, Matrix.trace (R t * H t)) +
        (∫ t in a..b, Matrix.trace (state β (H t) * Hdot t)) =
      internalEnergy β (H b) - internalEnergy β (H a) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_internalEnergy_curve β H (Hdot t) (R t) t
      (hH t ht) (hR t ht)) (hheat.add hwork)
  rwa [intervalIntegral.integral_add hheat hwork] at hFTC

/-! ## Constructed reciprocal-scale adiabats -/

def scaleSegment (a b t : ℝ) : ℝ := a + t * (b - a)

@[simp] theorem scaleSegment_zero (a b : ℝ) : scaleSegment a b 0 = a := by
  simp [scaleSegment]

@[simp] theorem scaleSegment_one (a b : ℝ) : scaleSegment a b 1 = b := by
  dsimp [scaleSegment]
  ring

theorem scaleSegment_pos {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < scaleSegment a b t := by
  by_cases h : a ≤ b
  · have hprod := mul_nonneg ht.1 (sub_nonneg.mpr h)
    dsimp [scaleSegment]
    linarith
  · have hdiff : 0 ≤ (1 - t) * (a - b) :=
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (lt_of_not_ge h).le)
    dsimp [scaleSegment]
    nlinarith

theorem state_scaling_segment (H : Mat) (β a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    state (β / scaleSegment a b t) (scaleSegment a b t • H) = state β H :=
  density_reciprocal_scale H β (scaleSegment a b t)
    (scaleSegment_pos ha hb ht).ne'

theorem entropy_scaling_segment (H : Mat) (β a b t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    stateEntropy (β / scaleSegment a b t) (scaleSegment a b t • H) =
      stateEntropy β H :=
  entropy_reciprocal_scale H β (scaleSegment a b t)
    (scaleSegment_pos ha hb ht).ne'

/-- Actual derivative of the changing Hamiltonian on a scale segment. -/
theorem hasDerivAt_scaledHamiltonian (H : Mat) (a b t : ℝ) :
    HasDerivAt (fun s => scaleSegment a b s • H) ((b - a) • H) t := by
  simpa only [scaleSegment, zero_add, one_mul] using
    ((hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const (b - a))).smul_const H

/-- Work done on the system on the constant-density scale segment. -/
def scalingWorkOn (β a b : ℝ) (H : Mat) : ℝ :=
  (b - a) * internalEnergy β H

theorem scalingWorkOn_integral (β a b : ℝ) (H : Mat) :
    (∫ _t in (0 : ℝ)..1,
      Matrix.trace (state β H * ((b - a) • H))) = scalingWorkOn β a b H := by
  simp [Matrix.mul_smul, Matrix.trace_smul, scalingWorkOn, internalEnergy,
    expectation, state]

/-! ## Four strokes and the Carnot efficiency -/

/-- Reversible heat absorbed on the hot isotherm. The preceding integral
theorem supplies the analytic realization under its derivative hypotheses. -/
def hotHeat (β : ℝ) (H₀ H₁ : Mat) : ℝ :=
  (stateEntropy β H₁ - stateEntropy β H₀) / β

/-- Signed heat on the reversed cold isotherm, using its actual scaled
Hamiltonians and cold inverse temperature. -/
def coldHeat (β c : ℝ) (H₀ H₁ : Mat) : ℝ :=
  (stateEntropy (β / c) (c • H₀) - stateEntropy (β / c) (c • H₁)) / (β / c)

def hotWorkOn (β : ℝ) (H₀ H₁ : Mat) : ℝ :=
  internalEnergy β H₁ - internalEnergy β H₀ - hotHeat β H₀ H₁

def coldWorkOn (β c : ℝ) (H₀ H₁ : Mat) : ℝ :=
  internalEnergy (β / c) (c • H₀) - internalEnergy (β / c) (c • H₁) -
    coldHeat β c H₀ H₁

/-- Work output is minus the work done on the system during all four strokes. -/
def cycleWork (β c : ℝ) (H₀ H₁ : Mat) : ℝ :=
  -(hotWorkOn β H₀ H₁ + scalingWorkOn β 1 c H₁ +
      coldWorkOn β c H₀ H₁ + scalingWorkOn β c 1 H₀)

def efficiency (β c : ℝ) (H₀ H₁ : Mat) : ℝ :=
  cycleWork β c H₀ H₁ / hotHeat β H₀ H₁

theorem state_cold_corner (β c : ℝ) (H : Mat) (hc : c ≠ 0) :
    state (β / c) (c • H) = state β H :=
  density_reciprocal_scale H β c hc

theorem entropy_cold_corner (β c : ℝ) (H : Mat) (hc : c ≠ 0) :
    stateEntropy (β / c) (c • H) = stateEntropy β H :=
  entropy_reciprocal_scale H β c hc

theorem internalEnergy_cold_corner (β c : ℝ) (H : Mat) (hc : c ≠ 0) :
    internalEnergy (β / c) (c • H) = c * internalEnergy β H :=
  expectation_reciprocal_scale H β c hc

private theorem reversed_entropy_heat (S₀ S₁ β c : ℝ) (hβ : β ≠ 0)
    (hc : c ≠ 0) : (S₀ - S₁) / (β / c) = -c * ((S₁ - S₀) / β) := by
  field_simp [hβ, hc]
  ring

theorem coldHeat_eq_neg_scale_hotHeat (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0) :
    coldHeat β c H₀ H₁ = -c * hotHeat β H₀ H₁ := by
  rw [coldHeat, entropy_cold_corner β c H₀ hc,
    entropy_cold_corner β c H₁ hc]
  exact reversed_entropy_heat _ _ β c hβ hc

private theorem four_stroke_work_sum (U₀ U₁ Qh Qc c : ℝ) :
    -((U₁ - U₀ - Qh) + (c - 1) * U₁ +
        (c * U₀ - c * U₁ - Qc) + (1 - c) * U₀) = Qh + Qc := by
  ring

/-- All internal-energy changes telescope around the four-stroke cycle. -/
theorem cycleWork_eq_heat_sum (β c : ℝ) (H₀ H₁ : Mat) (hc : c ≠ 0) :
    cycleWork β c H₀ H₁ = hotHeat β H₀ H₁ + coldHeat β c H₀ H₁ := by
  rw [cycleWork, hotWorkOn, coldWorkOn,
    internalEnergy_cold_corner β c H₀ hc, internalEnergy_cold_corner β c H₁ hc]
  exact four_stroke_work_sum _ _ _ _ c

theorem cycleWork_eq_one_sub_scale_mul_hotHeat (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0) :
    cycleWork β c H₀ H₁ = (1 - c) * hotHeat β H₀ H₁ := by
  rw [cycleWork_eq_heat_sum β c H₀ H₁ hc,
    coldHeat_eq_neg_scale_hotHeat β c H₀ H₁ hβ hc, sub_mul, one_mul, neg_mul]
  abel

/-- Carnot efficiency for a nonzero entropy stroke on the full real matrix
state carrier. The scale `c` is the cold/hot temperature ratio. -/
theorem efficiency_eq_one_sub_scale (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (hS : stateEntropy β H₁ ≠ stateEntropy β H₀) :
    efficiency β c H₀ H₁ = 1 - c := by
  rw [efficiency, cycleWork_eq_one_sub_scale_mul_hotHeat β c H₀ H₁ hβ hc,
    mul_div_cancel_right₀ _ (div_ne_zero (sub_ne_zero.mpr hS) hβ)]

theorem hotHeat_pos (β : ℝ) (H₀ H₁ : Mat) (hβ : 0 < β)
    (hS : stateEntropy β H₀ < stateEntropy β H₁) : 0 < hotHeat β H₀ H₁ :=
  div_pos (sub_pos.mpr hS) hβ

theorem cycleWork_pos (β c : ℝ) (H₀ H₁ : Mat) (hβ : 0 < β)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hS : stateEntropy β H₀ < stateEntropy β H₁) : 0 < cycleWork β c H₀ H₁ := by
  rw [cycleWork_eq_one_sub_scale_mul_hotHeat β c H₀ H₁ hβ.ne' hc.1.ne']
  exact mul_pos (sub_pos.mpr hc.2) (hotHeat_pos β H₀ H₁ hβ hS)

/-! ## Native smooth isotherms realizing the endpoint budgets -/

/-- The hot Hamiltonian path retains both arbitrary endpoint matrices. -/
def affineHamiltonian (H₀ H₁ : Mat) (t : ℝ) : Mat := H₀ + t • (H₁ - H₀)

@[simp] theorem affineHamiltonian_zero (H₀ H₁ : Mat) :
    affineHamiltonian H₀ H₁ 0 = H₀ := by simp [affineHamiltonian]

@[simp] theorem affineHamiltonian_one (H₀ H₁ : Mat) :
    affineHamiltonian H₀ H₁ 1 = H₁ := by
  simp only [affineHamiltonian, one_smul]
  abel

theorem affineHamiltonian_selfAdjoint (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) (t : ℝ) :
    IsSelfAdjoint (affineHamiltonian H₀ H₁ t) := by
  rw [isSelfAdjoint_iff]
  simp [affineHamiltonian, star_add, star_smul, star_sub, h₀.star_eq, h₁.star_eq]

theorem contDiff_affineHamiltonian (H₀ H₁ : Mat) :
    ContDiff ℝ 1 (affineHamiltonian H₀ H₁) :=
  contDiff_const.add (contDiff_id.smul_const (H₁ - H₀))

theorem hasDerivAt_affineHamiltonian (H₀ H₁ : Mat) (t : ℝ) :
    HasDerivAt (affineHamiltonian H₀ H₁) (H₁ - H₀) t := by
  simpa only [zero_add, one_smul] using
    (hasDerivAt_const t H₀).add ((hasDerivAt_id t).smul_const (H₁ - H₀))

/-- The actual Gibbs state along the affine Hamiltonian is continuously
differentiable. Positivity discharges every inverse-partition domain premise. -/
theorem contDiff_state_affine [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    ContDiff ℝ 1 (fun t => state β (affineHamiltonian H₀ H₁ t)) := by
  have hK : ContDiff ℝ 1 (fun t => exponent β (affineHamiltonian H₀ H₁ t)) :=
    (contDiff_affineHamiltonian H₀ H₁).const_smul (-β)
  have hexp : ContDiff ℝ 1 (NormedSpace.exp : Mat → Mat) := by
    rw [contDiff_iff_contDiffAt]
    intro K
    exact (NormedSpace.exp_analytic (𝕂 := ℝ) K).contDiffAt
  have hweight := hexp.comp hK
  have hZ : ContDiff ℝ 1
      (fun t => partition (exponent β (affineHamiltonian H₀ H₁ t))) :=
    traceCLM.contDiff.comp hweight
  have hZne : ∀ t, partition (exponent β (affineHamiltonian H₀ H₁ t)) ≠ 0 := by
    intro t
    exact (partition_pos _ (exponent_selfAdjoint β _
      (affineHamiltonian_selfAdjoint H₀ H₁ h₀ h₁ t))).ne'
  exact (hZ.inv hZne).smul hweight

/-- Heat current uses the genuine native derivative of the constructed state. -/
def affineHeatCurrent (β : ℝ) (H₀ H₁ : Mat) (t : ℝ) : ℝ :=
  Matrix.trace
    (deriv (fun s => state β (affineHamiltonian H₀ H₁ s)) t *
      affineHamiltonian H₀ H₁ t)

/-- Work current uses the genuine derivative of the affine Hamiltonian. -/
def affineWorkCurrent (β : ℝ) (H₀ H₁ : Mat) (t : ℝ) : ℝ :=
  Matrix.trace (state β (affineHamiltonian H₀ H₁ t) * (H₁ - H₀))

theorem continuous_affineHeatCurrent [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Continuous (affineHeatCurrent β H₀ H₁) :=
  traceCLM.continuous.comp
    ((contDiff_state_affine β H₀ H₁ h₀ h₁).continuous_deriv_one.mul
      (contDiff_affineHamiltonian H₀ H₁).continuous)

theorem continuous_affineWorkCurrent [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    Continuous (affineWorkCurrent β H₀ H₁) :=
  traceCLM.continuous.comp
    ((contDiff_state_affine β H₀ H₁ h₀ h₁).continuous.mul continuous_const)

/-- The hot heat budget is the integral of the constructed noncommutative
matrix heat current. No derivative or integrability witness is left to supply. -/
theorem affineHeat_integral_eq_hotHeat [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    (∫ t in (0 : ℝ)..1, affineHeatCurrent β H₀ H₁ t) = hotHeat β H₀ H₁ := by
  have hFTC := isothermal_heat_integral β (affineHamiltonian H₀ H₁)
    (fun _ => H₁ - H₀) (deriv (fun t => state β (affineHamiltonian H₀ H₁ t))) 0 1
    (affineHamiltonian_selfAdjoint H₀ H₁ h₀ h₁)
    (fun t _ => hasDerivAt_affineHamiltonian H₀ H₁ t)
    (fun t _ => ((contDiff_state_affine β H₀ H₁ h₀ h₁).differentiable_one t).hasDerivAt)
    ((continuous_affineHeatCurrent β H₀ H₁ h₀ h₁).intervalIntegrable 0 1)
  change _ = (_ - _) / β
  apply (eq_div_iff hβ).mpr
  simpa only [affineHamiltonian_zero, affineHamiltonian_one, mul_comm] using hFTC

/-- The isothermal work budget is the integral of the actual work current. -/
theorem affineWork_integral_eq_hotWorkOn [Nonempty n] (β : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    (∫ t in (0 : ℝ)..1, affineWorkCurrent β H₀ H₁ t) = hotWorkOn β H₀ H₁ := by
  have hFTC := isothermal_firstLaw_integral β (affineHamiltonian H₀ H₁)
    (fun _ => H₁ - H₀) (deriv (fun t => state β (affineHamiltonian H₀ H₁ t))) 0 1
    (fun t _ => hasDerivAt_affineHamiltonian H₀ H₁ t)
    (fun t _ => ((contDiff_state_affine β H₀ H₁ h₀ h₁).differentiable_one t).hasDerivAt)
    ((continuous_affineHeatCurrent β H₀ H₁ h₀ h₁).intervalIntegrable 0 1)
    ((continuous_affineWorkCurrent β H₀ H₁ h₀ h₁).intervalIntegrable 0 1)
  change (∫ t in (0 : ℝ)..1, affineHeatCurrent β H₀ H₁ t) +
      (∫ t in (0 : ℝ)..1, affineWorkCurrent β H₀ H₁ t) = _ at hFTC
  rw [affineHeat_integral_eq_hotHeat β H₀ H₁ hβ h₀ h₁,
    affineHamiltonian_one, affineHamiltonian_zero] at hFTC
  unfold hotWorkOn
  rw [← hFTC]
  abel

/-- The reversed cold isotherm has the declared signed heat. This is the
same construction at its scaled endpoints and inverse temperature. -/
theorem affineHeat_integral_eq_coldHeat [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    (∫ t in (0 : ℝ)..1, affineHeatCurrent (β / c) (c • H₁) (c • H₀) t) =
      coldHeat β c H₀ H₁ := by
  apply affineHeat_integral_eq_hotHeat (β / c) (c • H₁) (c • H₀) (div_ne_zero hβ hc)
  · rw [isSelfAdjoint_iff]
    simp [star_smul, h₁.star_eq]
  · rw [isSelfAdjoint_iff]
    simp [star_smul, h₀.star_eq]

theorem affineWork_integral_eq_coldWorkOn [Nonempty n] (β c : ℝ) (H₀ H₁ : Mat)
    (hβ : β ≠ 0) (hc : c ≠ 0)
    (h₀ : IsSelfAdjoint H₀) (h₁ : IsSelfAdjoint H₁) :
    (∫ t in (0 : ℝ)..1, affineWorkCurrent (β / c) (c • H₁) (c • H₀) t) =
      coldWorkOn β c H₀ H₁ := by
  apply affineWork_integral_eq_hotWorkOn (β / c) (c • H₁) (c • H₀) (div_ne_zero hβ hc)
  · rw [isSelfAdjoint_iff]
    simp [star_smul, h₁.star_eq]
  · rw [isSelfAdjoint_iff]
    simp [star_smul, h₀.star_eq]

end InfoGeometry.Thermo.RealMatrixCarnot
