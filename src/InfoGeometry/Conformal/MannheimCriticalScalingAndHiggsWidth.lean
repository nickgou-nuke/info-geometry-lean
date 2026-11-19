/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass
import InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
import InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Mannheim Anomalous Dimension Critical Scaling and Dynamical Higgs Width

Formalizes the Johnson-Baker-Willey / Mannheim dressed fermion-bilinear anomalous dimension
`dim(psi-bar psi) = 3 + gamma` UV integrability trichotomy, the resulting critical effective
potential shape trichotomy across `-1 < gamma < 0` (single well), `gamma = -1` (finite
scale-invariant dynamical double well), and `gamma = -2` (inverted upside-down potential),
and the above-`2m`-threshold positive imaginary part / decay width of the dynamical bound-state
Higgs propagator contrasted with the identically zero width of an elementary tree-level Higgs.

## Main Declarations
- `dressedBilinearDim`, `fourFermionDim`
- `anomalous_dim_uv_integrability_trichotomy`
- `SingleWellShape`, `DoubleWellShape`, `UpsideDownShape`, `mannheimCriticalPotential`
- `mannheim_anomalous_dimension_potential_trichotomy`
- `scalarBubbleImPart`, `dynamicalHiggsComplexInvProp`, `elementaryHiggsInvProp`
- `scalarBubbleImPart_threshold_dichotomy`
- `dynamical_higgs_above_threshold_positive_width_vs_elementary_zero`
- `archMA14CriticalScalingAndHiggsWidth`
-/

noncomputable section

namespace InfoGeometry.Conformal.MannheimCriticalScalingAndHiggsWidth

open Filter MeasureTheory Set
open scoped Interval
open InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass
open InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
open InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance
open InfoGeometry.MetaCompiler

/-! ### Part 1: Dressed Bilinear Dimension & UV Integrability Trichotomy -/

/-- Dressed scaling dimension of the fermion bilinear `psi-bar psi` with anomalous dimension `gamma`. -/
def dressedBilinearDim (γ : ℝ) : ℝ := 3 + γ

/-- Scaling dimension of the four-fermion operator `(psi-bar psi)^2`. -/
def fourFermionDim (γ : ℝ) : ℝ := 2 * dressedBilinearDim γ

/-- UV integrability trichotomy of the dressed kernel `u ^ gamma` on `(1, +infty)`:
- `fourFermionDim gamma = 4 <-> gamma = -1` (renormalizable marginal scaling),
- `IntegrableOn (fun u => u ^ gamma) (Set.Ioi 1) <-> gamma < -1`,
- divergence for `-1 < gamma < 0` and at `gamma = -1` (where `u ^ (-1 : ℝ) = u⁻¹`),
- strict UV convergence at `gamma = -2` with exact improper integral `1 > 0` and
  exact cutoff integral `1 - 1 / Λ < 1` for `1 ≤ Λ`. -/
theorem anomalous_dim_uv_integrability_trichotomy :
    (∀ γ : ℝ, fourFermionDim γ = 4 ↔ γ = -1) ∧
    (∀ γ : ℝ, MeasureTheory.IntegrableOn (fun u : ℝ => u ^ γ) (Set.Ioi 1) ↔ γ < -1) ∧
    (∀ γ : ℝ, -1 < γ → γ < 0 →
      ¬ MeasureTheory.IntegrableOn (fun u : ℝ => u ^ γ) (Set.Ioi 1)) ∧
    (¬ MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Set.Ioi 1) ∧
      ∀ u : ℝ, u ^ (-1 : ℝ) = u⁻¹) ∧
    (MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioi 1) ∧
      (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) = 1 ∧
      0 < (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) ∧
      (∀ Λ : ℝ, 1 ≤ Λ →
        (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) = 1 - 1 / Λ ∧
        (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) < 1) ∧
      (∀ Λ : ℝ, 1 < Λ →
        0 < (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) ∧
        (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) < 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ
    unfold fourFermionDim dressedBilinearDim
    constructor <;> intro h <;> linarith
  · intro γ
    exact integrableOn_Ioi_rpow_iff zero_lt_one
  · intro γ hgt _hlt
    rw [integrableOn_Ioi_rpow_iff zero_lt_one]
    linarith
  · refine ⟨?_, ?_⟩
    · rw [integrableOn_Ioi_rpow_iff zero_lt_one]
      norm_num
    · intro u
      exact Real.rpow_neg_one u
  · have hint : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one
    have hval : (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) = 1 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.one_rpow]
      norm_num
    have hcut : ∀ Λ : ℝ, 1 ≤ Λ → (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) = 1 - 1 / Λ := by
      intro Λ hΛ
      have h0 : (0 : ℝ) ∉ [[(1 : ℝ), Λ]] := by
        rw [Set.uIcc_of_le hΛ]
        rintro ⟨h1, _⟩
        linarith
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, Real.rpow_neg_one,
        inv_one, one_div]
      ring
    refine ⟨hint, hval, by rw [hval]; norm_num, ?_, ?_⟩
    · intro Λ hΛ
      have heq := hcut Λ hΛ
      refine ⟨heq, ?_⟩
      rw [heq]
      have hpos : 0 < 1 / Λ := div_pos zero_lt_one (by linarith)
      linarith
    · intro Λ hΛ
      have heq := hcut Λ hΛ.le
      rw [heq]
      have hpos : 0 < 1 / Λ := div_pos zero_lt_one (by linarith)
      have hlt : 1 / Λ < 1 := (div_lt_one (by linarith)).mpr hΛ
      exact ⟨by linarith, by linarith⟩

/-! ### Part 2: Critical Potential Shape Trichotomy -/

/-- Single-well effective potential shape (`-1 < gamma < 0`): vanishes at `0`, strictly positive
away from `0`, strictly increasing on `[0, +infty)`, even, and coercive at `+infty`. -/
def SingleWellShape (V : ℝ → ℝ) : Prop :=
  V 0 = 0 ∧
  (∀ m : ℝ, m ≠ 0 → 0 < V m) ∧
  StrictMonoOn V (Set.Ici 0) ∧
  (∀ m : ℝ, V (-m) = V m) ∧
  Filter.Tendsto V Filter.atTop Filter.atTop

/-- Scale-invariant dynamical double-well effective potential shape (`gamma = -1`):
vanishes at `0`, achieves global minima `-(M^4 / 2)` precisely at `m = ±M`, has positive
curvature `8 * M^2` at `m = M`, and grows to `+infty`. -/
def DoubleWellShape (M : ℝ) (V : ℝ → ℝ) : Prop :=
  V 0 = 0 ∧
  (∀ m : ℝ, m ≠ 0 → -(M ^ 4 / 2) ≤ V m ∧ (V m = -(M ^ 4 / 2) ↔ m = M ∨ m = -M)) ∧
  V M = -(M ^ 4 / 2) ∧
  V (-M) = -(M ^ 4 / 2) ∧
  V M < V 0 ∧
  V (-M) < V 0 ∧
  deriv V M = 0 ∧
  deriv (deriv V) M = 8 * M ^ 2 ∧
  0 < deriv (deriv V) M ∧
  Filter.Tendsto V Filter.atTop Filter.atTop

/-- Inverted upside-down effective potential shape (`gamma = -2`): vanishes at `0`,
strictly negative away from `0`, strictly decreasing on `[0, +infty)`, even, strictly concave
away from `0`, and diverges to `-infty`. -/
def UpsideDownShape (V : ℝ → ℝ) : Prop :=
  V 0 = 0 ∧
  (∀ m : ℝ, m ≠ 0 → V m < 0) ∧
  StrictAntiOn V (Set.Ici 0) ∧
  (∀ m : ℝ, V (-m) = V m) ∧
  (∀ m : ℝ, m ≠ 0 → deriv (deriv V) m < 0) ∧
  Filter.Tendsto V Filter.atTop Filter.atBot

/-- Unified critical effective potential parameterized by anomalous dimension `gamma`,
dynamical mass scale `M`, and coupling constants `c2`, `c4`. -/
def mannheimCriticalPotential (γ M c₂ c₄ m : ℝ) : ℝ :=
  if γ = -1 then dynamicalDoubleWell M m
  else if γ < -1 then -c₄ * m ^ 4
  else c₂ * m ^ 2 + c₄ * (m ^ 2) ^ (2 / (1 - γ))

/-- Critical potential shape trichotomy across the three anomalous-dimension regimes:
1. `-1 < gamma < 0`: single well (`SingleWellShape`),
2. `gamma = -1`: finite scale-invariant double well (`DoubleWellShape M`) reusing
   `dynamicalDoubleWell M`, `dynamical_mass_goldstone_njl_and_vacuum_doublewell`, and the
   continuum limit `fermionBubble_integral_and_continuum_doubleWell`,
3. `gamma = -2`: upside-down inverted quartic potential (`UpsideDownShape`), including
   instantiation at the convergent `gamma = -2` UV integral constant `c_uv = 1`. -/
theorem mannheim_anomalous_dimension_potential_trichotomy :
    (∀ γ M c₂ c₄ : ℝ, -1 < γ → γ < 0 → 0 < c₂ → 0 < c₄ →
      SingleWellShape (mannheimCriticalPotential γ M c₂ c₄)) ∧
    (∀ M c₂ c₄ : ℝ, 0 < M →
      DoubleWellShape M (mannheimCriticalPotential (-1) M c₂ c₄) ∧
      (∀ m : ℝ, m ≠ 0 →
        Filter.Tendsto (fun Λ : ℝ => renormalizedFermionPotential Λ M m)
          Filter.atTop (nhds (mannheimCriticalPotential (-1) M c₂ c₄ m)))) ∧
    (∀ M c₂ c₄ : ℝ, 0 < c₄ →
      UpsideDownShape (mannheimCriticalPotential (-2) M c₂ c₄)) ∧
    (∀ M c₂ : ℝ,
      let c_uv : ℝ := ∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)
      c_uv = 1 ∧ 0 < c_uv ∧ UpsideDownShape (mannheimCriticalPotential (-2) M c₂ c_uv)) := by
  have hUpsideDown : ∀ (M c₂ c₄ : ℝ), 0 < c₄ →
      UpsideDownShape (mannheimCriticalPotential (-2) M c₂ c₄) := by
    intro M c₂ c₄ hc₄
    have hfun : mannheimCriticalPotential (-2) M c₂ c₄ = fun m : ℝ => -c₄ * m ^ 4 := by
      funext m
      simp [mannheimCriticalPotential, (by norm_num : (-2 : ℝ) ≠ -1),
        (by norm_num : (-2 : ℝ) < -1)]
    rw [hfun]
    refine ⟨by ring, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm
      have hm4 : 0 < m ^ 4 := by
        have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
        nlinarith [hm2]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc₄) hm4
    · intro a ha b _ hab
      have hpow : a ^ 4 < b ^ 4 := pow_lt_pow_left₀ hab ha (by norm_num : (4 : ℕ) ≠ 0)
      exact mul_lt_mul_of_neg_left hpow (neg_lt_zero.mpr hc₄)
    · intro m
      ring
    · intro m hm
      have hd1 : ∀ x : ℝ,
          HasDerivAt (fun t : ℝ => -c₄ * t ^ 4) (-4 * c₄ * x ^ 3) x := by
        intro x
        exact ((hasDerivAt_pow 4 x).const_mul (-c₄)).congr_deriv (by ring)
      have hderivFun : deriv (fun t : ℝ => -c₄ * t ^ 4) = fun x : ℝ => -4 * c₄ * x ^ 3 :=
        funext fun x => (hd1 x).deriv
      have hd2 : HasDerivAt (deriv (fun t : ℝ => -c₄ * t ^ 4)) (-12 * c₄ * m ^ 2) m := by
        rw [hderivFun]
        exact ((hasDerivAt_pow 3 m).const_mul (-4 * c₄)).congr_deriv (by ring)
      rw [hd2.deriv]
      have hm2 : 0 < m ^ 2 := sq_pos_of_ne_zero hm
      nlinarith
    · exact Filter.tendsto_neg_const_mul_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
        (neg_lt_zero.mpr hc₄)
  refine ⟨?_, ?_, hUpsideDown, ?_⟩
  · intro γ M c₂ c₄ hγ1 hγ0 hc₂ hc₄
    have hne : γ ≠ -1 := ne_of_gt hγ1
    have hnlt : ¬ γ < -1 := not_lt.mpr (le_of_lt hγ1)
    have hfun : mannheimCriticalPotential γ M c₂ c₄ =
        fun m : ℝ => c₂ * m ^ 2 + c₄ * (m ^ 2) ^ (2 / (1 - γ)) := by
      funext m
      simp [mannheimCriticalPotential, hne, hnlt]
    rw [hfun]
    set p : ℝ := 2 / (1 - γ)
    have hp : 0 < p := div_pos zero_lt_two (by linarith)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Real.zero_rpow hp.ne']
    · intro m hm
      have hsq : 0 < m ^ 2 := sq_pos_of_ne_zero hm
      exact add_pos (mul_pos hc₂ hsq) (mul_pos hc₄ (Real.rpow_pos_of_pos hsq p))
    · intro a ha b _ hab
      have hsq : a ^ 2 < b ^ 2 := pow_lt_pow_left₀ hab ha (by norm_num : (2 : ℕ) ≠ 0)
      have hrpow : (a ^ 2) ^ p < (b ^ 2) ^ p := Real.rpow_lt_rpow (sq_nonneg a) hsq hp
      exact add_lt_add (mul_lt_mul_of_pos_left hsq hc₂) (mul_lt_mul_of_pos_left hrpow hc₄)
    · intro m
      simp
    · have ht1 : Filter.Tendsto (fun m : ℝ => c₂ * m ^ 2) Filter.atTop Filter.atTop :=
        Filter.tendsto_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) hc₂
      exact Filter.tendsto_atTop_mono
        (fun m => le_add_of_nonneg_right
          (mul_nonneg hc₄.le (Real.rpow_nonneg (sq_nonneg m) p))) ht1
  · intro M c₂ c₄ hM
    have hfun : mannheimCriticalPotential (-1) M c₂ c₄ = dynamicalDoubleWell M := by
      funext m
      simp [mannheimCriticalPotential]
    rw [hfun]
    rcases dynamical_mass_goldstone_njl_and_vacuum_doublewell with
      ⟨_, _, _, _, hmin, hcurv, _, _⟩
    have hv0 : dynamicalDoubleWell M 0 = 0 := by
      unfold dynamicalDoubleWell
      norm_num
    have hMval : dynamicalDoubleWell M M = -(M ^ 4 / 2) :=
      (hmin M M hM hM.ne').2.1.mpr (Or.inl rfl)
    have hnegMval : dynamicalDoubleWell M (-M) = -(M ^ 4 / 2) :=
      (hmin M (-M) hM (neg_ne_zero.mpr hM.ne')).2.1.mpr (Or.inr rfl)
    have hMlt0 : dynamicalDoubleWell M M < dynamicalDoubleWell M 0 := by
      rw [hMval]
      exact (hmin M M hM hM.ne').2.2
    have hnegMlt0 : dynamicalDoubleWell M (-M) < dynamicalDoubleWell M 0 := by
      rw [hnegMval]
      exact (hmin M (-M) hM (neg_ne_zero.mpr hM.ne')).2.2
    have htend : Filter.Tendsto (dynamicalDoubleWell M) Filter.atTop Filter.atTop := by
      have htPow4 : Filter.Tendsto (fun m : ℝ => m ^ 4) Filter.atTop Filter.atTop :=
        Filter.tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)
      have htRat : Filter.Tendsto (fun m : ℝ => m ^ 2 / M ^ 2) Filter.atTop Filter.atTop :=
        (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const
          (sq_pos_of_pos hM)
      have htLog :
          Filter.Tendsto (fun m : ℝ => Real.log (m ^ 2 / M ^ 2)) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp htRat
      have htFac : Filter.Tendsto
          (fun m : ℝ => Real.log (m ^ 2 / M ^ 2) + (-(1 / 2 : ℝ))) Filter.atTop Filter.atTop :=
        htLog.atTop_add tendsto_const_nhds
      exact (htPow4.atTop_mul_atTop₀ htFac).congr (fun m => by unfold dynamicalDoubleWell; ring)
    refine ⟨?_, ?_⟩
    · refine ⟨hv0, ?_, hMval, hnegMval, hMlt0, hnegMlt0, ?_, ?_, ?_, htend⟩
      · intro m hm
        exact ⟨(hmin M m hM hm).1, (hmin M m hM hm).2.1⟩
      · exact (hcurv M hM).1
      · exact (hcurv M hM).2.1
      · exact (hcurv M hM).2.2
    · intro m hm
      exact (fermionBubble_integral_and_continuum_doubleWell M m hM hm).2.2
  · intro M c₂
    have hc_uv : (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) = 1 :=
      anomalous_dim_uv_integrability_trichotomy.2.2.2.2.2.1
    have hpos_uv : 0 < ∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ) :=
      anomalous_dim_uv_integrability_trichotomy.2.2.2.2.2.2.1
    exact ⟨hc_uv, hpos_uv, hUpsideDown M c₂ _ hpos_uv⟩

/-! ### Part 3: Above-Threshold Dynamical Higgs Decay Width vs Elementary Zero Width -/

/-- Two-fermion cut imaginary part of the 1-loop scalar bubble polarization: vanishes at and
below the `4 * m^2` pair-production threshold, and opens positively above threshold. -/
def scalarBubbleImPart (c_ps m qSq : ℝ) : ℝ :=
  if qSq ≤ 4 * m ^ 2 then 0
  else c_ps * (qSq - 4 * m ^ 2) * Real.sqrt (1 - 4 * m ^ 2 / qSq)

/-- Complex inverse propagator of the dynamical bound-state Higgs near resonance `M_H^2`,
incorporating the two-fermion cut imaginary part above `4 * m^2`. -/
def dynamicalHiggsComplexInvProp (g Z_H M_H c_ps m qSq : ℝ) : ℂ :=
  ((qSq - M_H ^ 2 : ℝ) : ℂ) + Complex.I * ((g * Z_H * scalarBubbleImPart c_ps m qSq : ℝ) : ℂ)

/-- Tree-level elementary Higgs inverse propagator with real mass pole and zero decay width. -/
def elementaryHiggsInvProp (M_H qSq : ℝ) : ℂ :=
  ((qSq - M_H ^ 2 : ℝ) : ℂ)

/-- Threshold dichotomy for `scalarBubbleImPart`: identically `0` for `qSq <= 4 * m^2` and
strictly positive for `4 * m^2 < qSq` when `0 < c_ps`. -/
theorem scalarBubbleImPart_threshold_dichotomy :
    (∀ c_ps m qSq : ℝ, qSq ≤ 4 * m ^ 2 → scalarBubbleImPart c_ps m qSq = 0) ∧
    (∀ c_ps m qSq : ℝ, 0 < c_ps → 4 * m ^ 2 < qSq → 0 < scalarBubbleImPart c_ps m qSq) := by
  refine ⟨?_, ?_⟩
  · intro c_ps m qSq hq
    simp [scalarBubbleImPart, hq]
  · intro c_ps m qSq hc hq
    have hqPos : 0 < qSq := lt_of_le_of_lt (by positivity) hq
    have hfrac : 4 * m ^ 2 / qSq < 1 := (div_lt_one hqPos).mpr hq
    have hsqrt : 0 < Real.sqrt (1 - 4 * m ^ 2 / qSq) := Real.sqrt_pos.mpr (sub_pos.mpr hfrac)
    simp only [scalarBubbleImPart, not_le.mpr hq, ↓reduceIte]
    exact mul_pos (mul_pos hc (sub_pos.mpr hq)) hsqrt

/-- Above-`2m`-threshold dynamical Higgs decay width vs elementary zero width:
for `2 * m < M_H` (with `0 < g`, `0 < Z_H`, `0 < m`, `0 < c_ps`),
- there exists a strictly positive decay width `Γ_dyn > 0` such that
  `(dynamicalHiggsComplexInvProp ... (M_H ^ 2)).im = M_H * Γ_dyn > 0` (while `= 0` at and
  below `4 * m ^ 2`),
- the dynamical resonance pole `s_pole` has strictly negative imaginary part `-(M_H * Γ_dyn) < 0`
  and connects directly to `conjPoleLorentzC`, `bwResonanceSq`, and positive Wigner time-delay
  derivative `0 < deriv (breitWignerPhase (M_H^2) (M_H * Γ_dyn)) qSq` via
  `pt_resonance_conjugate_poles_and_time_advance`,
- the real part links directly to `njlDressedInvPropagatorS` (and `njlInvPropagatorS` at
  threshold `M_H = 2 * m`),
- in contrast, `elementaryHiggsInvProp` has identically zero imaginary part everywhere and a
  real-axis pole `((M_H ^ 2 : ℝ) : ℂ).im = 0`. -/
theorem dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
    {g Z_H M_H c_ps m : ℝ}
    (hg : 0 < g) (hZ : 0 < Z_H) (hc : 0 < c_ps) (hm : 0 < m) (hMH : 2 * m < M_H) :
    ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      0 < M_H * Γ_dyn ∧
      (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m (M_H ^ 2)).re = 0 ∧
      (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m (M_H ^ 2)).im = M_H * Γ_dyn ∧
      (∀ qSq : ℝ, qSq ≤ 4 * m ^ 2 →
        (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m qSq).im = 0) ∧
      (let s_pole : ℂ := ((M_H ^ 2 : ℝ) : ℂ) - Complex.I * ((M_H * Γ_dyn : ℝ) : ℂ)
       s_pole.im < 0 ∧
       (∀ qSq : ℝ,
         ((qSq : ℂ) - s_pole) =
           ((qSq - M_H ^ 2 : ℝ) : ℂ) + Complex.I * ((M_H * Γ_dyn : ℝ) : ℂ)) ∧
       ((M_H ^ 2 : ℝ) : ℂ) - s_pole = dynamicalHiggsComplexInvProp g Z_H M_H c_ps m (M_H ^ 2) ∧
       (∀ E : ℝ,
         conjPoleLorentzC E (M_H ^ 2) (M_H * Γ_dyn) =
           (((M_H * Γ_dyn) / ((E - M_H ^ 2) ^ 2 + (M_H * Γ_dyn) ^ 2) : ℝ) : ℂ) ∧
         (bwResonanceSq E (M_H ^ 2) (M_H * Γ_dyn) = 1 / 2 ↔
           (E - M_H ^ 2) ^ 2 = (M_H * Γ_dyn) ^ 2 * (Real.sqrt 2 - 1)) ∧
         HasDerivAt (breitWignerPhase (M_H ^ 2) (M_H * Γ_dyn))
           ((M_H * Γ_dyn) / ((E - M_H ^ 2) ^ 2 + (M_H * Γ_dyn) ^ 2)) E ∧
         0 < deriv (breitWignerPhase (M_H ^ 2) (M_H * Γ_dyn)) E)) ∧
      (∀ Igap Jq qSq : ℝ, 0 < Jq → g * Igap = 1 →
        njlDressedInvPropagatorS g Igap Jq m (4 * m ^ 2 - M_H ^ 2) qSq =
          (g * Jq / 2) * (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m qSq).re ∧
        (njlDressedInvPropagatorS g Igap Jq m (4 * m ^ 2 - M_H ^ 2) qSq = 0 ↔ qSq = M_H ^ 2) ∧
        njlInvPropagatorS g Igap Jq m qSq =
          (g * Jq / 2) * (dynamicalHiggsComplexInvProp g Z_H (2 * m) c_ps m qSq).re) ∧
      (∀ qSq : ℝ, (elementaryHiggsInvProp M_H qSq).im = 0 ∧
        (elementaryHiggsInvProp M_H qSq = 0 ↔ qSq = M_H ^ 2)) ∧
      ((M_H ^ 2 : ℝ) : ℂ).im = 0 := by
  have hMH_pos : 0 < M_H := by linarith
  have hthresh : 4 * m ^ 2 < M_H ^ 2 := by nlinarith
  have him_pos : 0 < scalarBubbleImPart c_ps m (M_H ^ 2) :=
    scalarBubbleImPart_threshold_dichotomy.2 c_ps m (M_H ^ 2) hc hthresh
  let Γ_dyn : ℝ := (g * Z_H / M_H) * scalarBubbleImPart c_ps m (M_H ^ 2)
  have hΓ_pos : 0 < Γ_dyn := mul_pos (div_pos (mul_pos hg hZ) hMH_pos) him_pos
  have hMΓ_eq : M_H * Γ_dyn = g * Z_H * scalarBubbleImPart c_ps m (M_H ^ 2) := by
    dsimp [Γ_dyn]
    field_simp [hMH_pos.ne']
  have hMΓ_pos : 0 < M_H * Γ_dyn := mul_pos hMH_pos hΓ_pos
  refine ⟨Γ_dyn, hΓ_pos, hMΓ_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dynamicalHiggsComplexInvProp]
  · simp [dynamicalHiggsComplexInvProp, hMΓ_eq]
  · intro qSq hq
    have him0 : scalarBubbleImPart c_ps m qSq = 0 :=
      scalarBubbleImPart_threshold_dichotomy.1 c_ps m qSq hq
    simp [dynamicalHiggsComplexInvProp, him0, -Complex.ofReal_pow]
  · dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [-Complex.ofReal_pow]
      exact hMΓ_pos
    · intro qSq
      push_cast
      ring
    · rw [hMΓ_eq]
      simp only [dynamicalHiggsComplexInvProp]
      push_cast
      ring
    · intro E
      have hres := pt_resonance_conjugate_poles_and_time_advance E (M_H ^ 2) (M_H * Γ_dyn) hMΓ_pos
      exact ⟨hres.1, hres.2.1, hres.2.2.1, hres.2.2.2.2.1.2⟩
  · intro Igap Jq qSq hJ hgap
    have hre : (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m qSq).re = qSq - M_H ^ 2 := by
      unfold dynamicalHiggsComplexInvProp
      simp [-Complex.ofReal_pow]
    have hre_thresh :
        (dynamicalHiggsComplexInvProp g Z_H (2 * m) c_ps m qSq).re = qSq - (2 * m) ^ 2 := by
      unfold dynamicalHiggsComplexInvProp
      simp [-Complex.ofReal_pow]
    have hdressed : njlDressedInvPropagatorS g Igap Jq m (4 * m ^ 2 - M_H ^ 2) qSq =
        (g * Jq / 2) * (qSq - M_H ^ 2) := by
      unfold njlDressedInvPropagatorS
      have hsub : 1 - g * Igap = 0 := by linarith
      calc
        1 - g * (Igap - ((qSq - 4 * m ^ 2 + (4 * m ^ 2 - M_H ^ 2)) / 2) * Jq)
            = (1 - g * Igap) + (g * Jq / 2) * (qSq - M_H ^ 2) := by ring
        _ = (g * Jq / 2) * (qSq - M_H ^ 2) := by rw [hsub, zero_add]
    have hbare : njlInvPropagatorS g Igap Jq m qSq = (g * Jq / 2) * (qSq - (2 * m) ^ 2) := by
      have hnjl :=
        (dynamical_electroweak_goldstone_and_boundstate_higgs_poles hg hJ hm hgap).2.1 qSq
      rw [hnjl.1]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hdressed, hre]
    · rw [hdressed]
      have hgJ : 0 < g * Jq / 2 := div_pos (mul_pos hg hJ) zero_lt_two
      constructor
      · intro hz
        rcases mul_eq_zero.mp hz with hzero | hdiff
        · exfalso; exact hgJ.ne' hzero
        · linarith
      · intro hq
        rw [hq]
        ring
    · rw [hbare, hre_thresh]
  · intro qSq
    refine ⟨by simp [elementaryHiggsInvProp, -Complex.ofReal_pow], ?_⟩
    simp only [elementaryHiggsInvProp, Complex.ofReal_eq_zero]
    constructor <;> intro h <;> linarith
  · simp [-Complex.ofReal_pow]

section ArchetypeRegistrations

/-- Proved `TypedArchetype` for `MA₁₄`: Mannheim anomalous-dimension UV integrability
trichotomy, critical effective potential shape trichotomy (`-1 < gamma < 0` single well,
`gamma = -1` scale-invariant dynamical double well, `gamma = -2` upside-down potential),
and above-`2m`-threshold dynamical Higgs decay width vs zero elementary Higgs width. -/
def archMA14CriticalScalingAndHiggsWidth : TypedArchetype Unit .proved where
  name := `archMA14CriticalScalingAndHiggsWidth
  phase := 14
  claim := fun _ =>
    (∀ γ : ℝ, fourFermionDim γ = 4 ↔ γ = -1) ∧
    (∀ γ : ℝ, MeasureTheory.IntegrableOn (fun u : ℝ => u ^ γ) (Set.Ioi 1) ↔ γ < -1) ∧
    ((∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) = 1 ∧
      ∀ Λ : ℝ, 1 ≤ Λ → (∫ u in (1 : ℝ)..Λ, u ^ (-2 : ℝ)) = 1 - 1 / Λ) ∧
    (∀ γ M c₂ c₄ : ℝ, -1 < γ → γ < 0 → 0 < c₂ → 0 < c₄ →
      SingleWellShape (mannheimCriticalPotential γ M c₂ c₄)) ∧
    (∀ M c₂ c₄ : ℝ, 0 < M →
      DoubleWellShape M (mannheimCriticalPotential (-1) M c₂ c₄)) ∧
    (∀ M c₂ c₄ : ℝ, 0 < c₄ →
      UpsideDownShape (mannheimCriticalPotential (-2) M c₂ c₄)) ∧
    (∀ {g Z_H M_H c_ps m : ℝ},
      0 < g → 0 < Z_H → 0 < c_ps → 0 < m → 2 * m < M_H →
      ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
        (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m (M_H ^ 2)).im = M_H * Γ_dyn ∧
        0 < deriv (breitWignerPhase (M_H ^ 2) (M_H * Γ_dyn)) (M_H ^ 2) ∧
        (∀ qSq : ℝ, (elementaryHiggsInvProp M_H qSq).im = 0))
  evidence := fun _ =>
    let huv := anomalous_dim_uv_integrability_trichotomy
    let hpot := mannheim_anomalous_dimension_potential_trichotomy
    ⟨huv.1,
     huv.2.1,
     ⟨huv.2.2.2.2.2.1, fun Λ hΛ => (huv.2.2.2.2.2.2.2.1 Λ hΛ).1⟩,
     hpot.1,
     fun M c₂ c₄ hM => (hpot.2.1 M c₂ c₄ hM).1,
     hpot.2.2.1,
     fun hg hZ hc hm hMH =>
       let hh := dynamical_higgs_above_threshold_positive_width_vs_elementary_zero hg hZ hc hm hMH
       ⟨hh.choose, hh.choose_spec.1,
        hh.choose_spec.2.2.2.1,
        (hh.choose_spec.2.2.2.2.2.1.2.2.2 ( _ )).2.2.2,
        fun qSq => (hh.choose_spec.2.2.2.2.2.2.2.1 qSq).1⟩⟩

#register_archetype archMA14CriticalScalingAndHiggsWidth
#audit_archetype archMA14CriticalScalingAndHiggsWidth

end ArchetypeRegistrations

end InfoGeometry.Conformal.MannheimCriticalScalingAndHiggsWidth
