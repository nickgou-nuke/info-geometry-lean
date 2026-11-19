/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.PenroseEikonalTwistorRay
import InfoGeometry.Synthesis.MannheimTwistorBlochWavefrontEpistemicSynthesis
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Mannheim Double-Slit Spacetime Phase Cancellation & Finite Source Coherence Window

Formalizes the spacetime phase cancellation and finite-coherence-window optics results from
Philip Mannheim's Part 2 lecture (`01:02:25–01:06:08`), bridged to Penrose null eikonal rays
and the Möbius–Tomita–Bloch wavefront synthesis:

1. **Equal-Emission Propagation Phase Cancellation**:
   For two slit paths separated by spatial path difference `ΔL = c Δt` and dispersion
   `ω = c k`, the spacetime propagation phase `propPhaseDiff k ω ΔL Δt = k ΔL - ω Δt`
   vanishes identically (`exp (i * propPhaseDiff) = 1`), matching Minkowski null propagation
   `IsMinkowskiNull (slitRayDisplacement c Δt ΔL)` and `(pauliSoldering _).det = 0`.
2. **Earlier-Emission Source Phase Restoration**:
   An earlier source wavefront emission time offset `Δt_src = ΔL / c` restores the observable
   interference phase `sourcePhaseDiff ω Δt_src = ω Δt_src = k ΔL`, giving
   `totalSlitPhaseDiff k ω ΔL Δt Δt_src = k ΔL`.
3. **Finite Source Coherence Window & Fringe Cutoff**:
   The coherence gate `IsWithinCoherenceWindow τ_coh Δt_src` (`|Δt_src| ≤ τ_coh`) holds iff
   `|ΔL| ≤ c * τ_coh`, and `coherenceVisibility τ_coh Δt_src = max 0 (1 - |Δt_src| / τ_coh)`
   ranges in `[0, 1]`, is strictly positive iff `|ΔL| < c * τ_coh`, and vanishes for
   `|ΔL| > c * τ_coh`, collapsing `twoSlitIntensity` to the incoherent sum `2 * I₀`.
4. **Null-Ray, Wavefront-Leaflet, & `M₂(ℂ)` Unitary Interferometer Bridge**:
   Connects without circularity to `PenroseEikonalTwistorRay` (`IsMinkowskiNull`,
   `null_iff_det_pauliSoldering_zero`, `conformal_null_invariance`),
   `MannheimTwistorBlochWavefrontEpistemicSynthesis` (`fisherLeaflet`, `stereoLeaflet`,
   `mobius_tomita_wavefront_leaflet_triality`, `gramBlochState`, `quantumUmegakiGibbs`), and a
   unitary `twoSlitInterferometerOp` with an explicit non-commutativity witness on `M₂(ℂ)`.
-/

noncomputable section

namespace InfoGeometry.Optics.MannheimDoubleSlitSpacetimeCoherence

open Matrix Filter
open scoped MatrixOrder ComplexOrder
open InfoGeometry.Physics.PenroseEikonalTwistorRay
open InfoGeometry.Synthesis.MannheimTwistorBlochWavefrontEpistemicSynthesis
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology (scaleGaugeMultiplier)
open InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
  (blochNormSq blochZ coherenceRelEntropy quantumUmegakiGibbs)
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants (bregmanPhi meanSpin)
open InfoGeometry.MetaCompiler

/-! ## 1. Core Spacetime Phase, Coherence Window, & Interferometer Definitions -/

/-- Spacetime propagation phase difference `k ΔL - ω Δt` between the two slit paths. -/
def propPhaseDiff (k ω ΔL Δt : ℝ) : ℝ :=
  k * ΔL - ω * Δt

/-- Source emission phase difference `+ω Δt_src` from an earlier wavefront emission time. -/
def sourcePhaseDiff (ω Δt_src : ℝ) : ℝ :=
  ω * Δt_src

/-- Total two-slit phase difference `(k ΔL - ω Δt) + ω Δt_src`. -/
def totalSlitPhaseDiff (k ω ΔL Δt Δt_src : ℝ) : ℝ :=
  propPhaseDiff k ω ΔL Δt + sourcePhaseDiff ω Δt_src

/-- Finite source coherence window predicate `|Δt_src| ≤ τ_coh`. -/
def IsWithinCoherenceWindow (τ_coh Δt_src : ℝ) : Prop :=
  |Δt_src| ≤ τ_coh

/-- Tent coherence visibility `max 0 (1 - |Δt_src| / τ_coh)` (for `τ_coh > 0`). -/
def coherenceVisibility (τ_coh Δt_src : ℝ) : ℝ :=
  max 0 (1 - |Δt_src| / τ_coh)

/-- Double-slit intensity `2 I₀ (1 + V(τ_coh, Δt_src) cos(ΔΦ_tot))`. -/
def twoSlitIntensity (I₀ τ_coh k ω ΔL Δt Δt_src : ℝ) : ℝ :=
  2 * I₀ * (1 + coherenceVisibility τ_coh Δt_src *
    Real.cos (totalSlitPhaseDiff k ω ΔL Δt Δt_src))

/-- Minkowski displacement 4-vector `(c Δt, ΔL, 0, 0)` along the propagation axis. -/
def slitRayDisplacement (c Δt ΔL : ℝ) : MinkowskiVector :=
  ⟨c * Δt, ΔL, 0, 0⟩

/-- Minkowski 4-wavevector `(ω / c, k, 0, 0)` along the propagation axis. -/
def waveFourVector (c ω k : ℝ) : MinkowskiVector :=
  ⟨ω / c, k, 0, 0⟩

/-- Two-slit relative phase-shift matrix `diag(exp(i ΔΦ), 1)` on `ℂ²`. -/
def slitPhaseMatrix (ΔΦ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * (ΔΦ : ℂ)), 0; 0, 1]

/-- Symmetric 50:50 beam-splitter / slit-recombination Hadamard matrix on `ℂ²`. -/
def beamSplitterHadamard : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • !![1, 1; 1, -1]

/-- Unitary two-slit Mach–Zehnder / interferometer matrix `H * P(ΔΦ) * H`. -/
def twoSlitInterferometerOp (ΔΦ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  beamSplitterHadamard * slitPhaseMatrix ΔΦ * beamSplitterHadamard

/-! ## 2. Equal-Emission Cancellation, Source Restoration, & Finite Coherence Cutoff -/

/-- **Equal-Emission Propagation Phase Cancellation**:
For light-cone path separation `ΔL = c Δt` and dispersion `ω = c k`, the spacetime propagation
phase `k ΔL - ω Δt` vanishes identically, `exp (i * propPhaseDiff) = 1`, the inter-slit
displacement 4-vector is Minkowski-null with vanishing Pauli-soldering determinant, and (for
`c ≠ 0`) the wave 4-vector is Minkowski-null. -/
theorem equal_emission_phase_cancellation
    (c k ω ΔL Δt : ℝ)
    (h_light : ΔL = c * Δt)
    (h_disp : ω = c * k) :
    propPhaseDiff k ω ΔL Δt = 0 ∧
    Complex.exp (Complex.I * (propPhaseDiff k ω ΔL Δt : ℂ)) = 1 ∧
    IsMinkowskiNull (slitRayDisplacement c Δt ΔL) ∧
    (pauliSoldering (slitRayDisplacement c Δt ΔL)).det = 0 ∧
    (c ≠ 0 → IsMinkowskiNull (waveFourVector c ω k)) := by
  have h_prop : propPhaseDiff k ω ΔL Δt = 0 := by
    unfold propPhaseDiff
    rw [h_light, h_disp]
    ring
  have h_exp : Complex.exp (Complex.I * (propPhaseDiff k ω ΔL Δt : ℂ)) = 1 := by
    rw [h_prop, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have h_null : IsMinkowskiNull (slitRayDisplacement c Δt ΔL) := by
    unfold IsMinkowskiNull minkowskiNorm slitRayDisplacement
    rw [h_light]
    ring
  have h_det : (pauliSoldering (slitRayDisplacement c Δt ΔL)).det = 0 :=
    (null_iff_det_pauliSoldering_zero (slitRayDisplacement c Δt ΔL)).mp h_null
  have h_wave : c ≠ 0 → IsMinkowskiNull (waveFourVector c ω k) := by
    intro hc
    unfold IsMinkowskiNull minkowskiNorm waveFourVector
    rw [h_disp]
    field_simp [hc]
    ring
  exact ⟨h_prop, h_exp, h_null, h_det, h_wave⟩

/-- **Earlier-Emission Source Phase Restoration**:
With `c ≠ 0`, `ΔL = c Δt`, `ω = c k`, and source emission offset `Δt_src = ΔL / c`, propagation
phase cancels (`propPhaseDiff = 0`), while the source term restores `sourcePhaseDiff = k ΔL`
and `totalSlitPhaseDiff = k ΔL`, preserving the interference phase factor `exp (i k ΔL)`. -/
theorem earlier_emission_phase_restoration
    (c k ω ΔL Δt Δt_src : ℝ)
    (hc : c ≠ 0)
    (h_light : ΔL = c * Δt)
    (h_disp : ω = c * k)
    (h_src : Δt_src = ΔL / c) :
    propPhaseDiff k ω ΔL Δt = 0 ∧
    sourcePhaseDiff ω Δt_src = k * ΔL ∧
    totalSlitPhaseDiff k ω ΔL Δt Δt_src = k * ΔL ∧
    Complex.exp (Complex.I * (totalSlitPhaseDiff k ω ΔL Δt Δt_src : ℂ)) =
      Complex.exp (Complex.I * ((k * ΔL : ℝ) : ℂ)) := by
  have h_prop : propPhaseDiff k ω ΔL Δt = 0 :=
    (equal_emission_phase_cancellation c k ω ΔL Δt h_light h_disp).1
  have h_src_eq : sourcePhaseDiff ω Δt_src = k * ΔL := by
    unfold sourcePhaseDiff
    rw [h_disp, h_src]
    field_simp [hc]
  have h_tot : totalSlitPhaseDiff k ω ΔL Δt Δt_src = k * ΔL := by
    unfold totalSlitPhaseDiff
    rw [h_prop, h_src_eq, zero_add]
  have h_exp :
      Complex.exp (Complex.I * (totalSlitPhaseDiff k ω ΔL Δt Δt_src : ℂ)) =
        Complex.exp (Complex.I * ((k * ΔL : ℝ) : ℂ)) := by
    rw [h_tot]
  exact ⟨h_prop, h_src_eq, h_tot, h_exp⟩

/-- **Finite Source Coherence Window & Fringe Cutoff**:
For `0 < c`, `0 < τ_coh`, and `Δt_src = ΔL / c`:
1. The coherence window `|Δt_src| ≤ τ_coh` holds iff `|ΔL| ≤ c * τ_coh`;
2. `0 ≤ coherenceVisibility τ_coh Δt_src ≤ 1`;
3. `0 < coherenceVisibility τ_coh Δt_src ↔ |ΔL| < c * τ_coh`;
4. Beyond the coherence length (`c * τ_coh < |ΔL|`), the coherence window fails,
   `coherenceVisibility τ_coh Δt_src = 0`, and fringes disappear (`twoSlitIntensity = 2 * I₀`);
5. For `0 ≤ I₀`, `0 ≤ twoSlitIntensity ≤ 4 * I₀`. -/
theorem coherence_window_and_fringe_cutoff
    (c τ_coh ΔL Δt_src I₀ k ω Δt : ℝ)
    (hc : 0 < c)
    (hτ : 0 < τ_coh)
    (h_src : Δt_src = ΔL / c) :
    (IsWithinCoherenceWindow τ_coh Δt_src ↔ |ΔL| ≤ c * τ_coh) ∧
    (0 ≤ coherenceVisibility τ_coh Δt_src ∧ coherenceVisibility τ_coh Δt_src ≤ 1) ∧
    (0 < coherenceVisibility τ_coh Δt_src ↔ |ΔL| < c * τ_coh) ∧
    (c * τ_coh < |ΔL| →
      ¬ IsWithinCoherenceWindow τ_coh Δt_src ∧
      coherenceVisibility τ_coh Δt_src = 0 ∧
      twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src = 2 * I₀) ∧
    (0 ≤ I₀ →
      0 ≤ twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ∧
      twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ≤ 4 * I₀) := by
  have h_abs : |Δt_src| = |ΔL| / c := by
    rw [h_src, abs_div, abs_of_pos hc]
  have h_win : IsWithinCoherenceWindow τ_coh Δt_src ↔ |ΔL| ≤ c * τ_coh := by
    unfold IsWithinCoherenceWindow
    rw [h_abs, div_le_iff₀ hc, mul_comm]
  have h_vis_nonneg : 0 ≤ coherenceVisibility τ_coh Δt_src :=
    le_max_left 0 (1 - |Δt_src| / τ_coh)
  have h_vis_le_one : coherenceVisibility τ_coh Δt_src ≤ 1 := by
    unfold coherenceVisibility
    refine max_le zero_le_one ?_
    have h_div_nonneg : 0 ≤ |Δt_src| / τ_coh := div_nonneg (abs_nonneg Δt_src) hτ.le
    linarith
  have h_vis_pos : 0 < coherenceVisibility τ_coh Δt_src ↔ |ΔL| < c * τ_coh := by
    unfold coherenceVisibility
    rw [lt_max_iff]
    simp only [lt_self_iff_false, false_or, sub_pos, div_lt_one hτ, h_abs, div_lt_iff₀ hc,
      mul_comm]
  have h_cutoff :
      c * τ_coh < |ΔL| →
        ¬ IsWithinCoherenceWindow τ_coh Δt_src ∧
        coherenceVisibility τ_coh Δt_src = 0 ∧
        twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src = 2 * I₀ := by
    intro h_gt
    have h_not_win : ¬ IsWithinCoherenceWindow τ_coh Δt_src := by
      rw [h_win]
      exact not_le_of_gt h_gt
    have h_ge_one : 1 ≤ |Δt_src| / τ_coh := by
      rw [one_le_div₀ hτ, h_abs, le_div_iff₀ hc, mul_comm]
      exact h_gt.le
    have h_vis_zero : coherenceVisibility τ_coh Δt_src = 0 := by
      unfold coherenceVisibility
      exact max_eq_left (by linarith)
    have h_int : twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src = 2 * I₀ := by
      unfold twoSlitIntensity
      rw [h_vis_zero, zero_mul, add_zero, mul_one]
    exact ⟨h_not_win, h_vis_zero, h_int⟩
  have h_bounds :
      0 ≤ I₀ →
        0 ≤ twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ∧
        twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ≤ 4 * I₀ := by
    intro hI₀
    unfold twoSlitIntensity
    set V := coherenceVisibility τ_coh Δt_src
    set C := Real.cos (totalSlitPhaseDiff k ω ΔL Δt Δt_src)
    have hC_ge : -1 ≤ C := Real.neg_one_le_cos _
    have hC_le : C ≤ 1 := Real.cos_le_one _
    have hVC_ge : -1 ≤ V * C := by nlinarith
    have hVC_le : V * C ≤ 1 := by nlinarith
    constructor <;> nlinarith
  exact ⟨h_win, ⟨h_vis_nonneg, h_vis_le_one⟩, h_vis_pos, h_cutoff, h_bounds⟩

/-! ## 3. Unitary `M₂(ℂ)` Two-Slit Interferometer & Non-Commutativity Witness (`T16`) -/

lemma slitPhaseMatrix_unitary (ΔΦ : ℝ) :
    (slitPhaseMatrix ΔΦ)ᴴ * slitPhaseMatrix ΔΦ = 1 ∧
    slitPhaseMatrix ΔΦ * (slitPhaseMatrix ΔΦ)ᴴ = 1 := by
  have hz_conj :
      starRingEnd ℂ (Complex.exp (Complex.I * (ΔΦ : ℂ))) =
        Complex.exp (-(Complex.I * (ΔΦ : ℂ))) := by
    rw [← Complex.exp_conj]
    simp [Complex.conj_I]
  have hzz :
      starRingEnd ℂ (Complex.exp (Complex.I * (ΔΦ : ℂ))) *
        Complex.exp (Complex.I * (ΔΦ : ℂ)) = 1 := by
    rw [hz_conj, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hzz' :
      Complex.exp (Complex.I * (ΔΦ : ℂ)) *
        starRingEnd ℂ (Complex.exp (Complex.I * (ΔΦ : ℂ))) = 1 := by
    rw [hz_conj, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two] using hzz
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two] using hzz'
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
    · simp [slitPhaseMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

lemma beamSplitterHadamard_unitary :
    beamSplitterHadamardᴴ * beamSplitterHadamard = 1 ∧
    beamSplitterHadamard * beamSplitterHadamardᴴ = 1 := by
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs_ne : Real.sqrt 2 ≠ 0 := by positivity
  have h12 : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) +
      (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 := by
    field_simp [hs_ne]
    linarith [hsq2]
  have h12C : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) +
      ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    exact_mod_cast h12
  have hH_sa : beamSplitterHadamardᴴ = beamSplitterHadamard := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [beamSplitterHadamard, Matrix.conjTranspose_apply]
  have hH_sq : beamSplitterHadamard * beamSplitterHadamard = 1 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [beamSplitterHadamard, Matrix.mul_apply, Fin.sum_univ_two] using h12C
    · simp [beamSplitterHadamard, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [beamSplitterHadamard, Matrix.mul_apply, Fin.sum_univ_two]
    · simpa [beamSplitterHadamard, Matrix.mul_apply, Fin.sum_univ_two] using h12C
  rw [hH_sa]
  exact ⟨hH_sq, hH_sq⟩

lemma twoSlitInterferometerOp_unitary_and_det_ne_zero (ΔΦ : ℝ) :
    (twoSlitInterferometerOp ΔΦ)ᴴ * twoSlitInterferometerOp ΔΦ = 1 ∧
    twoSlitInterferometerOp ΔΦ * (twoSlitInterferometerOp ΔΦ)ᴴ = 1 ∧
    Matrix.det (twoSlitInterferometerOp ΔΦ) ≠ 0 := by
  have hP := slitPhaseMatrix_unitary ΔΦ
  have hH := beamSplitterHadamard_unitary
  have hleft : (twoSlitInterferometerOp ΔΦ)ᴴ * twoSlitInterferometerOp ΔΦ = 1 := by
    unfold twoSlitInterferometerOp
    calc
      (beamSplitterHadamard * slitPhaseMatrix ΔΦ * beamSplitterHadamard)ᴴ *
          (beamSplitterHadamard * slitPhaseMatrix ΔΦ * beamSplitterHadamard)
          = beamSplitterHadamardᴴ *
              ((slitPhaseMatrix ΔΦ)ᴴ * (beamSplitterHadamardᴴ * beamSplitterHadamard) *
                slitPhaseMatrix ΔΦ) *
              beamSplitterHadamard := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = beamSplitterHadamardᴴ * ((slitPhaseMatrix ΔΦ)ᴴ * slitPhaseMatrix ΔΦ) *
            beamSplitterHadamard := by
            rw [hH.1, Matrix.mul_one]
      _ = beamSplitterHadamardᴴ * beamSplitterHadamard := by
            rw [hP.1, Matrix.mul_one]
      _ = 1 := hH.1
  have hright : twoSlitInterferometerOp ΔΦ * (twoSlitInterferometerOp ΔΦ)ᴴ = 1 := by
    unfold twoSlitInterferometerOp
    calc
      (beamSplitterHadamard * slitPhaseMatrix ΔΦ * beamSplitterHadamard) *
          (beamSplitterHadamard * slitPhaseMatrix ΔΦ * beamSplitterHadamard)ᴴ
          = beamSplitterHadamard *
              (slitPhaseMatrix ΔΦ * (beamSplitterHadamard * beamSplitterHadamardᴴ) *
                (slitPhaseMatrix ΔΦ)ᴴ) *
              beamSplitterHadamardᴴ := by
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = beamSplitterHadamard * (slitPhaseMatrix ΔΦ * (slitPhaseMatrix ΔΦ)ᴴ) *
            beamSplitterHadamardᴴ := by
            rw [hH.2, Matrix.mul_one]
      _ = beamSplitterHadamard * beamSplitterHadamardᴴ := by
            rw [hP.2, Matrix.mul_one]
      _ = 1 := hH.2
  have hdet : Matrix.det (twoSlitInterferometerOp ΔΦ) ≠ 0 := by
    intro h0
    have hmul := congrArg Matrix.det hleft
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at hmul
    exact zero_ne_one hmul
  exact ⟨hleft, hright, hdet⟩

lemma twoSlitInterferometerOp_fringe_normSq (ΔΦ : ℝ) :
    2 * Complex.normSq ((twoSlitInterferometerOp ΔΦ) 0 0) = 1 + Real.cos ΔΦ := by
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hhalf : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
    field_simp [hs_ne]
    linarith [hsq2]
  have hhalfC : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_mul, hhalf]
    norm_num
  have h00 : (twoSlitInterferometerOp ΔΦ) 0 0 =
      (1 / 2 : ℂ) * (Complex.exp (Complex.I * (ΔΦ : ℂ)) + 1) := by
    simp only [twoSlitInterferometerOp, beamSplitterHadamard, slitPhaseMatrix, Matrix.mul_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.sum_univ_two, smul_eq_mul]
    calc
      (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1 * Complex.exp (Complex.I * (ΔΦ : ℂ)) +
          ((1 / Real.sqrt 2 : ℝ) : ℂ) * 1 * 0) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1) +
        (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1 * 0 +
          ((1 / Real.sqrt 2 : ℝ) : ℂ) * 1 * 1) * (((1 / Real.sqrt 2 : ℝ) : ℂ) * 1)
          = (((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ)) *
              (Complex.exp (Complex.I * (ΔΦ : ℂ)) + 1) := by ring
      _ = (1 / 2 : ℂ) * (Complex.exp (Complex.I * (ΔΦ : ℂ)) + 1) := by rw [hhalfC]
  have hexp : Complex.exp (Complex.I * (ΔΦ : ℂ)) =
      (Real.cos ΔΦ : ℂ) + (Real.sin ΔΦ : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h00, hexp, Complex.normSq_mul]
  have hnorm_half : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    norm_num [Complex.normSq]
  have hnorm_sum :
      Complex.normSq ((Real.cos ΔΦ : ℂ) + (Real.sin ΔΦ : ℂ) * Complex.I + 1) =
        2 * (1 + Real.cos ΔΦ) := by
    have hre : ((Real.cos ΔΦ : ℂ) + (Real.sin ΔΦ : ℂ) * Complex.I + 1).re = Real.cos ΔΦ + 1 := by
      rw [Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.one_re]
      ring
    have him : ((Real.cos ΔΦ : ℂ) + (Real.sin ΔΦ : ℂ) * Complex.I + 1).im = Real.sin ΔΦ := by
      rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re, Complex.one_im]
      ring
    rw [Complex.normSq_apply, hre, him]
    have htrig := Real.sin_sq_add_cos_sq ΔΦ
    linarith [show (Real.cos ΔΦ + 1) * (Real.cos ΔΦ + 1) + Real.sin ΔΦ * Real.sin ΔΦ =
      (Real.sin ΔΦ ^ 2 + Real.cos ΔΦ ^ 2) + 2 * Real.cos ΔΦ + 1 by ring]
  rw [hnorm_half, hnorm_sum]
  ring

lemma slitPhaseMatrix_pi_beamSplitter_ne :
    slitPhaseMatrix Real.pi * beamSplitterHadamard ≠
      beamSplitterHadamard * slitPhaseMatrix Real.pi := by
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  have hpi : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  have hleft : (slitPhaseMatrix Real.pi * beamSplitterHadamard) 0 1 =
      -((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    unfold slitPhaseMatrix beamSplitterHadamard
    simp [Matrix.mul_apply, Fin.sum_univ_two, hpi]
  have hright : (beamSplitterHadamard * slitPhaseMatrix Real.pi) 0 1 =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    unfold slitPhaseMatrix beamSplitterHadamard
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [hleft, hright] at h01
  have hre := congrArg Complex.re h01
  simp only [Complex.neg_re, Complex.ofReal_re] at hre
  have hpos : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
  linarith

/-- **OpenGauss `T16` Closed Non-Commutativity Witness on `M₂(ℂ)`**:
The relative slit-phase operator `slitPhaseMatrix Real.pi` and 50:50 beam-splitter
`beamSplitterHadamard` do not commute. -/
theorem doubleSlit_matrix2_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨slitPhaseMatrix Real.pi, beamSplitterHadamard, slitPhaseMatrix_pi_beamSplitter_ne⟩

/-! ## 4. Bridge to Penrose Eikonal Rays & Mannheim Wavefront Leaflets / Bloch Umegaki -/

/-- **Double-Slit Null-Ray, Wavefront-Leaflet, & `M₂(ℂ)` Bloch–Umegaki Bridge**:
Connects the double-slit spacetime coherence system without circularity to:
1. `PenroseEikonalTwistorRay`: nullity of `slitRayDisplacement` and `waveFourVector`,
   `null_iff_det_pauliSoldering_zero`, and `conformal_null_invariance` under `g̃ = Ω² g`;
2. `MannheimTwistorBlochWavefrontEpistemicSynthesis` (`fisherLeaflet`, `stereoLeaflet`, and
   `mobius_tomita_wavefront_leaflet_triality`): exact algebraic identity
   `stereoLeaflet (Real.exp τ) = fisherLeaflet (2 * τ)` and `0 → 1 → 0` envelope comparison
   between `coherenceVisibility` (compact support on `|ΔL| ≤ c * τ_coh`) and the smooth
   wavefront leaflets;
3. Unitary `twoSlitInterferometerOp` fringe readout, Weyl scale–gauge invariance of
   `gramBlochState`, and unconditional `quantumUmegakiGibbs` via
   `gramBlochState_determinant_and_unconditional_umegaki`. -/
theorem doubleSlit_null_ray_and_leaflet_bridge :
    (∀ c k ω Δt ΔL Ω : ℝ, ΔL = c * Δt → ω = c * k → 0 < Ω →
      let dx := slitRayDisplacement c Δt ΔL
      IsMinkowskiNull dx ∧
      (pauliSoldering dx).det = 0 ∧
      Ω ^ 2 * minkowskiNorm dx = 0 ∧
      propPhaseDiff k ω ΔL Δt = 0 ∧
      Complex.exp (Complex.I * (propPhaseDiff k ω ΔL Δt : ℂ)) = 1) ∧
    (∀ c k ω : ℝ, c ≠ 0 → ω = c * k →
      IsMinkowskiNull (waveFourVector c ω k) ∧
      (pauliSoldering (waveFourVector c ω k)).det = 0) ∧
    (∀ τ : ℝ, stereoLeaflet (Real.exp τ) = fisherLeaflet (2 * τ)) ∧
    (∀ c τ_coh k Δt I₀ : ℝ, 0 < c → 0 < τ_coh →
      coherenceVisibility τ_coh 0 = 1 ∧
      fisherLeaflet 0 = 1 ∧
      stereoLeaflet (Real.exp 0) = 1 ∧
      twoSlitIntensity I₀ τ_coh k (c * k) (c * Δt) Δt 0 = 4 * I₀ ∧
      (∀ Δt_src : ℝ,
        coherenceVisibility τ_coh (-Δt_src) = coherenceVisibility τ_coh Δt_src ∧
        (coherenceVisibility τ_coh Δt_src = 1 ↔ Δt_src = 0)) ∧
      (∀ ΔL : ℝ, c * τ_coh < |ΔL| →
        coherenceVisibility τ_coh (ΔL / c) = 0 ∧
        twoSlitIntensity I₀ τ_coh k (c * k) ΔL Δt (ΔL / c) = 2 * I₀ ∧
        0 < fisherLeaflet (ΔL / (c * τ_coh)) ∧
        fisherLeaflet (ΔL / (c * τ_coh)) < 1) ∧
      Filter.Tendsto (fun ΔL : ℝ => coherenceVisibility τ_coh (ΔL / c))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun ΔL : ℝ => coherenceVisibility τ_coh (ΔL / c))
        Filter.atBot (nhds 0) ∧
      Filter.Tendsto (fun ΔL : ℝ => fisherLeaflet (ΔL / (c * τ_coh)))
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun ΔL : ℝ => fisherLeaflet (ΔL / (c * τ_coh)))
        Filter.atBot (nhds 0) ∧
      Filter.Tendsto stereoLeaflet Filter.atTop (nhds 0) ∧
      Filter.Tendsto stereoLeaflet Filter.atBot (nhds 0)) ∧
    (∀ ΔΦ β α θ I₀ τ_coh k ω ΔL Δt : ℝ, 0 < τ_coh →
      totalSlitPhaseDiff k ω ΔL Δt 0 = ΔΦ →
      let W := twoSlitInterferometerOp ΔΦ
      let ρ := gramBlochState W
      Wᴴ * W = 1 ∧
      2 * I₀ * (2 * Complex.normSq (W 0 0)) = twoSlitIntensity I₀ τ_coh k ω ΔL Δt 0 ∧
      gramBlochState (scaleGaugeMultiplier β α • W) = ρ ∧
      IsSelfAdjoint ρ ∧
      Matrix.trace ρ = 1 ∧
      blochNormSq ρ < 1 ∧
      IsStrictlyPositive ρ ∧
      0 ≤ quantumUmegakiGibbs ρ θ ∧
      quantumUmegakiGibbs ρ θ = coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ)) := by
  have htri := mobius_tomita_wavefront_leaflet_triality
  have hfisher_prop := htri.2.2.2.2.2.2.1
  have hfisher_lim := htri.2.2.2.2.2.2.2.1
  have hstereo_lim := htri.2.2.2.2.2.2.2.2.2
  have hgram := gramBlochState_determinant_and_unconditional_umegaki
  have hstereo_fisher : ∀ τ : ℝ, stereoLeaflet (Real.exp τ) = fisherLeaflet (2 * τ) := by
    intro τ
    unfold stereoLeaflet InfoGeometry.Thermodynamics.ProjectiveTemperature.stereographicTemperatureX
    rw [fisherLeaflet_formula]
    have hexp_pos : 0 < Real.exp τ := Real.exp_pos τ
    have hden1 : (Real.exp τ) ^ 2 + 1 ≠ 0 := by positivity
    have hexp2 : Real.exp (2 * τ) = (Real.exp τ) ^ 2 := by
      rw [two_mul, Real.exp_add, sq]
    rw [hexp2]
    field_simp [hden1]
    ring
  refine ⟨?_, ?_, hstereo_fisher, ?_, ?_⟩
  · intro c k ω Δt ΔL Ω h_light h_disp hΩ
    have hcanc := equal_emission_phase_cancellation c k ω ΔL Δt h_light h_disp
    have hnorm : minkowskiNorm (slitRayDisplacement c Δt ΔL) = 0 := hcanc.2.2.1
    have hconf : Ω ^ 2 * minkowskiNorm (slitRayDisplacement c Δt ΔL) = 0 :=
      (conformal_null_invariance (minkowskiNorm (slitRayDisplacement c Δt ΔL)) Ω hΩ).mpr hnorm
    exact ⟨hnorm, hcanc.2.2.2.1, hconf, hcanc.1, hcanc.2.1⟩
  · intro c k ω hc h_disp
    have hnull : IsMinkowskiNull (waveFourVector c ω k) :=
      (equal_emission_phase_cancellation c k ω (c * 0) 0 rfl h_disp).2.2.2.2 hc
    have hdet : (pauliSoldering (waveFourVector c ω k)).det = 0 :=
      (null_iff_det_pauliSoldering_zero (waveFourVector c ω k)).mp hnull
    exact ⟨hnull, hdet⟩
  · intro c τ_coh k Δt I₀ hc hτ
    have h_vis0 : coherenceVisibility τ_coh 0 = 1 := by
      unfold coherenceVisibility
      rw [abs_zero, zero_div, sub_zero, max_eq_right zero_le_one]
    have h_f0 : fisherLeaflet 0 = 1 := (hfisher_prop 0).2.2.1.mpr rfl
    have h_s0 : stereoLeaflet (Real.exp 0) = 1 := by
      rw [hstereo_fisher 0, mul_zero]
      exact h_f0
    have h_int0 : twoSlitIntensity I₀ τ_coh k (c * k) (c * Δt) Δt 0 = 4 * I₀ := by
      unfold twoSlitIntensity
      have htot0 : totalSlitPhaseDiff k (c * k) (c * Δt) Δt 0 = 0 := by
        unfold totalSlitPhaseDiff propPhaseDiff sourcePhaseDiff
        ring
      rw [h_vis0, htot0, Real.cos_zero]
      ring
    have h_sym_peak : ∀ Δt_src : ℝ,
        coherenceVisibility τ_coh (-Δt_src) = coherenceVisibility τ_coh Δt_src ∧
        (coherenceVisibility τ_coh Δt_src = 1 ↔ Δt_src = 0) := by
      intro Δt_src
      have hsym : coherenceVisibility τ_coh (-Δt_src) = coherenceVisibility τ_coh Δt_src := by
        unfold coherenceVisibility
        rw [abs_neg]
      have hpeak : coherenceVisibility τ_coh Δt_src = 1 ↔ Δt_src = 0 := by
        unfold coherenceVisibility
        constructor
        · intro hmax
          rcases le_or_gt (1 - |Δt_src| / τ_coh) 0 with hle | hlt
          · rw [max_eq_left hle] at hmax
            linarith
          · rw [max_eq_right hlt.le] at hmax
            have hdiv0 : |Δt_src| / τ_coh = 0 := by linarith
            have habs0 : |Δt_src| = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right hτ.ne'
            exact abs_eq_zero.mp habs0
        · intro hz
          rw [hz, abs_zero, zero_div, sub_zero, max_eq_right zero_le_one]
      exact ⟨hsym, hpeak⟩
    have h_tail : ∀ ΔL : ℝ, c * τ_coh < |ΔL| →
        coherenceVisibility τ_coh (ΔL / c) = 0 ∧
        twoSlitIntensity I₀ τ_coh k (c * k) ΔL Δt (ΔL / c) = 2 * I₀ ∧
        0 < fisherLeaflet (ΔL / (c * τ_coh)) ∧
        fisherLeaflet (ΔL / (c * τ_coh)) < 1 := by
      intro ΔL hgt
      have hcut := (coherence_window_and_fringe_cutoff c τ_coh ΔL (ΔL / c) I₀ k (c * k) Δt
        hc hτ rfl).2.2.2.1 hgt
      have hfp := hfisher_prop (ΔL / (c * τ_coh))
      have hne0 : ΔL / (c * τ_coh) ≠ 0 := by
        intro hz
        have hΔL0 : ΔL = 0 := (div_eq_zero_iff.mp hz).resolve_right (mul_pos hc hτ).ne'
        rw [hΔL0, abs_zero] at hgt
        linarith [mul_pos hc hτ]
      have hlt1 : fisherLeaflet (ΔL / (c * τ_coh)) < 1 :=
        lt_of_le_of_ne hfp.2.1 (fun heq => hne0 (hfp.2.2.1.mp heq))
      exact ⟨hcut.2.1, hcut.2.2, hfp.1, hlt1⟩
    have hcτ_pos : 0 < c * τ_coh := mul_pos hc hτ
    have h_vis_top :
        Filter.Tendsto (fun ΔL : ℝ => coherenceVisibility τ_coh (ΔL / c))
          Filter.atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (c * τ_coh)] with ΔL hΔL
      have hgt : c * τ_coh < |ΔL| := lt_of_lt_of_le hΔL (le_abs_self ΔL)
      exact (h_tail ΔL hgt).1.symm
    have h_vis_bot :
        Filter.Tendsto (fun ΔL : ℝ => coherenceVisibility τ_coh (ΔL / c))
          Filter.atBot (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_lt_atBot (-(c * τ_coh))] with ΔL hΔL
      have hgt : c * τ_coh < |ΔL| := lt_of_lt_of_le (by linarith) (neg_le_abs ΔL)
      exact (h_tail ΔL hgt).1.symm
    have h_div_top :
        Filter.Tendsto (fun ΔL : ℝ => ΔL / (c * τ_coh)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_div_const hcτ_pos Filter.tendsto_id
    have h_div_bot :
        Filter.Tendsto (fun ΔL : ℝ => ΔL / (c * τ_coh)) Filter.atBot Filter.atBot :=
      Filter.Tendsto.atBot_div_const hcτ_pos Filter.tendsto_id
    refine ⟨h_vis0, h_f0, h_s0, h_int0, h_sym_peak, h_tail, h_vis_top, h_vis_bot,
      hfisher_lim.1.comp h_div_top, hfisher_lim.2.comp h_div_bot, hstereo_lim.1, hstereo_lim.2⟩
  · intro ΔΦ β α θ I₀ τ_coh k ω ΔL Δt hτ hΦ
    set W := twoSlitInterferometerOp ΔΦ
    set ρ := gramBlochState W
    have hW := twoSlitInterferometerOp_unitary_and_det_ne_zero ΔΦ
    have hfringe :
        2 * I₀ * (2 * Complex.normSq (W 0 0)) = twoSlitIntensity I₀ τ_coh k ω ΔL Δt 0 := by
      have hnorm := twoSlitInterferometerOp_fringe_normSq ΔΦ
      have h_vis0 : coherenceVisibility τ_coh 0 = 1 := by
        unfold coherenceVisibility
        rw [abs_zero, zero_div, sub_zero, max_eq_right zero_le_one]
      unfold twoSlitIntensity
      rw [hnorm, h_vis0, one_mul, hΦ]
    have hgauge : gramBlochState (scaleGaugeMultiplier β α • W) = ρ :=
      hgram.2.2.1 β α W
    have hum := hgram.2.2.2 W θ hW.2.2
    exact ⟨hW.1, hfringe, hgauge, hum.1, hum.2.1, hum.2.2.1, hum.2.2.2.1, hum.2.2.2.2.1,
      hum.2.2.2.2.2⟩

/-! ## 5. Certified `TypedArchetype` Registration for `R₂` -/

/-- Proved `TypedArchetype` for `R₂`: double-slit spacetime phase cancellation, source phase
restoration, finite coherence window cutoff, and null-ray / leaflet / Bloch–Umegaki bridge. -/
def archR2DoubleSlitSpacetimeCoherence : TypedArchetype Unit .proved where
  name := `archR2DoubleSlitSpacetimeCoherence
  phase := 2
  claim := fun _ =>
    (∀ c k ω ΔL Δt : ℝ, ΔL = c * Δt → ω = c * k →
      propPhaseDiff k ω ΔL Δt = 0 ∧
      IsMinkowskiNull (slitRayDisplacement c Δt ΔL)) ∧
    (∀ c k ω ΔL Δt Δt_src : ℝ, c ≠ 0 → ΔL = c * Δt → ω = c * k → Δt_src = ΔL / c →
      totalSlitPhaseDiff k ω ΔL Δt Δt_src = k * ΔL) ∧
    (∀ c τ_coh ΔL Δt_src I₀ k ω Δt : ℝ, 0 < c → 0 < τ_coh → Δt_src = ΔL / c →
      (IsWithinCoherenceWindow τ_coh Δt_src ↔ |ΔL| ≤ c * τ_coh) ∧
      (c * τ_coh < |ΔL| →
        coherenceVisibility τ_coh Δt_src = 0 ∧
        twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src = 2 * I₀)) ∧
    (∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A)
  evidence := fun _ =>
    ⟨fun c k ω ΔL Δt hl hd =>
      let h := equal_emission_phase_cancellation c k ω ΔL Δt hl hd
      ⟨h.1, h.2.2.1⟩,
     fun c k ω ΔL Δt Δt_src hc hl hd hs =>
      (earlier_emission_phase_restoration c k ω ΔL Δt Δt_src hc hl hd hs).2.2.1,
     fun c τ_coh ΔL Δt_src I₀ k ω Δt hc hτ hs =>
      let h := coherence_window_and_fringe_cutoff c τ_coh ΔL Δt_src I₀ k ω Δt hc hτ hs
      ⟨h.1, fun hgt => ⟨(h.2.2.2.1 hgt).2.1, (h.2.2.2.1 hgt).2.2⟩⟩,
     doubleSlit_matrix2_noncommutative⟩

#register_archetype archR2DoubleSlitSpacetimeCoherence
#audit_archetype archR2DoubleSlitSpacetimeCoherence

end InfoGeometry.Optics.MannheimDoubleSlitSpacetimeCoherence
