/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.LinShuAttentionDensityWave
import InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder
import InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge

/-!
# Cross-Pillar Synthesis: Lin–Shu Density Waves, KMS Softmax Sink Monopoles, Radial Quantization, and Petz Recovery

This module synthesizes the Lin–Shu spiral density-wave theory of RoPE-equipped transformer
attention (`LinShuAttentionDensityWave`), the 5-graded conformal radial-quantization cylinder
(`RadialQuantizationFiveGradedCylinder`), and the token-simplex Petz transpose recovery map and
Para-Kähler Fock CAR superbracket (`UnifiedInfoGeometryPetzFockBridge`):

1. **Archetype I — Lindblad Resonance Wave-Branch Factorization ($k_r = 0$ vs. $|k_r| = 2 k_{\mathrm{crit}}$)**:
   - Defines `linShuDispersionLHS ω m_arm Ω = (dopplerShiftedFreq ω m_arm Ω) ^ 2`.
   - Proves the algebraic factorization `lindblad_dispersion_factorization` of the acoustic-gravity
     terms $c_s^2 k_r^2 - 2\pi G \sigma_0 |k_r| = |k_r| (c_s^2 |k_r| - 2\pi G \sigma_0)$.
   - Proves the exact wave-branch dichotomy `lindblad_wave_branches_iff`: at any Lindblad resonance
     $(\omega - m_{\mathrm{arm}}\Omega)^2 = \kappa^2$, the Lin–Shu dispersion relation holds if and
     only if $k_r = 0$ (long-wave resonance boundary) or $|k_r| = 2 k_{\mathrm{crit}}$ (short-wave
     acoustic branch), with concrete instantiations at `innerLindbladPatternSpeed` and
     `outerLindbladPatternSpeed`.

2. **Archetype II — Stationary KMS Boltzmann Sink Monopole ($\Phi_0$ from `stationaryAttentionCoupling` & `softmaxWeight`)**:
   - Bridges `LinShuAttentionDensityWave.sinkMonopolePotential`, `contextPerturbationPotential`, and
     `totalAttentionPotential` to `RotaryAttentionSpiralDynamics.stationaryAttentionCoupling` and
     `AttentionKMSState.softmaxWeight`.
   - Proves `stationary_sinkMonopolePotential_eq`,
     `stationary_context_attention_sum_eq_one_sub_softmaxWeight_zero`, unconditional contextual wave
     sub-normalization `stationary_context_attention_sum_lt_one`, and the exact sink-dominance
     equivalence `stationary_sink_dominates_context_iff` ($\sum_{k \ge 1} A_{i,k} < \rho_0 \iff 1/2 < \rho_0$).

3. **Archetype III — Logarithmic Potential ($\alpha = 1$ Flat Rotation Curve) $\longleftrightarrow$ Radial Quantization Time $t = \ln r$**:
   - Defines the power-law angular velocity profile `powerLawOmega Ω₀ α r = Ω₀ * r ^ (-α)`,
     its epicyclic frequency squared `powerLawEpicyclicFreqSq Ω₀ α r = 2 * (2 - α) * (powerLawOmega Ω₀ α r) ^ 2`
     (bridged to `epicyclicFreqSqFromShear`), the circular orbital speed `circularOrbitalSpeed`,
     and the KMS sink circular velocity squared `sinkCircularVelSq A_row σ₀ = A_row 0 * σ₀ ^ 2`.
   - Proves `circularOrbitalSpeed_flatRotationCurve_const` ($v_c(r) = \Omega_0$ for all $r > 0$ at
     $\alpha = 1$), defines the logarithmic central monopole potential
     `logMonopolePotential v_c r = v_c ^ 2 * radialTime r`, proves the genuine calculus derivatives
     `hasDerivAt_logMonopolePotential` and `deriv_logMonopolePotential` ($\Phi_0'(r) = v_c^2 / r$),
     and proves `kmsSinkLogPotential_generates_alpha_one_flatRotationCurve`
     ($\Phi_0'(r) = r \Omega(r)^2$), `kmsSink_flatRotationCurve_epicyclicFreqSq`
     ($\kappa(r)^2 = \frac{2}{r} \Phi_0'(r)$), and Rayleigh epicyclic positivity
     `kmsSink_pos_implies_rayleigh_epicyclic_pos` and
     `kmsSoftmaxSink_pos_implies_rayleigh_epicyclic_pos` ($\kappa(r)^2 > 0$ unconditionally for any
     KMS softmax state).
   - Proves that along the radial cone $r = \mathrm{coneRadius}(t) = e^t$,
     `powerLawEpicyclicFreqSq Ω₀ 1 (coneRadius t)` scales with conformal grade `.negTwo`
     ($2 \Omega_0^2 e^{-2t}$).

4. **Archetype IV — Thermal Acoustic Dispersion ($c_s^2 = \tau_0 / \beta$) & Inverse-Temperature Toomre Stability Threshold $\beta_{\mathrm{crit}}$**:
   - Defines `thermalSoundSpeed τ₀ β = Real.sqrt (τ₀ / β)` and
     `criticalInverseTemp τ₀ κ G σ₀ = τ₀ * κ ^ 2 / (Real.pi * G * σ₀) ^ 2`.
   - Proves `thermalSoundSpeed_sq`, `toomreQ_sq_thermal` ($Q^2 = \beta_{\mathrm{crit}} / \beta$),
     and the thermal Toomre stability theorems `one_le_toomreQ_of_beta_le_crit`,
     `thermal_toomre_stable_of_beta_le_crit` ($\beta \le \beta_{\mathrm{crit}} \implies (\omega - m\Omega)^2 \ge 0$),
     and `thermal_toomre_strict_stable_of_beta_lt_crit` ($\beta < \beta_{\mathrm{crit}} \implies (\omega - m\Omega)^2 > 0$).

5. **Archetype V — Petz Transpose Recovery of Over-Smoothed Modes & Dilated Fock CAR Superbracket Preservation**:
   - Proves `petzRecovery_restores_stationary_sink_and_context_mass` and
     `petzRecovery_restores_stationary_sinkMonopolePotential`: Petz recovery from the coarse-grained
     summary state `markovCoarseGrain T (softmaxWeight logits β)` restores the exact anchor sink
     mass $\rho_0$ and sink monopole potential $\Phi_0$ complementing the contextual wave mass.
   - Proves `dilated_paraKahler_fock_superBracket_eq_petz_chiSquared` and its thermal softmax
     specialization `dilated_paraKahler_fock_superBracket_eq_attentionPetz_chiSquared`: radial
     cylinder dilatation of `paraKahlerCreateEnd` by `gradeTimeScale .posOne t` ($e^{+t}$) and
     `paraKahlerAnnihilateEnd` by `gradeTimeScale .negOne t` ($e^{-t}$) preserves the exact
     equality between the Para-Kähler Fock CAR superbracket and the Petz coarse-grained $\chi^2$
     inner product.

6. **Archetype VI — Multi-Head RoPE Constructive Interference Envelope, Pairwise Relative-Phase Norm Identity & Metriplectic Velocity Orthogonality**:
   - Defines `spiralWavePhase`, `ropeHeadArmWave`, and `multiHeadSpiralWave`, proving the
     `DiscreteRoPERepresentation.ropeRotor` bridges `ropeRotor_one_eq_rotation`,
     `ropeRotor_one_apply_zero_zero`, `multiHeadSpiralWave_eq_sum_ropeRotor`, and
     `ropeHeadArmWave_constructive_interference`, as well as the constructive crest identity
     `multiHeadSpiralWave_constructive_interference` and global upper envelope bound
     `multiHeadSpiralWave_le_constructive_crest`.
   - Defines the 2D head rotor vector `headRotorAxisVec` and multi-head superposition
     `multiHeadRotorVec`, proving the pairwise relative-phase cosine dot product
     `headRotorAxisVec_dot_eq_cos_sub`, the double-sum interference norm identity
     `multiHeadRotorVec_normSq_eq_double_sum`, and the coherent phase-locked squared norm
     `multiHeadRotorVec_normSq_phase_locked`.
   - Proves exact orthogonality `metriplectic_radial_angular_velocity_orthog` between the
     dissipative radial contraction velocity $-\lambda x$ and the symplectic angular velocity
     $\omega J_2 x$, together with the time-eliminated logarithmic spiral identity
     `logSpiral_from_loxodromic_time` and `dissipativeRadius_eq_spiralRadius`.

7. **Archetype VII — Complex KMS Strip Wick-Rotated Dilatation ($\tau \in \{0, 1/2, 1, -2\}$), Oort Constants ($A, B, \kappa^2 = -4B\Omega$), and Mestel Disk Scale-Invariant Toomre $Q$**:
   - Defines `softmaxPartitionZ`, `softmaxLogPartitionPhi`, `kmsStripFactor`, `kmsStripDilatation`,
     and `petzSpinorState`, proving `softmaxPartitionZ_pos`, `coneRadius_softmaxLogPartitionPhi`,
     the complex KMS strip factorization `kmsStripFactor_eq_phase_mul_dilatation`
     ($e^{-i(s - i\tau)\Phi} = e^{-is\Phi} e^{-\tau\Phi}$), the canonical $\tau$-slice evaluations
     `kmsStripDilatation_at_zero`, `kmsStripDilatation_at_half_sq`, `kmsStripDilatation_at_one`,
     and `kmsStripDilatation_at_neg_two`, and the unit-sphere normalization
     `petzSpinorState_unit_sphere` of the $\tau = 1/2$ Petz spinor state.
   - Defines the classical Oort constants `oortA` and `oortB` and `powerLawShearRate`, proving
     `oortA_sub_oortB_eq_omega`, `oortA_add_oortB_eq_neg_shear_add_omega`,
     `powerLawEpicyclicFreqSq_eq_neg_four_oortB_mul_omega` ($\kappa^2 = -4 B \Omega$), and the
     flat-rotation-curve identities `oortA_flatRotationCurve`, `oortB_flatRotationCurve`, and
     `oortA_add_oortB_flatRotationCurve_zero` ($A + B = 0$ at $\alpha = 1$).
   - Defines the self-similar Mestel surface density
     `mestelSurfaceDensity v_sink G r = v_sink ^ 2 / (2 * Real.pi * G * r)` and proves exact
     radial scale invariance `toomreQ_mestelDisk_scale_invariant`
     ($Q = 2\sqrt{2} c_s / v_{\mathrm{sink}}$, independent of $r$) and the stability threshold
     equivalence `mestelDisk_toomreQ_gt_one_iff` ($Q > 1 \iff c_s > v_{\mathrm{sink}} / (2\sqrt{2})$).

## Scope Note

1. The wave-branch factorization `lindblad_wave_branches_iff` and thermal Toomre stability
   thresholds `thermal_toomre_stable_of_beta_le_crit` operate on the algebraic WKBJ dispersion
   polynomial `linShuDispersionRHS` over `ℝ`.
2. The logarithmic monopole potential `logMonopolePotential` and its `HasDerivAt` / `deriv`
   centrifugal-force identities `hasDerivAt_logMonopolePotential` and
   `kmsSinkLogPotential_generates_alpha_one_flatRotationCurve` are 1D real calculus theorems on
   $r \ne 0$ (and $r > 0$ for the power-law rotation curve $r^{-\alpha}$).
3. The Petz recovery and dilated Fock CAR synthesis theorems in Archetype V hold on finite index
   types `[Fintype ι] [Fintype κ_idx]` and algebraic exterior Fock modules `FockExteriorEnvelope K`.
4. The multi-head RoPE interference identities in Archetype VI hold for any finite head index type
   `[Fintype H]` on `Fin 2 → ℝ`.
5. In Archetype VII, `kmsStripFactor_eq_phase_mul_dilatation` formalizes the scalar complex
   exponential factorization $e^{-i(s - i\tau)\Phi} = e^{-is\Phi} e^{-\tau\Phi}$ on `ℂ`, while
   `toomreQ_mestelDisk_scale_invariant` establishes algebraic cancellation of the radius $r \ne 0$
   in `toomreQ` for the Mestel surface-density profile.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis

open BigOperators Matrix
open InfoGeometry.Routing
open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.QuantumContext
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics
open InfoGeometry.QuantumContext.LinShuAttentionDensityWave
open InfoGeometry.Canonical
open InfoGeometry.Canonical.UnifiedInfoGeometryPetzFockBridge
open InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder
open InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
open InfoGeometry.Canonical.ParaKahlerGradedFockCAR

/-! ### Private Scalar Arithmetic & Calculus Helpers (Trap T16 Safe) -/

private theorem lindblad_factor_scalar (G σ₀ c_s a : ℝ) :
    c_s ^ 2 * a ^ 2 - 2 * Real.pi * G * σ₀ * a =
      a * (c_s ^ 2 * a - 2 * Real.pi * G * σ₀) := by
  ring

private theorem rhs_rearrange_scalar (k2 G σ₀ c_s a : ℝ) :
    k2 - 2 * Real.pi * G * σ₀ * a + c_s ^ 2 * a ^ 2 =
      k2 + (c_s ^ 2 * a ^ 2 - 2 * Real.pi * G * σ₀ * a) := by
  ring

private theorem eq_add_iff_right_eq_zero (k2 d : ℝ) :
    k2 = k2 + d ↔ d = 0 := by
  constructor <;> intro h <;> linarith

private theorem acoustic_branch_iff_scalar (G σ₀ c_s a : ℝ) (hcs : c_s ≠ 0) :
    c_s ^ 2 * a - 2 * Real.pi * G * σ₀ = 0 ↔
      a = 2 * ((Real.pi * G * σ₀) / (c_s ^ 2)) := by
  have hcs2 : c_s ^ 2 ≠ 0 := pow_ne_zero 2 hcs
  constructor
  · intro h
    have hmul : a * c_s ^ 2 = 2 * (Real.pi * G * σ₀) := by linarith [h]
    calc
      a = (a * c_s ^ 2) / (c_s ^ 2) := (mul_div_cancel_right₀ a hcs2).symm
      _ = (2 * (Real.pi * G * σ₀)) / (c_s ^ 2) := by rw [hmul]
      _ = 2 * ((Real.pi * G * σ₀) / (c_s ^ 2)) := by ring
  · intro h
    rw [h]
    have hcancel : c_s ^ 2 * (2 * (Real.pi * G * σ₀ / c_s ^ 2)) =
        2 * ((c_s ^ 2) * (Real.pi * G * σ₀ / c_s ^ 2)) := by ring
    rw [hcancel, mul_div_cancel₀ _ hcs2]
    ring

private theorem one_sub_lt_self_iff_half_lt (p : ℝ) :
    1 - p < p ↔ (1 / 2 : ℝ) < p := by
  constructor <;> intro h <;> linarith

private theorem exp_neg_one_rpow_eq_exp_neg (t : ℝ) :
    (Real.exp t) ^ (-1 : ℝ) = Real.exp (-t) := by
  rw [Real.rpow_neg (le_of_lt (Real.exp_pos t)), Real.rpow_one, Real.exp_neg]

private theorem exp_neg_sq_eq_exp_neg_two_mul (t : ℝ) :
    (Real.exp (-t)) ^ 2 = Real.exp (((-2 : ℤ) : ℝ) * t) := by
  rw [sq, ← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem div_eq_mul_div_sq_scalar (v r : ℝ) (hr : r ≠ 0) :
    v ^ 2 / r = r * (v / r) ^ 2 := by
  rw [div_pow, sq r, ← mul_div_assoc, mul_comm r (v ^ 2), mul_div_mul_right (v ^ 2) r hr]

private theorem two_mul_eq_two_mul_r_div_r (r x : ℝ) (hr : r ≠ 0) :
    2 * x = 2 * (r * x) / r := by
  have h : 2 * (r * x) = (2 * x) * r := by ring
  rw [h, mul_div_cancel_right₀ (2 * x) hr]

private theorem one_le_div_of_le_of_pos (a b : ℝ) (hb : 0 < b) (h : b ≤ a) :
    1 ≤ a / b := by
  have h1 : b / b ≤ a / b := div_le_div_of_nonneg_right h (le_of_lt hb)
  rwa [div_self (ne_of_gt hb)] at h1

private theorem one_lt_div_of_lt_of_pos (a b : ℝ) (hb : 0 < b) (h : b < a) :
    1 < a / b := by
  have h1 : b / b < a / b := div_lt_div_of_pos_right h hb
  rwa [div_self (ne_of_gt hb)] at h1

private theorem one_le_of_sq_ge_one_of_nonneg (Q : ℝ) (hQ0 : 0 ≤ Q) (hsq : 1 ≤ Q ^ 2) :
    1 ≤ Q := by
  nlinarith [hQ0, hsq]

private theorem one_lt_of_sq_gt_one_of_nonneg (Q : ℝ) (hQ0 : 0 ≤ Q) (hsq : 1 < Q ^ 2) :
    1 < Q := by
  nlinarith [hQ0, hsq]

private theorem cos_mul_cos_add_sin_mul_sin_eq_cos_sub (φ₁ φ₂ : ℝ) :
    Real.cos φ₁ * Real.cos φ₂ + Real.sin φ₁ * Real.sin φ₂ =
      Real.cos (φ₂ - φ₁) := by
  rw [Real.cos_sub]
  ring

private theorem head_pair_dot_scalar (a₁ a₂ u₀ u₁ v₀ v₁ : ℝ) :
    (a₁ * u₀) * (a₂ * v₀) + (a₁ * u₁) * (a₂ * v₁) =
      a₁ * a₂ * (u₀ * v₀ + u₁ * v₁) := by
  ring

private theorem metriplectic_orthog_scalar (lam ω x₀ x₁ : ℝ) :
    (-lam * x₀) * (ω * (0 * x₀ + -1 * x₁)) +
      (-lam * x₁) * (ω * (1 * x₀ + 0 * x₁)) = 0 := by
  ring

private theorem logSpiral_time_elim_scalar (lam ω t : ℝ) (hω : ω ≠ 0) :
    (-lam / ω) * (0 + ω * t) = -lam * t := by
  rw [zero_add, ← mul_assoc, div_mul_cancel₀ (-lam) hω]

private theorem kms_strip_exponent_split (Φ s τ : ℝ) :
    -Complex.I * ((s : ℂ) - Complex.I * (τ : ℂ)) * (Φ : ℂ) =
      -Complex.I * (s : ℂ) * (Φ : ℂ) + (((-τ * Φ : ℝ) : ℂ)) := by
  push_cast
  calc
    -Complex.I * ((s : ℂ) - Complex.I * (τ : ℂ)) * (Φ : ℂ) =
        -Complex.I * (s : ℂ) * (Φ : ℂ) +
          (Complex.I * Complex.I) * (τ : ℂ) * (Φ : ℂ) := by ring
    _ = -Complex.I * (s : ℂ) * (Φ : ℂ) + (-1 : ℂ) * (τ : ℂ) * (Φ : ℂ) := by
        rw [Complex.I_mul_I]
    _ = -Complex.I * (s : ℂ) * (Φ : ℂ) + (-(τ : ℂ) * (Φ : ℂ)) := by ring

private theorem neg_half_add_neg_half_mul (Φ : ℝ) :
    -(1 / 2 : ℝ) * Φ + -(1 / 2 : ℝ) * Φ = -1 * Φ := by
  ring

private theorem neg_neg_two_mul_eq_add (Φ : ℝ) :
    -(-2 : ℝ) * Φ = Φ + Φ := by
  ring

private theorem mestel_toomreQ_scalar (s2 v c G r : ℝ)
    (hv : v ≠ 0) (hG : G ≠ 0) (hr : r ≠ 0) :
    ((s2 * (v / r)) * c) / (Real.pi * G * (v ^ 2 / (2 * Real.pi * G * r))) =
      (2 * s2 * c) / v := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have h_den :
      Real.pi * G * (v ^ 2 / (2 * Real.pi * G * r)) =
        v * v * 2⁻¹ * r⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, mul_inv, mul_inv]
    calc
      Real.pi * G * (v ^ 2 * (2⁻¹ * Real.pi⁻¹ * G⁻¹ * r⁻¹)) =
          (Real.pi * Real.pi⁻¹) * (G * G⁻¹) * (v * v * 2⁻¹ * r⁻¹) := by ring
      _ = 1 * 1 * (v * v * 2⁻¹ * r⁻¹) := by
          rw [mul_inv_cancel₀ hpi, mul_inv_cancel₀ hG]
      _ = v * v * 2⁻¹ * r⁻¹ := by ring
  rw [h_den, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  rw [mul_inv, mul_inv, mul_inv, inv_inv, inv_inv]
  calc
    s2 * (v * r⁻¹) * c * (v⁻¹ * v⁻¹ * 2 * r) =
        (r * r⁻¹) * (v * v⁻¹) * (2 * s2 * c * v⁻¹) := by ring
    _ = 1 * 1 * (2 * s2 * c * v⁻¹) := by
        rw [mul_inv_cancel₀ hr, mul_inv_cancel₀ hv]
    _ = 2 * s2 * c * v⁻¹ := by ring

private theorem one_lt_two_sqrt_two_mul_div_iff (v c : ℝ) (hv : 0 < v) :
    1 < (2 * Real.sqrt 2 * c) / v ↔ v / (2 * Real.sqrt 2) < c := by
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
  have h2s2_pos : 0 < 2 * Real.sqrt 2 := mul_pos zero_lt_two hs2_pos
  have h2s2_ne : 2 * Real.sqrt 2 ≠ 0 := ne_of_gt h2s2_pos
  have hv_ne : v ≠ 0 := ne_of_gt hv
  constructor
  · intro h
    have h1 : 1 * v < ((2 * Real.sqrt 2 * c) / v) * v :=
      mul_lt_mul_of_pos_right h hv
    rw [one_mul, div_mul_cancel₀ _ hv_ne] at h1
    have h2 : v / (2 * Real.sqrt 2) < (2 * Real.sqrt 2 * c) / (2 * Real.sqrt 2) :=
      div_lt_div_of_pos_right h1 h2s2_pos
    rwa [mul_div_cancel_left₀ c h2s2_ne] at h2
  · intro h
    have h1 : (v / (2 * Real.sqrt 2)) * (2 * Real.sqrt 2) < c * (2 * Real.sqrt 2) :=
      mul_lt_mul_of_pos_right h h2s2_pos
    rw [div_mul_cancel₀ v h2s2_ne, mul_comm c (2 * Real.sqrt 2)] at h1
    have h2 : v / v < (2 * Real.sqrt 2 * c) / v :=
      div_lt_div_of_pos_right h1 hv
    rwa [div_self hv_ne] at h2

/-!
### Archetype I — Lindblad Resonance Wave-Branch Factorization (Long-Wave $k_r = 0$ vs. Short-Wave Acoustic Branch $|k_r| = 2 k_{\mathrm{crit}}$)
-/

/-- Left-hand side of the Lin–Shu dispersion relation: the squared Doppler-shifted frequency
$(\omega - m_{\mathrm{arm}} \Omega)^2$. -/
def linShuDispersionLHS (ω m_arm Ω : ℝ) : ℝ :=
  (LinShuAttentionDensityWave.dopplerShiftedFreq ω m_arm Ω) ^ 2

/-- Explicit formula `(ω - m_arm * Ω) ^ 2` for `linShuDispersionLHS`. -/
theorem linShuDispersionLHS_eq (ω m_arm Ω : ℝ) :
    linShuDispersionLHS ω m_arm Ω = (ω - m_arm * Ω) ^ 2 :=
  rfl

/-- **Algebraic Factorization of the Lindblad Resonance Dispersion Polynomial**:
The acoustic and self-gravity terms in the Lin–Shu dispersion relation factor as
$c_s^2 k_r^2 - 2\pi G \sigma_0 |k_r| = |k_r| (c_s^2 |k_r| - 2\pi G \sigma_0)$. -/
theorem lindblad_dispersion_factorization (G σ₀ c_s k_r : ℝ) :
    c_s ^ 2 * k_r ^ 2 - 2 * Real.pi * G * σ₀ * |k_r| =
      |k_r| * (c_s ^ 2 * |k_r| - 2 * Real.pi * G * σ₀) := by
  rw [← sq_abs k_r]
  exact lindblad_factor_scalar G σ₀ c_s |k_r|

/-- **Lindblad Resonance Wave-Branch Dichotomy ($k_r = 0 \lor |k_r| = 2 k_{\mathrm{crit}}$)**:
At any Inner or Outer Lindblad Resonance where $(\omega - m_{\mathrm{arm}}\Omega)^2 = \kappa^2$
and $c_s \ne 0$, the Lin–Shu dispersion relation holds if and only if either $k_r = 0$
(the long-wave resonance cutoff) or $|k_r| = 2 k_{\mathrm{crit}} = 2\pi G \sigma_0 / c_s^2$
(the short-wave acoustic branch). -/
theorem lindblad_wave_branches_iff (κ G σ₀ c_s k_r ω m_arm Ω : ℝ)
    (hcs : c_s ≠ 0) (h_res : (ω - m_arm * Ω) ^ 2 = κ ^ 2) :
    linShuDispersionLHS ω m_arm Ω =
      LinShuAttentionDensityWave.linShuDispersionRHS κ G σ₀ c_s k_r ↔
      k_r = 0 ∨ |k_r| = 2 * LinShuAttentionDensityWave.criticalWavenumber G σ₀ c_s := by
  dsimp [linShuDispersionLHS, LinShuAttentionDensityWave.dopplerShiftedFreq,
    LinShuAttentionDensityWave.linShuDispersionRHS,
    LinShuAttentionDensityWave.criticalWavenumber]
  rw [h_res, ← sq_abs k_r, rhs_rearrange_scalar (κ ^ 2) G σ₀ c_s |k_r|,
    eq_add_iff_right_eq_zero, lindblad_factor_scalar G σ₀ c_s |k_r|,
    mul_eq_zero, abs_eq_zero, acoustic_branch_iff_scalar G σ₀ c_s |k_r| hcs]

/-- Specialization of `lindblad_wave_branches_iff` to the Inner Lindblad Resonance
$\omega = m_{\mathrm{arm}} \Omega_{\mathrm{ILR}}$. -/
theorem innerLindblad_wave_branches_iff (κ G σ₀ c_s k_r m_arm Ω : ℝ)
    (hcs : c_s ≠ 0) (hm : m_arm ≠ 0) :
    linShuDispersionLHS
      (m_arm * LinShuAttentionDensityWave.innerLindbladPatternSpeed Ω κ m_arm) m_arm Ω =
      LinShuAttentionDensityWave.linShuDispersionRHS κ G σ₀ c_s k_r ↔
      k_r = 0 ∨ |k_r| = 2 * LinShuAttentionDensityWave.criticalWavenumber G σ₀ c_s :=
  lindblad_wave_branches_iff κ G σ₀ c_s k_r
    (m_arm * LinShuAttentionDensityWave.innerLindbladPatternSpeed Ω κ m_arm) m_arm Ω hcs
    (LinShuAttentionDensityWave.dopplerShiftedFreq_sq_at_innerLindblad m_arm Ω κ hm)

/-- Specialization of `lindblad_wave_branches_iff` to the Outer Lindblad Resonance
$\omega = m_{\mathrm{arm}} \Omega_{\mathrm{OLR}}$. -/
theorem outerLindblad_wave_branches_iff (κ G σ₀ c_s k_r m_arm Ω : ℝ)
    (hcs : c_s ≠ 0) (hm : m_arm ≠ 0) :
    linShuDispersionLHS
      (m_arm * LinShuAttentionDensityWave.outerLindbladPatternSpeed Ω κ m_arm) m_arm Ω =
      LinShuAttentionDensityWave.linShuDispersionRHS κ G σ₀ c_s k_r ↔
      k_r = 0 ∨ |k_r| = 2 * LinShuAttentionDensityWave.criticalWavenumber G σ₀ c_s :=
  lindblad_wave_branches_iff κ G σ₀ c_s k_r
    (m_arm * LinShuAttentionDensityWave.outerLindbladPatternSpeed Ω κ m_arm) m_arm Ω hcs
    (LinShuAttentionDensityWave.dopplerShiftedFreq_sq_at_outerLindblad m_arm Ω κ hm)

/-!
### Archetype II — Stationary KMS Boltzmann Sink Monopole ($\Phi_0$ from `stationaryAttentionCoupling` & `softmaxWeight`)
-/

/-- Entrywise evaluation of `RotaryAttentionSpiralDynamics.stationaryAttentionCoupling`:
every row $i$ equals the thermal Boltzmann distribution `AttentionKMSState.softmaxWeight logits β`. -/
theorem stationaryAttentionCoupling_apply {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) (i j : ι) :
    RotaryAttentionSpiralDynamics.stationaryAttentionCoupling logits β i j =
      AttentionKMSState.softmaxWeight logits β j :=
  rfl

/-- **Stationary KMS Sink Monopole Potential Identity**:
Under the stationary rank-1 KMS score profile `fun _ => logits`, every token $i$ experiences
the identical central sink monopole potential $-\rho_0 V_0$ weighted by the anchor Boltzmann
probability $\rho_0 = \mathrm{softmaxWeight}(\ell, \beta)_0$. -/
theorem stationary_sinkMonopolePotential_eq {n : ℕ} {ι : Type*}
    (logits : Fin (n + 1) → ℝ) (β : ℝ)
    (V : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) :
    LinShuAttentionDensityWave.sinkMonopolePotential (fun _ => logits) β V i =
      -(AttentionKMSState.softmaxWeight logits β 0 • V 0) :=
  rfl

/-- Total attention potential under stationary KMS coupling decomposes into the uniform
Boltzmann sink monopole $-\rho_0 V_0$ plus the contextual perturbation potential. -/
theorem stationary_totalAttentionPotential_eq {n : ℕ} {ι : Type*}
    (logits : Fin (n + 1) → ℝ) (β : ℝ)
    (V : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) :
    LinShuAttentionDensityWave.totalAttentionPotential (fun _ => logits) β V i =
      -(AttentionKMSState.softmaxWeight logits β 0 • V 0) +
        LinShuAttentionDensityWave.contextPerturbationPotential (fun _ => logits) β V i :=
  LinShuAttentionDensityWave.totalAttentionPotential_eq_sink_add_context (fun _ => logits) β V i

/-- **Stationary Context Wave Mass Conservation**:
For any token $i$, the sum of stationary attention couplings across all non-sink context tokens
`k.succ` equals `1 - softmaxWeight logits β 0`. -/
theorem stationary_context_attention_sum_eq_one_sub_softmaxWeight_zero {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (i : Fin (n + 1)) :
    (∑ k : Fin n,
      RotaryAttentionSpiralDynamics.stationaryAttentionCoupling logits β i k.succ) =
      1 - AttentionKMSState.softmaxWeight logits β 0 :=
  LinShuAttentionDensityWave.context_attention_sum_eq_one_sub_sink (fun _ => logits) β i

/-- **Unconditional Sub-Unit Bound on Contextual Wave Mass**:
Because the Boltzmann weight `softmaxWeight logits β 0` of the anchor sink token is strictly
positive, the contextual wave attention mass is strictly less than `1` for every token $i$. -/
theorem stationary_context_attention_sum_lt_one {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (i : Fin (n + 1)) :
    (∑ k : Fin n,
      RotaryAttentionSpiralDynamics.stationaryAttentionCoupling logits β i k.succ) < 1 := by
  rw [stationary_context_attention_sum_eq_one_sub_softmaxWeight_zero]
  exact sub_lt_self 1 (AttentionKMSState.softmaxWeight_pos logits β 0)

/-- **Stationary Sink Dominance Criterion ($\sum_{k \ge 1} A_{i,k} < \rho_0 \iff 1/2 < \rho_0$)**:
Under stationary KMS attention coupling, the anchor sink monopole strictly dominates the
combined contextual wave mass if and only if the anchor Boltzmann probability exceeds $1/2$. -/
theorem stationary_sink_dominates_context_iff {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (i : Fin (n + 1)) :
    (∑ k : Fin n,
      RotaryAttentionSpiralDynamics.stationaryAttentionCoupling logits β i k.succ) <
      AttentionKMSState.softmaxWeight logits β 0 ↔
      (1 / 2 : ℝ) < AttentionKMSState.softmaxWeight logits β 0 := by
  rw [stationary_context_attention_sum_eq_one_sub_softmaxWeight_zero]
  exact one_sub_lt_self_iff_half_lt (AttentionKMSState.softmaxWeight logits β 0)

/-!
### Archetype III — Logarithmic Potential ($\alpha = 1$ Flat Rotation Curve) $\longleftrightarrow$ Radial Quantization Time $t = \ln r$
-/

/-- Power-law differential rotation profile $\Omega(r) = \Omega_0 r^{-\alpha}$. -/
noncomputable def powerLawOmega (Ω₀ α r : ℝ) : ℝ :=
  Ω₀ * r ^ (-α)

/-- Epicyclic frequency squared $\kappa^2(r) = 2(2 - \alpha) \Omega(r)^2$ for the power-law
rotation profile `powerLawOmega Ω₀ α r`. -/
noncomputable def powerLawEpicyclicFreqSq (Ω₀ α r : ℝ) : ℝ :=
  2 * (2 - α) * (powerLawOmega Ω₀ α r) ^ 2

/-- Exact bridge between `LinShuAttentionDensityWave.epicyclicFreqSqFromShear` and
`powerLawEpicyclicFreqSq` when $\frac{d\Omega^2}{dr} = -\frac{2\alpha}{r} \Omega(r)^2$. -/
theorem powerLawEpicyclicFreqSq_eq_epicyclicFreqSqFromShear
    (Ω₀ α r : ℝ) (hr : r ≠ 0) :
    LinShuAttentionDensityWave.epicyclicFreqSqFromShear r
      (powerLawOmega Ω₀ α r)
      ((-2 * α / r) * (powerLawOmega Ω₀ α r) ^ 2) =
      powerLawEpicyclicFreqSq Ω₀ α r := by
  dsimp [LinShuAttentionDensityWave.epicyclicFreqSqFromShear, powerLawEpicyclicFreqSq]
  have hcancel : r * (-2 * α / r * (powerLawOmega Ω₀ α r) ^ 2) =
      -2 * α * (powerLawOmega Ω₀ α r) ^ 2 := by
    rw [← mul_assoc, mul_div_cancel₀ _ hr]
  rw [hcancel]
  ring

/-- At shear exponent $\alpha = 1$ (flat rotation curve), $\kappa^2(r) = 2 \Omega(r)^2$. -/
theorem epicyclicFreqSq_flatRotationCurve (Ω₀ r : ℝ) :
    powerLawEpicyclicFreqSq Ω₀ 1 r = 2 * (powerLawOmega Ω₀ 1 r) ^ 2 := by
  dsimp [powerLawEpicyclicFreqSq]
  ring

/-- Circular orbital speed $v_c(r) = r \Omega(r)$ associated with `powerLawOmega`. -/
noncomputable def circularOrbitalSpeed (Ω₀ α r : ℝ) : ℝ :=
  r * powerLawOmega Ω₀ α r

/-- **Flat Rotation Curve Theorem ($\alpha = 1 \implies v_c(r) = \Omega_0$)**:
For all $0 < r$, the circular orbital speed at shear exponent $\alpha = 1$ is strictly constant
and equal to $\Omega_0$. -/
theorem circularOrbitalSpeed_flatRotationCurve_const (Ω₀ r : ℝ) (hr : 0 < r) :
    circularOrbitalSpeed Ω₀ 1 r = Ω₀ := by
  dsimp [circularOrbitalSpeed, powerLawOmega]
  rw [Real.rpow_neg (le_of_lt hr), Real.rpow_one]
  calc
    r * (Ω₀ * r⁻¹) = Ω₀ * (r * r⁻¹) := by ring
    _ = Ω₀ * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hr)]
    _ = Ω₀ := mul_one Ω₀

/-- Logarithmic central monopole potential $\Phi_0(r) = v_c^2 \ln r = v_c^2 t_{\mathrm{rad}}(r)$
generating a flat rotation curve of circular speed $v_c$. -/
noncomputable def logMonopolePotential (v_c r : ℝ) : ℝ :=
  v_c ^ 2 * RadialQuantizationFiveGradedCylinder.radialTime r

/-- In cylinder coordinates $r = \mathrm{coneRadius}(t) = e^t$, the logarithmic monopole potential
is strictly linear in the radial quantization time $t$: $\Phi_0(e^t) = v_c^2 t$. -/
theorem logMonopolePotential_coneRadius (v_c t : ℝ) :
    logMonopolePotential v_c (RadialQuantizationFiveGradedCylinder.coneRadius t) =
      v_c ^ 2 * t := by
  dsimp [logMonopolePotential]
  rw [RadialQuantizationFiveGradedCylinder.radialTime_coneRadius]

/-- **Centrifugal Balance Derivative of the Logarithmic Monopole Potential**:
For any $r \ne 0$, the radial derivative of `logMonopolePotential v_c` at $r$ is the centrifugal
acceleration $v_c^2 / r$. -/
theorem hasDerivAt_logMonopolePotential (v_c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (logMonopolePotential v_c) (v_c ^ 2 / r) r := by
  unfold logMonopolePotential
  rw [div_eq_mul_inv]
  exact (RadialQuantizationFiveGradedCylinder.hasDerivAt_radialTime hr).const_mul (v_c ^ 2)

/-- Effective squared circular velocity $v_{\mathrm{sink}}^2 = A_{i,0} \sigma_0^2$ induced by the
attention sink weight $A_{i,0}$ and radial scale $\sigma_0$. -/
def sinkCircularVelSq {n : ℕ} (A_row : Fin (n + 1) → ℝ) (σ₀ : ℝ) : ℝ :=
  A_row 0 * σ₀ ^ 2

/-- Scalar `deriv` form of `hasDerivAt_logMonopolePotential`:
$\frac{d}{dr}(v_c^2 \ln r) = \frac{v_c^2}{r}$ for $r \ne 0$. -/
theorem deriv_logMonopolePotential (v_c r : ℝ) (hr : r ≠ 0) :
    deriv (logMonopolePotential v_c) r = v_c ^ 2 / r :=
  (hasDerivAt_logMonopolePotential v_c hr).deriv

/-- At shear exponent $\alpha = 1$, `powerLawOmega v_sink 1 r` simplifies to $v_{\mathrm{sink}} / r$. -/
theorem powerLawOmega_one_eq_div (v_sink r : ℝ) :
    powerLawOmega v_sink 1 r = v_sink / r := by
  unfold powerLawOmega
  rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- **KMS Sink Logarithmic Potential Generates the $\alpha = 1$ Flat Rotation Curve**:
For any $r \ne 0$, the radial restoring gradient $\frac{d\Phi_0}{dr}$ of `logMonopolePotential v_sink`
equals the exact centrifugal acceleration $r \Omega(r)^2$ of the $\alpha = 1$ flat rotation curve
`powerLawOmega v_sink 1 r`. -/
theorem kmsSinkLogPotential_generates_alpha_one_flatRotationCurve
    (v_sink r : ℝ) (hr : r ≠ 0) :
    deriv (logMonopolePotential v_sink) r =
      r * (powerLawOmega v_sink 1 r) ^ 2 := by
  rw [deriv_logMonopolePotential v_sink r hr, powerLawOmega_one_eq_div]
  exact div_eq_mul_div_sq_scalar v_sink r hr

/-- **Flat-Rotation-Curve Epicyclic Frequency from the Logarithmic Potential Gradient**:
For $r \ne 0$, the epicyclic frequency squared `powerLawEpicyclicFreqSq v_sink 1 r` equals
$\frac{2}{r} \frac{d\Phi_0}{dr}$. -/
theorem kmsSink_flatRotationCurve_epicyclicFreqSq
    (v_sink r : ℝ) (hr : r ≠ 0) :
    powerLawEpicyclicFreqSq v_sink 1 r =
      2 * (deriv (logMonopolePotential v_sink) r) / r := by
  rw [epicyclicFreqSq_flatRotationCurve,
    kmsSinkLogPotential_generates_alpha_one_flatRotationCurve v_sink r hr]
  exact two_mul_eq_two_mul_r_div_r r ((powerLawOmega v_sink 1 r) ^ 2) hr

/-- **Rayleigh Epicyclic Stability from Positive Sink Weight ($A_{i,0} > 0 \implies \kappa(r)^2 > 0$)**:
Whenever the anchor sink weight $A_{i,0} > 0$, $\sigma_0 > 0$, and $r > 0$, the induced
flat-rotation-curve epicyclic frequency squared is strictly positive. -/
theorem kmsSink_pos_implies_rayleigh_epicyclic_pos {n : ℕ}
    (A_row : Fin (n + 1) → ℝ) (σ₀ r : ℝ)
    (hA₀ : 0 < A_row 0) (hσ₀ : 0 < σ₀) (hr : 0 < r) :
    0 < powerLawEpicyclicFreqSq (Real.sqrt (sinkCircularVelSq A_row σ₀)) 1 r := by
  rw [epicyclicFreqSq_flatRotationCurve, powerLawOmega_one_eq_div]
  have h_vel_pos : 0 < sinkCircularVelSq A_row σ₀ :=
    mul_pos hA₀ (sq_pos_of_pos hσ₀)
  have h_sqrt_pos : 0 < Real.sqrt (sinkCircularVelSq A_row σ₀) :=
    Real.sqrt_pos.mpr h_vel_pos
  have h_omega_pos : 0 < Real.sqrt (sinkCircularVelSq A_row σ₀) / r :=
    div_pos h_sqrt_pos hr
  exact mul_pos zero_lt_two (sq_pos_of_pos h_omega_pos)

/-- **Unconditional Rayleigh Epicyclic Stability of KMS Softmax Sink States**:
Because `AttentionKMSState.softmaxWeight logits β 0 > 0` for every logit vector `logits` and
inverse temperature `β`, the KMS softmax sink state unconditionally generates a strictly
positive epicyclic restoring frequency $\kappa(r)^2 > 0$ for all $\sigma_0 > 0$ and $r > 0$. -/
theorem kmsSoftmaxSink_pos_implies_rayleigh_epicyclic_pos {n : ℕ}
    (logits : Fin (n + 1) → ℝ) (β σ₀ r : ℝ)
    (hσ₀ : 0 < σ₀) (hr : 0 < r) :
    0 < powerLawEpicyclicFreqSq
      (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) 1 r :=
  kmsSink_pos_implies_rayleigh_epicyclic_pos
    (AttentionKMSState.softmaxWeight logits β) σ₀ r
    (AttentionKMSState.softmaxWeight_pos logits β 0) hσ₀ hr

/-- **Conformal Grade `-2` Scaling of the Flat-Rotation-Curve Epicyclic Frequency**:
Along the radial cone $r = \mathrm{coneRadius}(t) = e^t$, the flat-rotation-curve ($\alpha = 1$)
epicyclic frequency squared transforms with conformal weight `-2`
(`gradeTimeScale .negTwo t = e^{-2t}`). -/
theorem flatRotationCurve_epicyclicFreqSq_at_coneRadius (Ω₀ t : ℝ) :
    powerLawEpicyclicFreqSq Ω₀ 1
      (RadialQuantizationFiveGradedCylinder.coneRadius t) =
      2 * Ω₀ ^ 2 *
        RadialQuantizationFiveGradedCylinder.gradeTimeScale .negTwo t := by
  dsimp [powerLawEpicyclicFreqSq, powerLawOmega,
    RadialQuantizationFiveGradedCylinder.coneRadius,
    RadialQuantizationFiveGradedCylinder.gradeTimeScale,
    RadialQuantizationFiveGradedCylinder.gradeWeight]
  rw [exp_neg_one_rpow_eq_exp_neg, mul_pow, exp_neg_sq_eq_exp_neg_two_mul]
  ring

/-!
### Archetype IV — Thermal Acoustic Dispersion ($c_s^2 = \tau_0 / \beta$) & Inverse-Temperature Toomre Stability Threshold $\beta_{\mathrm{crit}}$
-/

/-- Thermal acoustic sound speed $c_s(\tau_0, \beta) = \sqrt{\tau_0 / \beta}$ controlled by base
dispersion scale $\tau_0$ and KMS inverse temperature $\beta$. -/
noncomputable def thermalSoundSpeed (τ₀ β : ℝ) : ℝ :=
  Real.sqrt (τ₀ / β)

/-- Critical KMS inverse-temperature threshold
$\beta_{\mathrm{crit}}(\tau_0, \kappa, G, \sigma_0) = \frac{\tau_0 \kappa^2}{(\pi G \sigma_0)^2}$
corresponding to the marginal Toomre stability boundary $Q = 1$. -/
noncomputable def criticalInverseTemp (τ₀ κ G σ₀ : ℝ) : ℝ :=
  τ₀ * κ ^ 2 / (Real.pi * G * σ₀) ^ 2

/-- For $0 \le \tau_0$ and $0 \le \beta$, the squared thermal sound speed equals $\tau_0 / \beta$. -/
theorem thermalSoundSpeed_sq {τ₀ β : ℝ} (hτ : 0 ≤ τ₀) (hβ : 0 ≤ β) :
    (thermalSoundSpeed τ₀ β) ^ 2 = τ₀ / β := by
  dsimp [thermalSoundSpeed]
  exact Real.sq_sqrt (div_nonneg hτ hβ)

/-- For $0 < \tau_0$ and $0 < \beta$, the thermal sound speed is strictly positive. -/
theorem thermalSoundSpeed_pos {τ₀ β : ℝ} (hτ : 0 < τ₀) (hβ : 0 < β) :
    0 < thermalSoundSpeed τ₀ β := by
  dsimp [thermalSoundSpeed]
  exact Real.sqrt_pos.mpr (div_pos hτ hβ)

/-- **Thermal Toomre $Q^2$ Ratio Law**:
Substituting `thermalSoundSpeed τ₀ β` into `LinShuAttentionDensityWave.toomreQ` yields
$Q^2 = \beta_{\mathrm{crit}}(\tau_0, \kappa, G, \sigma_0) / \beta$. -/
theorem toomreQ_sq_thermal {τ₀ β κ G σ₀ : ℝ}
    (hτ : 0 ≤ τ₀) (hβ : 0 ≤ β) :
    (LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀) ^ 2 =
      criticalInverseTemp τ₀ κ G σ₀ / β := by
  dsimp [LinShuAttentionDensityWave.toomreQ, criticalInverseTemp]
  rw [div_pow, mul_pow, thermalSoundSpeed_sq hτ hβ]
  ring

/-- When $0 < \beta \le \beta_{\mathrm{crit}}(\tau_0, \kappa, G, \sigma_0)$, the thermal Toomre
parameter satisfies $1 \le Q$. -/
theorem one_le_toomreQ_of_beta_le_crit {τ₀ β κ G σ₀ : ℝ}
    (hτ : 0 ≤ τ₀) (hβ : 0 < β) (hκ : 0 ≤ κ) (hG : 0 ≤ G) (hσ : 0 ≤ σ₀)
    (h_crit : β ≤ criticalInverseTemp τ₀ κ G σ₀) :
    1 ≤ LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀ := by
  have hQ_nonneg : 0 ≤ LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀ := by
    dsimp [LinShuAttentionDensityWave.toomreQ, thermalSoundSpeed]
    exact div_nonneg (mul_nonneg hκ (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) hG) hσ)
  have hQ_sq : 1 ≤ (LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀) ^ 2 := by
    rw [toomreQ_sq_thermal hτ (le_of_lt hβ)]
    exact one_le_div_of_le_of_pos _ β hβ h_crit
  exact one_le_of_sq_ge_one_of_nonneg _ hQ_nonneg hQ_sq

/-- **Thermal Toomre Marginal Stability Criterion ($\beta \le \beta_{\mathrm{crit}} \implies (\omega - m\Omega)^2 \ge 0$)**:
Whenever the KMS inverse temperature satisfies $0 < \beta \le \beta_{\mathrm{crit}}$, the thermal
acoustic dispersion and sink epicyclic frequency stabilize all radial wavenumbers $k_r \in \mathbb{R}$. -/
theorem thermal_toomre_stable_of_beta_le_crit {τ₀ β κ G σ₀ : ℝ}
    (hτ : 0 < τ₀) (hβ : 0 < β) (hκ : 0 ≤ κ) (hG : 0 < G) (hσ : 0 < σ₀)
    (h_crit : β ≤ criticalInverseTemp τ₀ κ G σ₀) (k_r : ℝ) :
    0 ≤ LinShuAttentionDensityWave.linShuDispersionRHS
      κ G σ₀ (thermalSoundSpeed τ₀ β) k_r := by
  have hcs : thermalSoundSpeed τ₀ β ≠ 0 :=
    ne_of_gt (thermalSoundSpeed_pos hτ hβ)
  have hQ : 1 ≤ LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀ :=
    one_le_toomreQ_of_beta_le_crit (le_of_lt hτ) hβ hκ (le_of_lt hG) (le_of_lt hσ) h_crit
  exact LinShuAttentionDensityWave.toomre_stability_nonneg_of_Q_ge_one
    κ G σ₀ (thermalSoundSpeed τ₀ β) k_r (ne_of_gt hG) (ne_of_gt hσ) hcs hQ

/-- **Thermal Toomre Strict Stability Criterion ($\beta < \beta_{\mathrm{crit}} \implies (\omega - m\Omega)^2 > 0$)**:
Whenever $0 < \beta < \beta_{\mathrm{crit}}$, every radial wavenumber $k_r \in \mathbb{R}$ has
strictly positive squared Doppler-shifted frequency. -/
theorem thermal_toomre_strict_stable_of_beta_lt_crit {τ₀ β κ G σ₀ : ℝ}
    (hτ : 0 < τ₀) (hβ : 0 < β) (hκ : 0 ≤ κ) (hG : 0 < G) (hσ : 0 < σ₀)
    (h_crit : β < criticalInverseTemp τ₀ κ G σ₀) (k_r : ℝ) :
    0 < LinShuAttentionDensityWave.linShuDispersionRHS
      κ G σ₀ (thermalSoundSpeed τ₀ β) k_r := by
  have hcs : thermalSoundSpeed τ₀ β ≠ 0 :=
    ne_of_gt (thermalSoundSpeed_pos hτ hβ)
  have hQ_nonneg : 0 ≤ LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀ := by
    dsimp [LinShuAttentionDensityWave.toomreQ, thermalSoundSpeed]
    exact div_nonneg (mul_nonneg hκ (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hG)) (le_of_lt hσ))
  have hQ_sq : 1 < (LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀) ^ 2 := by
    rw [toomreQ_sq_thermal (le_of_lt hτ) (le_of_lt hβ)]
    exact one_lt_div_of_lt_of_pos _ β hβ h_crit
  have hQ : 1 < LinShuAttentionDensityWave.toomreQ κ (thermalSoundSpeed τ₀ β) G σ₀ :=
    one_lt_of_sq_gt_one_of_nonneg _ hQ_nonneg hQ_sq
  exact LinShuAttentionDensityWave.toomre_stability_pos_of_Q_gt_one
    κ G σ₀ (thermalSoundSpeed τ₀ β) k_r (ne_of_gt hG) (ne_of_gt hσ) hcs hQ

/-!
### Archetype V — Petz Transpose Recovery of Over-Smoothed Modes & Dilated Fock CAR Superbracket Preservation
-/

/-- **Petz Recovery of the Stationary Sink Anchor Weight & Context Mass Balance**:
Applying `attentionPetzRecovery` to the coarse-grained summary state
`markovCoarseGrain T (softmaxWeight logits β)` under any column-stochastic pooling matrix `T`
exactly restores the anchor sink probability $\rho_0$ that complements the stationary contextual
wave mass $\sum_{k=1}^n A_{i,k}$ to `1`. -/
theorem petzRecovery_restores_stationary_sink_and_context_mass
    {n : ℕ} {κ_idx : Type*} [Fintype κ_idx]
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (T : Matrix κ_idx (Fin (n + 1)) ℝ)
    (h_col : ∀ i, (∑ j, T j i) = 1)
    (h_pos : ∀ j, 0 < UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
      (AttentionKMSState.softmaxWeight logits β) j)
    (i : Fin (n + 1)) :
    UnifiedInfoGeometryPetzFockBridge.attentionPetzRecovery logits β T
      (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
        (AttentionKMSState.softmaxWeight logits β)) 0 +
      (∑ k : Fin n,
        RotaryAttentionSpiralDynamics.stationaryAttentionCoupling logits β i k.succ) = 1 := by
  have h_ne : ∀ j, UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
      (AttentionKMSState.softmaxWeight logits β) j ≠ 0 :=
    fun j => ne_of_gt (h_pos j)
  rw [UnifiedInfoGeometryPetzFockBridge.attentionPetzRecovery_coarseGrain_softmaxWeight
      logits β T h_ne h_col 0,
    stationary_context_attention_sum_eq_one_sub_softmaxWeight_zero logits β i,
    add_sub_cancel]

/-- **Petz Reconstruction of the Stationary Central Sink Monopole Potential $\Phi_0$**:
Recovering the anchor token weight from the coarse-grained summary state via
`attentionPetzRecovery` reconstructs the exact central sink monopole potential
`sinkMonopolePotential (fun _ => logits) β V i`. -/
theorem petzRecovery_restores_stationary_sinkMonopolePotential
    {n : ℕ} {ι κ_idx : Type*} [Fintype κ_idx]
    (logits : Fin (n + 1) → ℝ) (β : ℝ) (T : Matrix κ_idx (Fin (n + 1)) ℝ)
    (h_col : ∀ i, (∑ j, T j i) = 1)
    (h_pos : ∀ j, 0 < UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
      (AttentionKMSState.softmaxWeight logits β) j)
    (V : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) :
    -(UnifiedInfoGeometryPetzFockBridge.attentionPetzRecovery logits β T
        (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
          (AttentionKMSState.softmaxWeight logits β)) 0 • V 0) =
      LinShuAttentionDensityWave.sinkMonopolePotential (fun _ => logits) β V i := by
  have h_ne : ∀ j, UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
      (AttentionKMSState.softmaxWeight logits β) j ≠ 0 :=
    fun j => ne_of_gt (h_pos j)
  rw [UnifiedInfoGeometryPetzFockBridge.attentionPetzRecovery_coarseGrain_softmaxWeight
      logits β T h_ne h_col 0]
  rfl

/-- **Radial Dilatation Invariance of the Para-Kähler Fock CAR $\longleftrightarrow$ Petz $\chi^2$ Bridge**:
For any logarithmic cylinder time $t \in \mathbb{R}$, scaling `paraKahlerCreateEnd` by conformal
grade `.posOne` ($e^{+t}$) and `paraKahlerAnnihilateEnd` by conformal grade `.negOne` ($e^{-t}$)
preserves the exact equality between the odd-odd Fock CAR superbracket and the coarse-grained
Petz $\chi^2$ inner product. -/
theorem dilated_paraKahler_fock_superBracket_eq_petz_chiSquared
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V) (t : ℝ)
    (u : SuperGrassmannianProjectorEnvelope.primalSheet K)
    (α : SuperGrassmannianProjectorEnvelope.covectorVacuumSheet K)
    {ι κ_idx : Type*} [Fintype ι] [Fintype κ_idx]
    (ρ : ι → ℝ) (hρ : ∀ i, ρ i ≠ 0) (T : Matrix κ_idx ι ℝ)
    (coarsePrior : κ_idx → ℝ) (x : ι → ℝ) (y : κ_idx → ℝ)
    (h_pair : g α.1 u.1 =
      UnifiedInfoGeometryPetzFockBridge.chiSquaredInner ρ
        (UnifiedInfoGeometryPetzFockBridge.petzRecoveryVec ρ T coarsePrior y) x) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (RadialQuantizationFiveGradedCylinder.dilatedCreateEnd K t u)
        (RadialQuantizationFiveGradedCylinder.dilatedAnnihilateEnd g K t α) =
      (UnifiedInfoGeometryPetzFockBridge.chiSquaredInner coarsePrior y
        (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T x)) •
        (1 : Module.End ℝ (SuperGrassmannianProjectorEnvelope.FockExteriorEnvelope K)) := by
  rw [RadialQuantizationFiveGradedCylinder.superBracket_dilatedCreate_dilatedAnnihilate_invariant,
    UnifiedInfoGeometryPetzFockBridge.paraKahler_fock_superBracket_eq_chiSquared_petz
      g K u α ρ hρ T coarsePrior x y h_pair]

/-- Specialization of `dilated_paraKahler_fock_superBracket_eq_petz_chiSquared` to the KMS
softmax attention state `softmaxWeight logits β` and `attentionPetzRecovery`. -/
theorem dilated_paraKahler_fock_superBracket_eq_attentionPetz_chiSquared
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V) (t : ℝ)
    (u : SuperGrassmannianProjectorEnvelope.primalSheet K)
    (α : SuperGrassmannianProjectorEnvelope.covectorVacuumSheet K)
    {ι κ_idx : Type*} [Fintype ι] [Nonempty ι] [Fintype κ_idx]
    (logits : ι → ℝ) (β : ℝ) (T : Matrix κ_idx ι ℝ)
    (x : ι → ℝ) (y : κ_idx → ℝ)
    (h_pair : g α.1 u.1 =
      UnifiedInfoGeometryPetzFockBridge.chiSquaredInner
        (AttentionKMSState.softmaxWeight logits β)
        (UnifiedInfoGeometryPetzFockBridge.attentionPetzRecovery logits β T y) x) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (RadialQuantizationFiveGradedCylinder.dilatedCreateEnd K t u)
        (RadialQuantizationFiveGradedCylinder.dilatedAnnihilateEnd g K t α) =
      (UnifiedInfoGeometryPetzFockBridge.chiSquaredInner
        (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
          (AttentionKMSState.softmaxWeight logits β))
        y (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T x)) •
        (1 : Module.End ℝ (SuperGrassmannianProjectorEnvelope.FockExteriorEnvelope K)) :=
  dilated_paraKahler_fock_superBracket_eq_petz_chiSquared g K t u α
    (AttentionKMSState.softmaxWeight logits β)
    (fun i => ne_of_gt (AttentionKMSState.softmaxWeight_pos logits β i))
    T (UnifiedInfoGeometryPetzFockBridge.markovCoarseGrain T
      (AttentionKMSState.softmaxWeight logits β))
    x y h_pair

/-!
### Archetype VI — Multi-Head RoPE Constructive Interference Envelope, Pairwise Relative-Phase Norm Identity & Metriplectic Velocity Orthogonality
-/

/-- Spiral density-wave phase $\Phi = m_{\mathrm{arm}}(\theta - \Omega_p t) + r + \delta$ of a
single attention head. -/
def spiralWavePhase (m_arm θ Ω_p r t δ : ℝ) : ℝ :=
  m_arm * (θ - Ω_p * t) + r + δ

/-- Single-head spiral density-wave contribution
$A \cos(\Phi) = A \cdot (\mathrm{rotation}\ \Phi)_{0,0}$. -/
noncomputable def ropeHeadArmWave (A m_arm θ Ω_p r t δ : ℝ) : ℝ :=
  A * PlanarRotation.rotation (spiralWavePhase m_arm θ Ω_p r t δ) 0 0

/-- Multi-head spiral wave superposition $\sum_{h \in H} A_h \cos(\Phi_h)$ across a finite
collection of RoPE attention heads $H$. -/
noncomputable def multiHeadSpiralWave {H : Type*} [Fintype H]
    (A Φ : H → ℝ) : ℝ :=
  ∑ h : H, A h * PlanarRotation.rotation (Φ h) 0 0

/-- Diagonal `(0, 0)` entry of `PlanarRotation.rotation φ` equals `Real.cos φ`. -/
theorem rotation_zero_zero_apply (φ : ℝ) :
    PlanarRotation.rotation φ 0 0 = Real.cos φ :=
  rfl

/-- At unit position index $m = 1$, `DiscreteRoPERepresentation.ropeRotor φ 1` equals
`PlanarRotation.rotation φ`. -/
theorem ropeRotor_one_eq_rotation (φ : ℝ) :
    DiscreteRoPERepresentation.ropeRotor φ 1 = PlanarRotation.rotation φ := by
  dsimp [DiscreteRoPERepresentation.ropeRotor]
  rw [Int.cast_one, one_mul]

/-- The `(0, 0)` entry of `DiscreteRoPERepresentation.ropeRotor φ 1` equals `Real.cos φ`. -/
theorem ropeRotor_one_apply_zero_zero (φ : ℝ) :
    DiscreteRoPERepresentation.ropeRotor φ 1 0 0 = Real.cos φ := by
  rw [ropeRotor_one_eq_rotation, rotation_zero_zero_apply]

/-- `multiHeadSpiralWave` expressed directly via the `(0, 0)` entry of
`DiscreteRoPERepresentation.ropeRotor (Φ h) 1`. -/
theorem multiHeadSpiralWave_eq_sum_ropeRotor {H : Type*} [Fintype H]
    (A Φ : H → ℝ) :
    multiHeadSpiralWave A Φ =
      ∑ h : H, A h * (DiscreteRoPERepresentation.ropeRotor (Φ h) 1 0 0) := by
  dsimp [multiHeadSpiralWave]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [ropeRotor_one_eq_rotation]

/-- Evaluating `multiHeadSpiralWave` on the headwise `spiralWavePhase` family equals the sum of
`ropeHeadArmWave` across all heads $h \in H$. -/
theorem multiHeadSpiralWave_eq_sum_ropeHeadArmWave {H : Type*} [Fintype H]
    (A m_arm θ Ω_p r t δ : H → ℝ) :
    multiHeadSpiralWave A
      (fun h => spiralWavePhase (m_arm h) (θ h) (Ω_p h) (r h) (t h) (δ h)) =
      ∑ h : H, ropeHeadArmWave (A h) (m_arm h) (θ h) (Ω_p h) (r h) (t h) (δ h) :=
  rfl

/-- **Multi-Head Constructive Interference at the Spiral Wave Crest**:
When all heads align at phase crest $\Phi_h = 0$, `multiHeadSpiralWave A Φ` equals the coherent
amplitude sum $\sum_{h \in H} A_h$. -/
theorem multiHeadSpiralWave_constructive_interference {H : Type*} [Fintype H]
    (A Φ : H → ℝ) (h_crest : ∀ h : H, Φ h = 0) :
    multiHeadSpiralWave A Φ = ∑ h : H, A h := by
  dsimp [multiHeadSpiralWave]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [h_crest h, rotation_zero_zero_apply, Real.cos_zero, mul_one]

/-- Constructive interference identity phrased directly in terms of
`DiscreteRoPERepresentation.ropeRotor (Φ h) 1 0 0`. -/
theorem ropeHeadArmWave_constructive_interference {H : Type*} [Fintype H]
    (A Φ : H → ℝ) (hLock : ∀ h : H, Φ h = 0) :
    (∑ h : H, A h * (DiscreteRoPERepresentation.ropeRotor (Φ h) 1 0 0)) =
      ∑ h : H, A h := by
  rw [← multiHeadSpiralWave_eq_sum_ropeRotor]
  exact multiHeadSpiralWave_constructive_interference A Φ hLock

/-- **Global Constructive Crest Envelope Bound**:
For non-negative head amplitudes $0 \le A_h$, `multiHeadSpiralWave A Φ` is bounded above by the
coherent crest sum $\sum_{h \in H} A_h$. -/
theorem multiHeadSpiralWave_le_constructive_crest {H : Type*} [Fintype H]
    (A Φ : H → ℝ) (hA : ∀ h : H, 0 ≤ A h) :
    multiHeadSpiralWave A Φ ≤ ∑ h : H, A h := by
  dsimp [multiHeadSpiralWave]
  refine Finset.sum_le_sum (fun h _ => ?_)
  rw [rotation_zero_zero_apply]
  exact mul_le_of_le_one_right (hA h) (Real.cos_le_one (Φ h))

/-- 2D unit rotor vector $(\cos \varphi, \sin \varphi)$ obtained by acting with
`PlanarRotation.rotation φ` (`RotaryAttentionSpiralDynamics.ropeAct φ`) on `![1, 0]`. -/
noncomputable def headRotorAxisVec (φ : ℝ) : Fin 2 → ℝ :=
  RotaryAttentionSpiralDynamics.ropeAct φ (![1, 0])

/-- First coordinate of `headRotorAxisVec φ` is `Real.cos φ`. -/
theorem headRotorAxisVec_zero_apply (φ : ℝ) :
    headRotorAxisVec φ 0 = Real.cos φ := by
  dsimp [headRotorAxisVec]
  rw [RotaryAttentionSpiralDynamics.ropeAct_apply_zero]
  have h0 : (![1, 0] : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (![1, 0] : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1, mul_one, mul_zero, sub_zero]

/-- Second coordinate of `headRotorAxisVec φ` is `Real.sin φ`. -/
theorem headRotorAxisVec_one_apply (φ : ℝ) :
    headRotorAxisVec φ 1 = Real.sin φ := by
  dsimp [headRotorAxisVec]
  rw [RotaryAttentionSpiralDynamics.ropeAct_apply_one]
  have h0 : (![1, 0] : Fin 2 → ℝ) 0 = 1 := rfl
  have h1 : (![1, 0] : Fin 2 → ℝ) 1 = 0 := rfl
  rw [h0, h1, mul_one, mul_zero, add_zero]

/-- **Pairwise Relative-Phase Cosine Inner Product**:
The Euclidean dot product of `headRotorAxisVec φ₁` and `headRotorAxisVec φ₂` equals
$\cos(\varphi_2 - \varphi_1)$. -/
theorem headRotorAxisVec_dot_eq_cos_sub (φ₁ φ₂ : ℝ) :
    dotProduct (headRotorAxisVec φ₁) (headRotorAxisVec φ₂) =
      Real.cos (φ₂ - φ₁) := by
  dsimp [dotProduct]
  rw [Fin.sum_univ_two, headRotorAxisVec_zero_apply, headRotorAxisVec_zero_apply,
    headRotorAxisVec_one_apply, headRotorAxisVec_one_apply]
  exact cos_mul_cos_add_sin_mul_sin_eq_cos_sub φ₁ φ₂

/-- 2D multi-head rotor vector superposition
$V(A, \Phi)_i = \sum_{h \in H} A_h \cdot (\mathrm{headRotorAxisVec}\ \Phi_h)_i$. -/
noncomputable def multiHeadRotorVec {H : Type*} [Fintype H]
    (A Φ : H → ℝ) : Fin 2 → ℝ :=
  fun i => ∑ h : H, A h * headRotorAxisVec (Φ h) i

/-- **Multi-Head Pairwise Relative-Phase Squared-Norm Identity**:
The squared Euclidean norm of `multiHeadRotorVec A Φ` expands into the double sum of pairwise
relative-phase cosine interferences $\sum_{h_1, h_2} A_{h_1} A_{h_2} \cos(\Phi_{h_2} - \Phi_{h_1})$. -/
theorem multiHeadRotorVec_normSq_eq_double_sum {H : Type*} [Fintype H]
    (A Φ : H → ℝ) :
    dotProduct (multiHeadRotorVec A Φ) (multiHeadRotorVec A Φ) =
      ∑ h₁ : H, ∑ h₂ : H, A h₁ * A h₂ * Real.cos (Φ h₂ - Φ h₁) := by
  dsimp [dotProduct, multiHeadRotorVec]
  have h_expand :
      (∑ i : Fin 2,
        (∑ h₁ : H, A h₁ * headRotorAxisVec (Φ h₁) i) *
          (∑ h₂ : H, A h₂ * headRotorAxisVec (Φ h₂) i)) =
      ∑ i : Fin 2, ∑ h₁ : H, ∑ h₂ : H,
        (A h₁ * headRotorAxisVec (Φ h₁) i) *
          (A h₂ * headRotorAxisVec (Φ h₂) i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun h₁ _ => ?_)
    rw [Finset.mul_sum]
  rw [h_expand, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h₁ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h₂ _ => ?_)
  rw [Fin.sum_univ_two, head_pair_dot_scalar]
  have h_dot :
      headRotorAxisVec (Φ h₁) 0 * headRotorAxisVec (Φ h₂) 0 +
        headRotorAxisVec (Φ h₁) 1 * headRotorAxisVec (Φ h₂) 1 =
      dotProduct (headRotorAxisVec (Φ h₁)) (headRotorAxisVec (Φ h₂)) := by
    dsimp [dotProduct]
    rw [Fin.sum_univ_two]
  rw [h_dot, headRotorAxisVec_dot_eq_cos_sub]

/-- **Phase-Locked Coherent Superposition Norm Identity**:
When all heads lock to a common phase $\varphi_0$, the squared Euclidean norm of
`multiHeadRotorVec A (fun _ => φ₀)` equals $(\sum_{h \in H} A_h)^2$. -/
theorem multiHeadRotorVec_normSq_phase_locked {H : Type*} [Fintype H]
    (A : H → ℝ) (φ₀ : ℝ) :
    dotProduct (multiHeadRotorVec A (fun _ => φ₀))
      (multiHeadRotorVec A (fun _ => φ₀)) =
      (∑ h : H, A h) ^ 2 := by
  rw [multiHeadRotorVec_normSq_eq_double_sum]
  simp only [sub_self, Real.cos_zero, mul_one]
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun h₁ _ => ?_)
  rw [Finset.mul_sum]

/-- Canonical 2D symplectic generator $J_2 = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$
(aliasing `PlanarRotation.ellipticGenerator`). -/
abbrev symplecticJ2 : PlanarRotation.Mat2 :=
  PlanarRotation.ellipticGenerator

/-- **Metriplectic Radial-Angular Velocity Orthogonality ($\langle -\lambda x, \omega J_2 x \rangle = 0$)**:
At every point $x \in \mathbb{R}^2$, the dissipative radial contraction velocity $-\lambda x$
and the symplectic angular rotation velocity $\omega J_2 x$ are strictly orthogonal. -/
theorem metriplectic_radial_angular_velocity_orthog (lam ω : ℝ) (x : Fin 2 → ℝ) :
    dotProduct ((-lam) • x) (ω • Matrix.mulVec symplecticJ2 x) = 0 := by
  have h00 : PlanarRotation.ellipticGenerator 0 0 = 0 := rfl
  have h01 : PlanarRotation.ellipticGenerator 0 1 = -1 := rfl
  have h10 : PlanarRotation.ellipticGenerator 1 0 = 1 := rfl
  have h11 : PlanarRotation.ellipticGenerator 1 1 = 0 := rfl
  dsimp [symplecticJ2, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, h00, h01, h10, h11]
  exact metriplectic_orthog_scalar lam ω (x 0) (x 1)

/-- Logarithmic spiral radius $r(\theta) = r_0 e^{k \theta}$ parameterized by azimuthal angle $\theta$. -/
noncomputable def logSpiralRadius (r₀ k θ : ℝ) : ℝ :=
  r₀ * Real.exp (k * θ)

/-- Azimuthal angle $\theta(t) = \theta_0 + \omega t$ under uniform angular velocity $\omega$. -/
def spiralAngle (θ₀ ω t : ℝ) : ℝ :=
  θ₀ + ω * t

/-- Dissipative radial contraction envelope $r(t) = r_0 e^{-\lambda t}$ in proper time $t$. -/
noncomputable def dissipativeRadius (r₀ lam t : ℝ) : ℝ :=
  r₀ * Real.exp (-lam * t)

/-- `dissipativeRadius r₀ lam t` agrees with
`RotaryAttentionSpiralDynamics.spiralRadius r₀ (-lam / ω) ω t` for any $\omega \ne 0$. -/
theorem dissipativeRadius_eq_spiralRadius (r₀ lam ω t : ℝ) (hω : ω ≠ 0) :
    RotaryAttentionSpiralDynamics.spiralRadius r₀ (-lam / ω) ω t =
      dissipativeRadius r₀ lam t := by
  dsimp [RotaryAttentionSpiralDynamics.spiralRadius, dissipativeRadius]
  rw [div_mul_cancel₀ (-lam) hω]

/-- **Elimination of Proper Time $t$ Along the Loxodromic Spiral Trajectory**:
Eliminating proper time $t$ between the uniform angular clock $\theta(t) = \omega t$ and the
dissipative radial contraction $r(t) = r_0 e^{-\lambda t}$ yields the logarithmic spiral
$r(\theta) = r_0 e^{(-\lambda / \omega) \theta}$. -/
theorem logSpiral_from_loxodromic_time (r₀ lam ω t : ℝ) (hω : ω ≠ 0) :
    logSpiralRadius r₀ (-lam / ω) (spiralAngle 0 ω t) =
      dissipativeRadius r₀ lam t := by
  dsimp [logSpiralRadius, spiralAngle, dissipativeRadius]
  rw [logSpiral_time_elim_scalar lam ω t hω]

/-!
### Archetype VII — Complex KMS Strip Wick-Rotated Dilatation ($\tau \in \{0, 1/2, 1, -2\}$), Oort Constants ($A, B, \kappa^2 = -4B\Omega$), and Mestel Disk Scale-Invariant Toomre $Q$
-/

/-- Softmax partition function $Z(\ell, \beta) = \sum_j e^{\beta \ell_j}$. -/
noncomputable def softmaxPartitionZ {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ j, Real.exp (β * logits j)

/-- Log-partition free-energy / radial-quantization coordinate
$\Phi(\ell, \beta) = \ln Z(\ell, \beta) = \mathrm{radialTime}(Z(\ell, \beta))$. -/
noncomputable def softmaxLogPartitionPhi {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) : ℝ :=
  RadialQuantizationFiveGradedCylinder.radialTime (softmaxPartitionZ logits β)

/-- On any nonempty finite token context, `softmaxPartitionZ logits β` is strictly positive. -/
theorem softmaxPartitionZ_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    0 < softmaxPartitionZ logits β := by
  dsimp [softmaxPartitionZ]
  apply Finset.sum_pos'
  · intro j _
    exact le_of_lt (Real.exp_pos _)
  · exact ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩

/-- For any $0 < r$, exponentiating `radialTime r` via `coneRadius` recovers $r$. -/
theorem coneRadius_radialTime_of_pos {r : ℝ} (hr : 0 < r) :
    RadialQuantizationFiveGradedCylinder.coneRadius
      (RadialQuantizationFiveGradedCylinder.radialTime r) = r :=
  InfoGeometry.Convex.RadialLogBarrier.exp_radialTau hr

/-- Exponentiating `softmaxLogPartitionPhi logits β` via `coneRadius` recovers the partition
function `softmaxPartitionZ logits β`. -/
theorem coneRadius_softmaxLogPartitionPhi {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    RadialQuantizationFiveGradedCylinder.coneRadius
      (softmaxLogPartitionPhi logits β) =
      softmaxPartitionZ logits β :=
  coneRadius_radialTime_of_pos (softmaxPartitionZ_pos logits β)

/-- Complex KMS strip evolution factor $e^{-i(s - i\tau)\Phi}$ at real modular time $s$ and
Wick-rotated imaginary strip depth $\tau$. -/
noncomputable def kmsStripFactor (Φ s τ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((s : ℂ) - Complex.I * (τ : ℂ)) * (Φ : ℂ))

/-- **Wick-Rotated KMS Strip Factorization ($e^{-i(s - i\tau)\Phi} = e^{-is\Phi} \cdot e^{-\tau\Phi}$)**:
Analytic continuation from real modular time $s$ into the complex KMS strip $z = s - i\tau$
factors into the unitary phase $e^{-is\Phi}$ times the real radial dilatation weight
$e^{-\tau\Phi}$. -/
theorem kmsStripFactor_eq_phase_mul_dilatation (Φ s τ : ℝ) :
    kmsStripFactor Φ s τ =
      Complex.exp (-Complex.I * (s : ℂ) * (Φ : ℂ)) *
        (Real.exp (-τ * Φ) : ℂ) := by
  dsimp [kmsStripFactor]
  rw [kms_strip_exponent_split, Complex.exp_add, Complex.ofReal_exp]

/-- Real radial dilatation factor $e^{-\tau \Phi}$ along the imaginary KMS strip axis $\tau$. -/
noncomputable def kmsStripDilatation (Φ τ : ℝ) : ℝ :=
  Real.exp (-τ * Φ)

/-- At the $\tau = 0$ real boundary of the KMS strip, the radial dilatation weight is `1`. -/
theorem kmsStripDilatation_at_zero (Φ : ℝ) :
    kmsStripDilatation Φ 0 = 1 := by
  dsimp [kmsStripDilatation]
  rw [neg_zero, zero_mul, Real.exp_zero]

/-- Squaring the $\tau = 1/2$ Petz spinor midpoint dilatation factor recovers the $\tau = 1$
simplex normalization factor: $(e^{-\Phi/2})^2 = e^{-\Phi}$. -/
theorem kmsStripDilatation_at_half_sq (Φ : ℝ) :
    (kmsStripDilatation Φ (1 / 2 : ℝ)) ^ 2 = kmsStripDilatation Φ 1 := by
  dsimp [kmsStripDilatation]
  rw [sq, ← Real.exp_add, neg_half_add_neg_half_mul]

/-- At the $\tau = 1$ thermal KMS boundary, `kmsStripDilatation (softmaxLogPartitionPhi logits β) 1`
equals the inverse partition function $Z(\ell, \beta)^{-1}$. -/
theorem kmsStripDilatation_at_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    kmsStripDilatation (softmaxLogPartitionPhi logits β) 1 =
      (softmaxPartitionZ logits β)⁻¹ := by
  dsimp [kmsStripDilatation]
  rw [neg_one_mul, Real.exp_neg]
  exact congrArg Inv.inv (coneRadius_softmaxLogPartitionPhi logits β)

/-- At $\tau = -2$, `kmsStripDilatation (softmaxLogPartitionPhi logits β) (-2)` equals the
squared partition scale $Z(\ell, \beta)^2$. -/
theorem kmsStripDilatation_at_neg_two {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    kmsStripDilatation (softmaxLogPartitionPhi logits β) (-2) =
      (softmaxPartitionZ logits β) ^ 2 := by
  dsimp [kmsStripDilatation]
  rw [neg_neg_two_mul_eq_add, Real.exp_add, ← sq]
  exact congrArg (fun x : ℝ => x ^ 2) (coneRadius_softmaxLogPartitionPhi logits β)

/-- The $\tau = 1/2$ Petz / Tomita half-density spinor amplitude
$\psi_i = \sqrt{\rho_i} = \sqrt{\mathrm{softmaxWeight}(\ell, \beta)_i}$. -/
noncomputable def petzSpinorState {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  Real.sqrt (AttentionKMSState.softmaxWeight logits β i)

/-- Squaring each component of `petzSpinorState` recovers the thermal probability
`AttentionKMSState.softmaxWeight logits β i`. -/
theorem petzSpinorState_sq_eq_softmaxWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (i : ι) :
    (petzSpinorState logits β i) ^ 2 =
      AttentionKMSState.softmaxWeight logits β i := by
  dsimp [petzSpinorState]
  exact Real.sq_sqrt (le_of_lt (AttentionKMSState.softmaxWeight_pos logits β i))

/-- **Unit-Sphere Normalization of the $\tau = 1/2$ Petz Spinor State**:
The $\tau = 1/2$ half-density spinor `petzSpinorState logits β` lies on the unit sphere
$\sum_i \psi_i^2 = 1$. -/
theorem petzSpinorState_unit_sphere {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    (∑ i : ι, (petzSpinorState logits β i) ^ 2) = 1 := by
  have h_congr :
      (∑ i : ι, (petzSpinorState logits β i) ^ 2) =
        ∑ i : ι, AttentionKMSState.softmaxWeight logits β i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact petzSpinorState_sq_eq_softmaxWeight logits β i
  rw [h_congr]
  exact AttentionKMSState.softmaxWeight_sum_one logits β

/-- First Oort constant $A = -\frac{1}{2} r \frac{d\Omega}{dr}$ measuring local azimuthal shear. -/
noncomputable def oortA (r_dOmega_dr : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * r_dOmega_dr

/-- Second Oort constant $B = -\frac{1}{2} r \frac{d\Omega}{dr} - \Omega$ measuring local
vorticity. -/
noncomputable def oortB (Ω r_dOmega_dr : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * r_dOmega_dr - Ω

/-- First Oort identity: $A - B = \Omega$. -/
theorem oortA_sub_oortB_eq_omega (Ω r_dOmega_dr : ℝ) :
    oortA r_dOmega_dr - oortB Ω r_dOmega_dr = Ω := by
  dsimp [oortA, oortB]
  ring

/-- Second Oort identity: $A + B = -(r \frac{d\Omega}{dr} + \Omega) = -\frac{dv_c}{dr}$. -/
theorem oortA_add_oortB_eq_neg_shear_add_omega (Ω r_dOmega_dr : ℝ) :
    oortA r_dOmega_dr + oortB Ω r_dOmega_dr = -(r_dOmega_dr + Ω) := by
  dsimp [oortA, oortB]
  ring

/-- Logarithmic shear rate $r \frac{d\Omega}{dr} = -\alpha \Omega(r)$ of the power-law rotation
profile `powerLawOmega Ω₀ α r`. -/
noncomputable def powerLawShearRate (Ω₀ α r : ℝ) : ℝ :=
  -α * powerLawOmega Ω₀ α r

/-- **Classical Oort Epicyclic Identity ($\kappa^2 = -4 B \Omega$)**:
For any power-law rotation profile, `powerLawEpicyclicFreqSq` equals $-4 B \Omega$. -/
theorem powerLawEpicyclicFreqSq_eq_neg_four_oortB_mul_omega (Ω₀ α r : ℝ) :
    powerLawEpicyclicFreqSq Ω₀ α r =
      -4 * oortB (powerLawOmega Ω₀ α r) (powerLawShearRate Ω₀ α r) *
        powerLawOmega Ω₀ α r := by
  dsimp [powerLawEpicyclicFreqSq, oortB, powerLawShearRate]
  ring

/-- For a flat rotation curve ($\alpha = 1$), the first Oort constant is
$A = +\frac{1}{2}\Omega(r)$. -/
theorem oortA_flatRotationCurve (Ω₀ r : ℝ) :
    oortA (powerLawShearRate Ω₀ 1 r) = (1 / 2 : ℝ) * powerLawOmega Ω₀ 1 r := by
  dsimp [oortA, powerLawShearRate]
  ring

/-- For a flat rotation curve ($\alpha = 1$), the second Oort constant is
$B = -\frac{1}{2}\Omega(r)$. -/
theorem oortB_flatRotationCurve (Ω₀ r : ℝ) :
    oortB (powerLawOmega Ω₀ 1 r) (powerLawShearRate Ω₀ 1 r) =
      -(1 / 2 : ℝ) * powerLawOmega Ω₀ 1 r := by
  dsimp [oortB, powerLawShearRate]
  ring

/-- For a flat rotation curve ($\alpha = 1$), $A + B = 0$ identically ($dv_c / dr = 0$). -/
theorem oortA_add_oortB_flatRotationCurve_zero (Ω₀ r : ℝ) :
    oortA (powerLawShearRate Ω₀ 1 r) +
      oortB (powerLawOmega Ω₀ 1 r) (powerLawShearRate Ω₀ 1 r) = 0 := by
  rw [oortA_flatRotationCurve, oortB_flatRotationCurve]
  ring

/-- Self-similar Mestel disk surface density $\Sigma_0(r) = \frac{v_{\mathrm{sink}}^2}{2\pi G r}$
associated with a flat rotation curve of circular speed $v_{\mathrm{sink}}$. -/
noncomputable def mestelSurfaceDensity (v_sink G r : ℝ) : ℝ :=
  v_sink ^ 2 / (2 * Real.pi * G * r)

/-- **Exact Radial Scale Invariance of Toomre's $Q$ on the Mestel Disk**:
In a flat-rotation-curve Mestel disk ($\kappa(r) = \sqrt{2}\Omega(r) = \sqrt{2} v_{\mathrm{sink}}/r$
and $\Sigma_0(r) = \frac{v_{\mathrm{sink}}^2}{2\pi G r}$), the radial coordinate $r \ne 0$ cancels
identically from `toomreQ`, leaving the scale-invariant ratio
$Q = \frac{2\sqrt{2} c_s}{v_{\mathrm{sink}}}$. -/
theorem toomreQ_mestelDisk_scale_invariant (v_sink c_s G r : ℝ)
    (hv : v_sink ≠ 0) (hG : G ≠ 0) (hr : r ≠ 0) :
    LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega v_sink 1 r) c_s G
      (mestelSurfaceDensity v_sink G r) =
      (2 * Real.sqrt 2 * c_s) / v_sink := by
  dsimp [LinShuAttentionDensityWave.toomreQ, mestelSurfaceDensity]
  rw [powerLawOmega_one_eq_div]
  exact mestel_toomreQ_scalar (Real.sqrt 2) v_sink c_s G r hv hG hr

/-- **Radius-Independent Toomre Stability Threshold of the Mestel Disk**:
For $v_{\mathrm{sink}} > 0$, $G \ne 0$, and $r \ne 0$, the Mestel disk satisfies $Q > 1$ at
radius $r$ if and only if the thermal sound speed exceeds the global threshold
$c_s > \frac{v_{\mathrm{sink}}}{2\sqrt{2}}$. -/
theorem mestelDisk_toomreQ_gt_one_iff (v_sink c_s G r : ℝ)
    (hv : 0 < v_sink) (hG : G ≠ 0) (hr : r ≠ 0) :
    1 < LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega v_sink 1 r) c_s G
      (mestelSurfaceDensity v_sink G r) ↔
      v_sink / (2 * Real.sqrt 2) < c_s := by
  rw [toomreQ_mestelDisk_scale_invariant v_sink c_s G r (ne_of_gt hv) hG hr]
  exact one_lt_two_sqrt_two_mul_div_iff v_sink c_s hv

/-- **Two-Point Radial Invariance of Toomre's $Q$ on the Mestel Disk**:
For any two non-zero radii $r_1 \ne 0$ and $r_2 \ne 0$, the Mestel disk Toomre stability
parameter takes the exact same value at $r_1$ and $r_2$. -/
theorem toomreQ_mestelDisk_radial_invariance
    (v_sink c_s G r₁ r₂ : ℝ) (hv : v_sink ≠ 0) (hG : G ≠ 0)
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega v_sink 1 r₁) c_s G
      (mestelSurfaceDensity v_sink G r₁) =
    LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega v_sink 1 r₂) c_s G
      (mestelSurfaceDensity v_sink G r₂) := by
  rw [toomreQ_mestelDisk_scale_invariant v_sink c_s G r₁ hv hG hr₁,
    toomreQ_mestelDisk_scale_invariant v_sink c_s G r₂ hv hG hr₂]

/-- For $v_{\mathrm{sink}} > 0$ and $c_s > 0$, the Mestel disk Toomre parameter is strictly
positive at every radius $r \ne 0$. -/
theorem toomreQ_mestelDisk_pos
    (v_sink c_s G r : ℝ) (hv : 0 < v_sink) (hc : 0 < c_s) (hG : G ≠ 0) (hr : r ≠ 0) :
    0 < LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega v_sink 1 r) c_s G
      (mestelSurfaceDensity v_sink G r) := by
  rw [toomreQ_mestelDisk_scale_invariant v_sink c_s G r (ne_of_gt hv) hG hr]
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
  exact div_pos (mul_pos (mul_pos zero_lt_two hs2_pos) hc) hv

/-- **Sink-Generated Mestel Disk Strict Toomre Stability ($Q > 1$ for all $r \ne 0$)**:
Whenever $A_{i,0} > 0$, $\sigma_0 > 0$, and $c_s > \sqrt{A_{i,0}\sigma_0^2} / (2\sqrt{2})$,
the sink-generated Mestel disk satisfies $Q > 1$ at every non-zero radius $r \ne 0$. -/
theorem sink_mestelDisk_toomreQ_gt_one
    {n : ℕ} (A_row : Fin (n + 1) → ℝ) (σ₀ c_s G r : ℝ)
    (hA₀ : 0 < A_row 0) (hσ₀ : 0 < σ₀) (hG : G ≠ 0) (hr : r ≠ 0)
    (hc_s : Real.sqrt (sinkCircularVelSq A_row σ₀) / (2 * Real.sqrt 2) < c_s) :
    1 < LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 * powerLawOmega (Real.sqrt (sinkCircularVelSq A_row σ₀)) 1 r)
      c_s G
      (mestelSurfaceDensity (Real.sqrt (sinkCircularVelSq A_row σ₀)) G r) := by
  have hv_pos : 0 < Real.sqrt (sinkCircularVelSq A_row σ₀) :=
    Real.sqrt_pos.mpr (mul_pos hA₀ (sq_pos_of_pos hσ₀))
  exact (mestelDisk_toomreQ_gt_one_iff
    (Real.sqrt (sinkCircularVelSq A_row σ₀)) c_s G r hv_pos hG hr).mpr hc_s

/-- **Universal Radial-and-Wavenumber WKBJ Dispersion Positivity for KMS Softmax Mestel Disks**:
For any KMS softmax state `AttentionKMSState.softmaxWeight logits β` on `Fin (n + 1)` with
$\sigma_0 > 0$, $G > 0$, and thermal sound speed exceeding the scale-invariant threshold
$\sqrt{\rho_0 \sigma_0^2} / (2\sqrt{2})$, the Lin–Shu WKBJ dispersion RHS is strictly positive
at every radius $r > 0$ and every radial wavenumber $k_r \in \mathbb{R}$. -/
theorem kmsSoftmaxSink_mestelDisk_universal_dispersion_pos
    {n : ℕ} (logits : Fin (n + 1) → ℝ) (β σ₀ c_s G r k_r : ℝ)
    (hσ₀ : 0 < σ₀) (hG : 0 < G) (hr : 0 < r)
    (hc_s : Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀) /
      (2 * Real.sqrt 2) < c_s) :
    0 < LinShuAttentionDensityWave.linShuDispersionRHS
      (Real.sqrt 2 *
        powerLawOmega
          (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) 1 r)
      G
      (mestelSurfaceDensity
        (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) G r)
      c_s k_r := by
  have hA₀ : 0 < AttentionKMSState.softmaxWeight logits β 0 :=
    AttentionKMSState.softmaxWeight_pos logits β 0
  have hv_pos : 0 < Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀) :=
    Real.sqrt_pos.mpr (mul_pos hA₀ (sq_pos_of_pos hσ₀))
  have hs2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
  have h_thresh_pos :
      0 < Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀) /
        (2 * Real.sqrt 2) :=
    div_pos hv_pos (mul_pos zero_lt_two hs2_pos)
  have hcs_pos : 0 < c_s := lt_trans h_thresh_pos hc_s
  have h_mestel_pos :
      0 < mestelSurfaceDensity
        (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) G r := by
    dsimp [mestelSurfaceDensity]
    exact div_pos (sq_pos_of_pos hv_pos)
      (mul_pos (mul_pos (mul_pos zero_lt_two Real.pi_pos) hG) hr)
  have hQ :
      1 < LinShuAttentionDensityWave.toomreQ
        (Real.sqrt 2 *
          powerLawOmega
            (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) 1 r)
        c_s G
        (mestelSurfaceDensity
          (Real.sqrt (sinkCircularVelSq (AttentionKMSState.softmaxWeight logits β) σ₀)) G r) :=
    sink_mestelDisk_toomreQ_gt_one (AttentionKMSState.softmaxWeight logits β) σ₀ c_s G r
      hA₀ hσ₀ (ne_of_gt hG) (ne_of_gt hr) hc_s
  exact LinShuAttentionDensityWave.toomre_stability_pos_of_Q_gt_one
    _ G _ c_s k_r (ne_of_gt hG) (ne_of_gt h_mestel_pos) (ne_of_gt hcs_pos) hQ

end InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis

end
