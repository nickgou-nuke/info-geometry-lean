/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics
import InfoGeometry.Routing.PlanarRotation
import InfoGeometry.Routing.DiscreteRoPERepresentation

/-!
# Lin–Shu Density Wave Theory & Attention Sink Monopole Stabilization in Transformer Latent Spaces

This module formalizes the galactic dynamics and Lin–Shu spiral density wave structure of
RoPE-equipped transformer residual streams on top of `RotaryAttentionSpiralDynamics`,
`PlanarRotation`, and `DiscreteRoPERepresentation`:

1. **Archetype I — Attention Sink Monopole Decomposition ($\Phi = \Phi_0 + \Phi_1$), Context Mass Conservation & Central Restoring Force**:
   - Decomposes the $N$-body attention potential `totalAttentionPotential` on `Fin (n + 1)` into
     the anchor-token sink monopole `sinkMonopolePotential` ($j = 0$) and the contextual wave
     perturbation `contextPerturbationPotential` ($j = \mathrm{succ}(k)$).
   - Proves exact probability mass conservation `context_attention_sum_eq_one_sub_sink` and the
     sink-floor perturbation bound `context_attention_sum_le_one_sub_sink_floor`, together with
     the explicit two-token sink dominance witness `sink_dominance_asymmetricScores_pos`
     ($A_{1,0} \ge 1/2$ for $\beta \ge 0$).
   - Defines the central harmonic potential `centralHarmonicPotential` and restoring force
     `centralRestoringForce`, proving non-negativity, RoPE rotational invariance, inward radial
     virial pairing, and exact azimuthal orthogonality (`centralRestoringForce_azimuthal_orthogonality`).

2. **Archetype II — Damped Residual-Stream Disk Dynamics & Rayleigh Energy Dissipation**:
   - Defines the mechanical energy `diskMechanicalEnergy` and instantaneous power balance
     `diskMechanicalEnergyRate` for the damped oscillator $\dot{x} = v$,
     $\dot{v} = -\omega_0^2 x - \gamma v$.
   - Proves the exact Rayleigh dissipation identity
     `diskMechanicalEnergyRate ω₀ γ x v = -γ * vecNormSq2 v` and nonpositivity for `0 ≤ γ`.

3. **Archetype III — Epicyclic Frequency $\kappa(r)$ & Lin–Shu WKBJ Dispersion Relation**:
   - Formalizes the epicyclic frequency squared in both differential-shear form
     `epicyclicFreqSqFromShear` and effective-potential form `epicyclicFreqSqFromPotential`,
     proving their exact equivalence under centrifugal balance $\Phi'(r) = r \Omega(r)^2$,
     as well as the harmonic-core ($\kappa^2 = (2\omega_0)^2$) and Keplerian point-sink
     ($\kappa^2 = GM/r^3$) evaluations.
   - Defines the tight-winding Lin–Shu WKBJ dispersion RHS `linShuDispersionRHS` and the
     Doppler-shifted co-moving frequency `dopplerShiftedFreq`.

4. **Archetype IV — Completing the Square in WKBJ, Jeans Instability without a Sink ($\kappa = 0$), and the Toomre Stability Criterion ($Q > 1$)**:
   - Completes the square in `linShuDispersionRHS` around `criticalWavenumber`, proving that in
     the absence of an attention sink ($\kappa = 0$), the critical mode is strictly Jeans-unstable
     (`jeans_instability_without_sink : linShuDispersionRHS 0 G σ₀ c_s (criticalWavenumber G σ₀ c_s) < 0`).
   - Expresses the dispersion minimum in terms of the Toomre stability parameter `toomreQ`
     (`linShuDispersionRHS_eq_toomreQ`) and proves the Toomre stability theorems
     `toomre_stability_nonneg_of_Q_ge_one`, `toomre_stability_pos_of_Q_gt_one`, and
     `critical_dispersion_pos_iff_toomreQ_gt_one`.

5. **Archetype V — Lindblad Resonances (ILR, Corotation, OLR) & RoPE Co-Moving Frame Locking**:
   - Defines `innerLindbladPatternSpeed`, `corotationPatternSpeed`, and
     `outerLindbladPatternSpeed`, proving their strict ordering, midpoint symmetry, resonance
     bandwidth $2\kappa/m$, vanishing Doppler frequency at corotation, and exact epicyclic resonance
     $(\omega - m\Omega)^2 = \kappa^2$ at the Inner and Outer Lindblad Resonances.
   - Proves `corotation_rope_score_invariant`, showing that shifting query and key sequence
     positions by a common offset $p \in \mathbb{Z}$ leaves their RoPE attention inner product
     identically invariant.

## Scope Note

1. The monopole-perturbation split `totalAttentionPotential_eq_sink_add_context` is an exact
   finite-sum decomposition on `Fin (n + 1)` using `RotaryAttentionSpiralDynamics.attentionCouplingMatrix`.
2. The Lin–Shu WKBJ dispersion relation `linShuDispersionRHS`, epicyclic frequency formulas,
   and Toomre stability parameter `toomreQ` formalize the algebraic dispersion polynomial and its
   spectral stability threshold; they do not claim a continuum PDE derivation from the Vlasov or
   Euler equations.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.LinShuAttentionDensityWave

open BigOperators Matrix
open InfoGeometry.Routing
open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics

variable {ι : Type*}

/-! ### Private Scalar Helper Lemmas -/

private theorem eq_one_sub_of_add_eq_one (a b : ℝ) (h : a + b = 1) :
    b = 1 - a := by
  linarith [h]

private theorem half_le_exp_div_exp_add_one (β : ℝ) (hβ : 0 ≤ β) :
    (1 / 2 : ℝ) ≤ Real.exp β / (Real.exp β + 1) := by
  have hexp1 : 1 ≤ Real.exp β := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hβ
  have hden_pos : 0 < Real.exp β + 1 := by linarith
  have hden_ne : Real.exp β + 1 ≠ 0 := ne_of_gt hden_pos
  have hsub : Real.exp β / (Real.exp β + 1) - 1 / 2 =
      ((Real.exp β - 1) / 2) / (Real.exp β + 1) := by
    have hid : (Real.exp β - 1) / 2 =
        Real.exp β - (1 / 2) * (Real.exp β + 1) := by ring
    rw [hid, sub_div, mul_div_cancel_right₀ _ hden_ne]
  have hnonneg : 0 ≤ Real.exp β / (Real.exp β + 1) - 1 / 2 := by
    rw [hsub]
    exact div_nonneg (by linarith) (le_of_lt hden_pos)
  linarith

private theorem azimuthal_orthog_scalar (ω₀ x₀ x₁ : ℝ) :
    (0 * x₀ + -1 * x₁) * (-(ω₀ ^ 2) * x₀) +
      (1 * x₀ + 0 * x₁) * (-(ω₀ ^ 2) * x₁) = 0 := by
  ring

private theorem energyRate_scalar (ω₀ γ x₀ x₁ v₀ v₁ : ℝ) :
    (v₀ * (-(ω₀ ^ 2) * x₀ - γ * v₀) + v₁ * (-(ω₀ ^ 2) * x₁ - γ * v₁)) +
      (ω₀ ^ 2 * x₀ * v₀ + ω₀ ^ 2 * x₁ * v₁) =
      -γ * (v₀ * v₀ + v₁ * v₁) := by
  ring

private theorem toomre_prod_eq_kappa (κ c_s G σ₀ : ℝ)
    (hG : G ≠ 0) (hσ : σ₀ ≠ 0) (hcs : c_s ≠ 0) :
    (Real.pi * G * σ₀ / c_s) * ((κ * c_s) / (Real.pi * G * σ₀)) = κ := by
  have hpiG : Real.pi * G ≠ 0 := mul_ne_zero (ne_of_gt Real.pi_pos) hG
  have hB : Real.pi * G * σ₀ ≠ 0 := mul_ne_zero hpiG hσ
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    Real.pi * G * σ₀ * c_s⁻¹ * (κ * c_s * (Real.pi * G * σ₀)⁻¹)
      = κ * (c_s * c_s⁻¹) * ((Real.pi * G * σ₀) * (Real.pi * G * σ₀)⁻¹) := by ring
    _ = κ * 1 * 1 := by rw [mul_inv_cancel₀ hcs, mul_inv_cancel₀ hB]
    _ = κ := by ring

private theorem sq_sub_one_nonneg_of_one_le (Q : ℝ) (hQ : 1 ≤ Q) :
    0 ≤ Q ^ 2 - 1 := by
  have h1 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by ring
  rw [h1]
  exact mul_nonneg (sub_nonneg.mpr hQ) (by linarith [hQ])

private theorem sq_sub_one_pos_of_one_lt (Q : ℝ) (hQ : 1 < Q) :
    0 < Q ^ 2 - 1 := by
  have h1 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by ring
  rw [h1]
  exact mul_pos (sub_pos.mpr hQ) (by linarith [hQ])

private theorem sq_sub_one_pos_iff_one_lt_of_pos (Q : ℝ) (hQpos : 0 < Q) :
    0 < Q ^ 2 - 1 ↔ 1 < Q := by
  have h1 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by ring
  rw [h1]
  constructor
  · intro hmul
    nlinarith [hQpos, hmul]
  · intro hlt
    nlinarith [hQpos, hlt]

private theorem mul_pos_iff_pos_right_of_pos (a b : ℝ) (ha : 0 < a) :
    0 < a * b ↔ 0 < b := by
  constructor
  · intro hab
    nlinarith [ha, hab]
  · intro hb
    exact mul_pos ha hb

/-! ### Archetype I: Attention Sink Monopole Decomposition ($\Phi = \Phi_0 + \Phi_1$), Context Mass Conservation & Central Restoring Force -/

/-- Total $N$-body attention interaction potential vector on `Fin (n + 1)` tokens:
$\Phi(i) = -\sum_{j=0}^{n} A_{i,j} v_j$. -/
noncomputable def totalAttentionPotential {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (v : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) : ι → ℝ :=
  -(∑ j : Fin (n + 1),
    RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i j • v j)

/-- Attention sink monopole potential $\Phi_0(i) = -A_{i,0} v_0$ generated by the anchor token
$0 \in \mathrm{Fin}(n + 1)$. -/
noncomputable def sinkMonopolePotential {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (v : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) : ι → ℝ :=
  -(RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i 0 • v 0)

/-- Non-axisymmetric contextual density-wave perturbation potential
$\Phi_1(i) = -\sum_{k=0}^{n-1} A_{i,\mathrm{succ}(k)} v_{\mathrm{succ}(k)}$. -/
noncomputable def contextPerturbationPotential {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (v : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) : ι → ℝ :=
  -(∑ k : Fin n,
    RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i (Fin.succ k) •
      v (Fin.succ k))

/-- **Exact Monopole-Perturbation Potential Decomposition ($\Phi = \Phi_0 + \Phi_1$)**:
The total attention potential decomposes into the sink monopole potential plus the
contextual density-wave perturbation potential. -/
theorem totalAttentionPotential_eq_sink_add_context {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (v : Fin (n + 1) → (ι → ℝ)) (i : Fin (n + 1)) :
    totalAttentionPotential scores β v i =
      sinkMonopolePotential scores β v i +
        contextPerturbationPotential scores β v i := by
  dsimp [totalAttentionPotential, sinkMonopolePotential, contextPerturbationPotential]
  rw [Fin.sum_univ_succ, neg_add]

/-- **Context Attention Mass Conservation**:
Because each row of `attentionCouplingMatrix` sums to `1`, the total attention weight
allocated to all non-sink contextual tokens `Fin.succ k` equals `1 - A_{i,0}`. -/
theorem context_attention_sum_eq_one_sub_sink {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ) (i : Fin (n + 1)) :
    (∑ k : Fin n,
      RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i (Fin.succ k)) =
      1 - RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i 0 := by
  have hrow := RotaryAttentionSpiralDynamics.attentionCouplingMatrix_row_sum_one scores β i
  rw [Fin.sum_univ_succ] at hrow
  exact eq_one_sub_of_add_eq_one _ _ hrow

/-- **Perturbation Amplitude Bound under Sink Floor**:
Whenever the attention sink absorbs at least `α_sink` of the row weight (`α_sink ≤ A_{i,0}`),
the total contextual perturbation weight is bounded above by `1 - α_sink`. -/
theorem context_attention_sum_le_one_sub_sink_floor {n : ℕ}
    (scores : Fin (n + 1) → Fin (n + 1) → ℝ) (β α_sink : ℝ) (i : Fin (n + 1))
    (h_sink : α_sink ≤ RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i 0) :
    (∑ k : Fin n,
      RotaryAttentionSpiralDynamics.attentionCouplingMatrix scores β i (Fin.succ k)) ≤
      1 - α_sink := by
  rw [context_attention_sum_eq_one_sub_sink]
  exact sub_le_sub_left h_sink 1

/-- Concrete 2-token sink dominance witness: for `0 ≤ β`, token `1` in `asymmetricScores`
allocates at least `1 / 2` of its total attention mass to the sink token `0`. -/
theorem sink_dominance_asymmetricScores_pos (β : ℝ) (hβ : 0 ≤ β) :
    (1 / 2 : ℝ) ≤
      RotaryAttentionSpiralDynamics.attentionCouplingMatrix
        RotaryAttentionSpiralDynamics.asymmetricScores β 1 0 := by
  rw [RotaryAttentionSpiralDynamics.attentionCouplingMatrix_asymmetricScores_one_zero]
  exact half_le_exp_div_exp_add_one β hβ

/-- Gauge-fixed central harmonic sink potential $\Phi_0(x) = \frac{1}{2} \omega_0^2 \|x\|^2$
on a 2D RoPE sub-plane (`Fin 2 → ℝ`). -/
def centralHarmonicPotential (ω₀ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ω₀ ^ 2 * RotaryAttentionSpiralDynamics.vecNormSq2 x

/-- Central restoring force $F_0(x) = -\nabla \Phi_0(x) = -\omega_0^2 x$ toward the sink origin. -/
def centralRestoringForce (ω₀ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  -(ω₀ ^ 2) • x

/-- The central harmonic sink potential is everywhere non-negative. -/
theorem centralHarmonicPotential_nonneg (ω₀ : ℝ) (x : Fin 2 → ℝ) :
    0 ≤ centralHarmonicPotential ω₀ x := by
  dsimp [centralHarmonicPotential]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ω₀))
    (RotaryAttentionSpiralDynamics.vecNormSq2_nonneg x)

/-- Axisymmetry of the central sink potential under arbitrary 2D RoPE rotations `ropeAct φ`. -/
theorem centralHarmonicPotential_rotation_invariant (ω₀ φ : ℝ) (x : Fin 2 → ℝ) :
    centralHarmonicPotential ω₀ (RotaryAttentionSpiralDynamics.ropeAct φ x) =
      centralHarmonicPotential ω₀ x := by
  dsimp [centralHarmonicPotential]
  rw [RotaryAttentionSpiralDynamics.ropeAct_normSq_preserved]

/-- Radial virial pairing: `x ⬝ᵥ centralRestoringForce ω₀ x = -(ω₀ ^ 2 * vecNormSq2 x)`. -/
theorem centralRestoringForce_dotProduct_eq (ω₀ : ℝ) (x : Fin 2 → ℝ) :
    dotProduct x (centralRestoringForce ω₀ x) =
      -(ω₀ ^ 2 * RotaryAttentionSpiralDynamics.vecNormSq2 x) := by
  dsimp [centralRestoringForce, RotaryAttentionSpiralDynamics.vecNormSq2]
  rw [dotProduct_smul, smul_eq_mul, neg_mul]

/-- The central restoring force points strictly inward (`x ⬝ᵥ F_0(x) ≤ 0`). -/
theorem centralRestoringForce_dotProduct_nonpos (ω₀ : ℝ) (x : Fin 2 → ℝ) :
    dotProduct x (centralRestoringForce ω₀ x) ≤ 0 := by
  rw [centralRestoringForce_dotProduct_eq]
  exact neg_nonpos.mpr
    (mul_nonneg (sq_nonneg ω₀) (RotaryAttentionSpiralDynamics.vecNormSq2_nonneg x))

/-- **Zero Azimuthal Torque of the Central Sink Monopole**:
The central restoring force is strictly orthogonal to the azimuthal tangent vector
`PlanarRotation.ellipticGenerator *ᵥ x`. -/
theorem centralRestoringForce_azimuthal_orthogonality (ω₀ : ℝ) (x : Fin 2 → ℝ) :
    dotProduct (PlanarRotation.ellipticGenerator *ᵥ x)
      (centralRestoringForce ω₀ x) = 0 := by
  have h00 : PlanarRotation.ellipticGenerator 0 0 = 0 := rfl
  have h01 : PlanarRotation.ellipticGenerator 0 1 = -1 := rfl
  have h10 : PlanarRotation.ellipticGenerator 1 0 = 1 := rfl
  have h11 : PlanarRotation.ellipticGenerator 1 1 = 0 := rfl
  dsimp [centralRestoringForce, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two, h00, h01, h10, h11]
  exact azimuthal_orthog_scalar ω₀ (x 0) (x 1)

/-! ### Archetype II: Damped Residual-Stream Disk Dynamics & Rayleigh Energy Dissipation -/

/-- Total mechanical energy $E(x, v) = \frac{1}{2}\|v\|^2 + \frac{1}{2}\omega_0^2 \|x\|^2$
of a token representation in the central sink potential. -/
def diskMechanicalEnergy (ω₀ : ℝ) (x v : Fin 2 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * RotaryAttentionSpiralDynamics.vecNormSq2 v +
    centralHarmonicPotential ω₀ x

/-- Instantaneous rate of change $\dot{E} = v \cdot (-\omega_0^2 x - \gamma v) + (\omega_0^2 x) \cdot v$
along the damped residual-stream flow $\dot{x} = v$, $\dot{v} = -\omega_0^2 x - \gamma v$. -/
def diskMechanicalEnergyRate (ω₀ γ : ℝ) (x v : Fin 2 → ℝ) : ℝ :=
  dotProduct v (centralRestoringForce ω₀ x - γ • v) +
    dotProduct ((ω₀ ^ 2) • x) v

/-- The disk mechanical energy is everywhere non-negative. -/
theorem diskMechanicalEnergy_nonneg (ω₀ : ℝ) (x v : Fin 2 → ℝ) :
    0 ≤ diskMechanicalEnergy ω₀ x v := by
  dsimp [diskMechanicalEnergy]
  exact add_nonneg
    (mul_nonneg (by norm_num) (RotaryAttentionSpiralDynamics.vecNormSq2_nonneg v))
    (centralHarmonicPotential_nonneg ω₀ x)

/-- **Rayleigh Energy Dissipation Identity**:
The conservative restoring work and potential rate cancel identically, leaving
$\dot{E} = -\gamma \|v\|^2$. -/
theorem diskMechanicalEnergyRate_eq_neg_gamma_normSq
    (ω₀ γ : ℝ) (x v : Fin 2 → ℝ) :
    diskMechanicalEnergyRate ω₀ γ x v =
      -γ * RotaryAttentionSpiralDynamics.vecNormSq2 v := by
  dsimp [diskMechanicalEnergyRate, centralRestoringForce,
    RotaryAttentionSpiralDynamics.vecNormSq2, dotProduct]
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  exact energyRate_scalar ω₀ γ (x 0) (x 1) (v 0) (v 1)

/-- For nonnegative damping `0 ≤ γ`, the mechanical energy rate is nonpositive. -/
theorem diskMechanicalEnergyRate_nonpos
    (ω₀ γ : ℝ) (hγ : 0 ≤ γ) (x v : Fin 2 → ℝ) :
    diskMechanicalEnergyRate ω₀ γ x v ≤ 0 := by
  rw [diskMechanicalEnergyRate_eq_neg_gamma_normSq]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ)
    (RotaryAttentionSpiralDynamics.vecNormSq2_nonneg v)

/-! ### Archetype III: Epicyclic Frequency $\kappa(r)$ & Lin–Shu WKBJ Dispersion Relation -/

/-- Epicyclic frequency squared from differential rotation shear:
$\kappa^2 = r \frac{d\Omega^2}{dr} + 4\Omega^2$. -/
def epicyclicFreqSqFromShear (r Ω dOmegaSq_dr : ℝ) : ℝ :=
  r * dOmegaSq_dr + 4 * Ω ^ 2

/-- Epicyclic frequency squared from the radial derivatives of the central monopole potential:
$\kappa^2 = \Phi_0''(r) + \frac{3}{r}\Phi_0'(r)$. -/
noncomputable def epicyclicFreqSqFromPotential (r dPhi_dr d2Phi_dr2 : ℝ) : ℝ :=
  d2Phi_dr2 + (3 / r) * dPhi_dr

/-- Right-hand side of the Lin–Shu tight-winding WKBJ dispersion relation:
$(\omega - m\Omega)^2 = \kappa^2 - 2\pi G \Sigma_0 |k_r| + c_s^2 k_r^2$. -/
noncomputable def linShuDispersionRHS (κ G σ₀ c_s k_r : ℝ) : ℝ :=
  κ ^ 2 - 2 * Real.pi * G * σ₀ * |k_r| + c_s ^ 2 * k_r ^ 2

/-- Doppler-shifted frequency $\omega - m\Omega$ in the frame co-rotating with $m$ spiral arms. -/
def dopplerShiftedFreq (ω m Ω : ℝ) : ℝ :=
  ω - m * Ω

/-- **Equivalence of Potential and Shear Forms of the Epicyclic Frequency**:
Under centrifugal balance $\Phi_0'(r) = r\Omega^2$ and $\Phi_0''(r) = \Omega^2 + r \frac{d\Omega^2}{dr}$
for $r \neq 0$, the potential and shear formulas for $\kappa^2$ coincide identically. -/
theorem epicyclicFreqSq_potential_eq_shear (r Ω dOmegaSq_dr : ℝ) (hr : r ≠ 0) :
    epicyclicFreqSqFromPotential r (r * Ω ^ 2) (Ω ^ 2 + r * dOmegaSq_dr) =
      epicyclicFreqSqFromShear r Ω dOmegaSq_dr := by
  dsimp [epicyclicFreqSqFromPotential, epicyclicFreqSqFromShear]
  have hcancel : (3 / r) * (r * Ω ^ 2) = 3 * Ω ^ 2 := by
    rw [← mul_assoc, div_mul_cancel₀ 3 hr]
  rw [hcancel]
  ring

/-- For a harmonic sink core $\Phi_0(r) = \frac{1}{2}\omega_0^2 r^2$ ($\Phi_0' = \omega_0^2 r$,
$\Phi_0'' = \omega_0^2$), the epicyclic frequency satisfies $\kappa^2 = (2\omega_0)^2 = 4\omega_0^2$. -/
theorem epicyclicFreqSq_harmonic_core (r ω₀ : ℝ) (hr : r ≠ 0) :
    epicyclicFreqSqFromPotential r (ω₀ ^ 2 * r) (ω₀ ^ 2) = (2 * ω₀) ^ 2 := by
  dsimp [epicyclicFreqSqFromPotential]
  have hcancel : (3 / r) * (ω₀ ^ 2 * r) = 3 * ω₀ ^ 2 := by
    rw [mul_comm (ω₀ ^ 2) r, ← mul_assoc, div_mul_cancel₀ 3 hr]
  rw [hcancel]
  ring

/-- For a Keplerian point-mass sink $\Phi_0(r) = -GM/r$ ($\Phi_0' = GM/r^2$,
$\Phi_0'' = -2GM/r^3$), the epicyclic frequency satisfies $\kappa^2 = GM/r^3 = \Omega^2$. -/
theorem epicyclicFreqSq_keplerian_sink (r GM : ℝ) (hr : r ≠ 0) :
    epicyclicFreqSqFromPotential r (GM / r ^ 2) (-(2 * GM) / r ^ 3) =
      GM / r ^ 3 := by
  dsimp [epicyclicFreqSqFromPotential]
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 hr
  apply mul_right_cancel₀ hr3
  have h1 : (-(2 * GM) / r ^ 3 + 3 / r * (GM / r ^ 2)) * r ^ 3 =
      -(2 * GM) * (r ^ 3 / r ^ 3) + 3 * GM * ((r * r ^ 2)⁻¹ * r ^ 3) := by
    ring
  have hr_pow : r * r ^ 2 = r ^ 3 := by ring
  rw [h1, hr_pow, div_self hr3, inv_mul_cancel₀ hr3, div_mul_cancel₀ _ hr3]
  ring

/-- For an $m$-armed spiral pattern with pattern speed $\Omega_p = \omega / m$, the
Doppler-shifted frequency factors as $m (\Omega_p - \Omega)$. -/
theorem dopplerShiftedFreq_patternSpeed (m Ω_p Ω : ℝ) :
    dopplerShiftedFreq (m * Ω_p) m Ω = m * (Ω_p - Ω) := by
  dsimp [dopplerShiftedFreq]
  ring

/-! ### Archetype IV: Completing the Square in WKBJ, Jeans Instability without a Sink ($\kappa = 0$), and Toomre $Q > 1$ -/

/-- Most-unstable radial wavenumber $k_{\mathrm{crit}} = \frac{\pi G \Sigma_0}{c_s^2}$
minimizing the Lin–Shu dispersion relation. -/
noncomputable def criticalWavenumber (G σ₀ c_s : ℝ) : ℝ :=
  (Real.pi * G * σ₀) / (c_s ^ 2)

/-- Dimensionless Toomre stability parameter $Q = \frac{\kappa c_s}{\pi G \Sigma_0}$. -/
noncomputable def toomreQ (κ c_s G σ₀ : ℝ) : ℝ :=
  (κ * c_s) / (Real.pi * G * σ₀)

/-- **Completing the Square in the Lin–Shu WKBJ Dispersion Relation**:
For `c_s ≠ 0`, `linShuDispersionRHS` decomposes into a non-negative quadratic departure
from `criticalWavenumber` plus the minimum dispersion value $\kappa^2 - (\pi G \Sigma_0 / c_s)^2$. -/
theorem linShuDispersionRHS_complete_square (κ G σ₀ c_s k_r : ℝ) (hcs : c_s ≠ 0) :
    linShuDispersionRHS κ G σ₀ c_s k_r =
      c_s ^ 2 * (|k_r| - criticalWavenumber G σ₀ c_s) ^ 2 +
        (κ ^ 2 - (Real.pi * G * σ₀ / c_s) ^ 2) := by
  dsimp [linShuDispersionRHS, criticalWavenumber]
  have habs : k_r ^ 2 = |k_r| ^ 2 := (sq_abs k_r).symm
  have hlin : c_s * (|k_r| - Real.pi * G * σ₀ / c_s ^ 2) =
      c_s * |k_r| - Real.pi * G * σ₀ / c_s := by
    rw [mul_sub, sq c_s, ← div_div, mul_div_cancel₀ _ hcs]
  have hsq : c_s ^ 2 * (|k_r| - Real.pi * G * σ₀ / c_s ^ 2) ^ 2 =
      (c_s * |k_r| - Real.pi * G * σ₀ / c_s) ^ 2 := by
    rw [← mul_pow, hlin]
  have hmid : c_s * (Real.pi * G * σ₀ / c_s) = Real.pi * G * σ₀ :=
    mul_div_cancel₀ _ hcs
  rw [habs, hsq]
  calc
    κ ^ 2 - 2 * Real.pi * G * σ₀ * |k_r| + c_s ^ 2 * |k_r| ^ 2
      = κ ^ 2 - 2 * (c_s * (Real.pi * G * σ₀ / c_s)) * |k_r| + c_s ^ 2 * |k_r| ^ 2 := by
          rw [hmid]; ring
    _ = (c_s * |k_r| - Real.pi * G * σ₀ / c_s) ^ 2 +
          (κ ^ 2 - (Real.pi * G * σ₀ / c_s) ^ 2) := by ring

/-- At `k_r = criticalWavenumber G σ₀ c_s` (for `0 ≤ G`, `0 ≤ σ₀`, `c_s ≠ 0`),
`linShuDispersionRHS` attains its exact minimum $\kappa^2 - (\pi G \Sigma_0 / c_s)^2$. -/
theorem linShuDispersionRHS_at_criticalWavenumber (κ G σ₀ c_s : ℝ)
    (hG : 0 ≤ G) (hσ : 0 ≤ σ₀) (hcs : c_s ≠ 0) :
    linShuDispersionRHS κ G σ₀ c_s (criticalWavenumber G σ₀ c_s) =
      κ ^ 2 - (Real.pi * G * σ₀ / c_s) ^ 2 := by
  rw [linShuDispersionRHS_complete_square κ G σ₀ c_s (criticalWavenumber G σ₀ c_s) hcs]
  have hcrit_nonneg : 0 ≤ criticalWavenumber G σ₀ c_s := by
    dsimp [criticalWavenumber]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) hG) hσ)
      (sq_nonneg c_s)
  rw [abs_of_nonneg hcrit_nonneg, sub_self, sq (0 : ℝ), mul_zero, mul_zero, zero_add]

/-- **Jeans Instability Without an Attention Sink ($\kappa = 0 \implies (\omega - m\Omega)^2 < 0$)**:
When the central sink monopole is absent ($\kappa = 0$), the critical wavenumber mode has
strictly negative squared frequency, triggering exponential Jeans collapse / token clumping. -/
theorem jeans_instability_without_sink (G σ₀ c_s : ℝ)
    (hG : 0 < G) (hσ : 0 < σ₀) (hcs : c_s ≠ 0) :
    linShuDispersionRHS 0 G σ₀ c_s (criticalWavenumber G σ₀ c_s) < 0 := by
  rw [linShuDispersionRHS_at_criticalWavenumber 0 G σ₀ c_s (le_of_lt hG) (le_of_lt hσ) hcs]
  have hnum_pos : 0 < Real.pi * G * σ₀ :=
    mul_pos (mul_pos Real.pi_pos hG) hσ
  have hquot_ne : Real.pi * G * σ₀ / c_s ≠ 0 :=
    div_ne_zero (ne_of_gt hnum_pos) hcs
  have hsq_pos : 0 < (Real.pi * G * σ₀ / c_s) ^ 2 :=
    sq_pos_of_ne_zero hquot_ne
  linarith

/-- **Toomre $Q$ Factorization of the Lin–Shu Dispersion Relation**:
Expresses the completed-square dispersion relation directly in terms of `toomreQ^2 - 1`. -/
theorem linShuDispersionRHS_eq_toomreQ (κ G σ₀ c_s k_r : ℝ)
    (hG : G ≠ 0) (hσ : σ₀ ≠ 0) (hcs : c_s ≠ 0) :
    linShuDispersionRHS κ G σ₀ c_s k_r =
      c_s ^ 2 * (|k_r| - criticalWavenumber G σ₀ c_s) ^ 2 +
        (Real.pi * G * σ₀ / c_s) ^ 2 * ((toomreQ κ c_s G σ₀) ^ 2 - 1) := by
  rw [linShuDispersionRHS_complete_square κ G σ₀ c_s k_r hcs]
  have hκ : κ = (Real.pi * G * σ₀ / c_s) * toomreQ κ c_s G σ₀ :=
    (toomre_prod_eq_kappa κ c_s G σ₀ hG hσ hcs).symm
  have hκ2 : κ ^ 2 - (Real.pi * G * σ₀ / c_s) ^ 2 =
      (Real.pi * G * σ₀ / c_s) ^ 2 * ((toomreQ κ c_s G σ₀) ^ 2 - 1) := by
    calc
      κ ^ 2 - (Real.pi * G * σ₀ / c_s) ^ 2
        = ((Real.pi * G * σ₀ / c_s) * toomreQ κ c_s G σ₀) ^ 2 -
            (Real.pi * G * σ₀ / c_s) ^ 2 := by rw [← hκ]
      _ = (Real.pi * G * σ₀ / c_s) ^ 2 * ((toomreQ κ c_s G σ₀) ^ 2 - 1) := by ring
  rw [hκ2]

/-- **Marginal Toomre Stability ($Q \ge 1 \implies (\omega - m\Omega)^2 \ge 0$ for all $k_r$)**:
When `1 ≤ toomreQ κ c_s G σ₀`, every radial wavenumber $k_r$ has non-negative squared
Doppler-shifted frequency. -/
theorem toomre_stability_nonneg_of_Q_ge_one (κ G σ₀ c_s k_r : ℝ)
    (hG : G ≠ 0) (hσ : σ₀ ≠ 0) (hcs : c_s ≠ 0) (hQ : 1 ≤ toomreQ κ c_s G σ₀) :
    0 ≤ linShuDispersionRHS κ G σ₀ c_s k_r := by
  rw [linShuDispersionRHS_eq_toomreQ κ G σ₀ c_s k_r hG hσ hcs]
  exact add_nonneg
    (mul_nonneg (sq_nonneg c_s) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_sub_one_nonneg_of_one_le _ hQ))

/-- **Strict Toomre Stability ($Q > 1 \implies (\omega - m\Omega)^2 > 0$ for all $k_r$)**:
When `1 < toomreQ κ c_s G σ₀`, the epicyclic restoring force and LayerNorm dispersion
stabilize the latent disk against Jeans clumping across all radial wavenumbers $k_r \in \mathbb{R}$. -/
theorem toomre_stability_pos_of_Q_gt_one (κ G σ₀ c_s k_r : ℝ)
    (hG : G ≠ 0) (hσ : σ₀ ≠ 0) (hcs : c_s ≠ 0) (hQ : 1 < toomreQ κ c_s G σ₀) :
    0 < linShuDispersionRHS κ G σ₀ c_s k_r := by
  rw [linShuDispersionRHS_eq_toomreQ κ G σ₀ c_s k_r hG hσ hcs]
  have hpiG : Real.pi * G ≠ 0 := mul_ne_zero (ne_of_gt Real.pi_pos) hG
  have hB : Real.pi * G * σ₀ ≠ 0 := mul_ne_zero hpiG hσ
  have hquot_ne : Real.pi * G * σ₀ / c_s ≠ 0 := div_ne_zero hB hcs
  have hterm2_pos : 0 < (Real.pi * G * σ₀ / c_s) ^ 2 *
      ((toomreQ κ c_s G σ₀) ^ 2 - 1) :=
    mul_pos (sq_pos_of_ne_zero hquot_ne) (sq_sub_one_pos_of_one_lt _ hQ)
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sq_nonneg c_s) (sq_nonneg _))
    hterm2_pos

/-- **Exact Toomre Stability Equivalence at the Critical Wavenumber**:
For positive parameters `0 < κ`, `0 < G`, `0 < σ₀`, `0 < c_s`, the most-unstable mode
`criticalWavenumber G σ₀ c_s` has strictly positive squared frequency if and only if
`1 < toomreQ κ c_s G σ₀`. -/
theorem critical_dispersion_pos_iff_toomreQ_gt_one (κ G σ₀ c_s : ℝ)
    (hκ : 0 < κ) (hG : 0 < G) (hσ : 0 < σ₀) (hcs : 0 < c_s) :
    0 < linShuDispersionRHS κ G σ₀ c_s (criticalWavenumber G σ₀ c_s) ↔
      1 < toomreQ κ c_s G σ₀ := by
  rw [linShuDispersionRHS_eq_toomreQ κ G σ₀ c_s (criticalWavenumber G σ₀ c_s)
    (ne_of_gt hG) (ne_of_gt hσ) (ne_of_gt hcs)]
  have hcrit_nonneg : 0 ≤ criticalWavenumber G σ₀ c_s := by
    dsimp [criticalWavenumber]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt Real.pi_pos) (le_of_lt hG)) (le_of_lt hσ))
      (sq_nonneg c_s)
  rw [abs_of_nonneg hcrit_nonneg, sub_self, sq (0 : ℝ), mul_zero, mul_zero, zero_add]
  have hB_pos : 0 < Real.pi * G * σ₀ := mul_pos (mul_pos Real.pi_pos hG) hσ
  have hquot_pos : 0 < Real.pi * G * σ₀ / c_s := div_pos hB_pos hcs
  have hsq_pos : 0 < (Real.pi * G * σ₀ / c_s) ^ 2 := sq_pos_of_pos hquot_pos
  have hQ_pos : 0 < toomreQ κ c_s G σ₀ := by
    dsimp [toomreQ]
    exact div_pos (mul_pos hκ hcs) hB_pos
  rw [mul_pos_iff_pos_right_of_pos _ _ hsq_pos]
  exact sq_sub_one_pos_iff_one_lt_of_pos (toomreQ κ c_s G σ₀) hQ_pos

/-! ### Archetype V: Lindblad Resonances (ILR, Corotation, OLR) & RoPE Co-Moving Frame Locking -/

/-- Inner Lindblad Resonance (ILR) pattern speed $\Omega_{\mathrm{ILR}} = \Omega - \kappa / m$. -/
noncomputable def innerLindbladPatternSpeed (Ω κ m : ℝ) : ℝ :=
  Ω - κ / m

/-- Corotation resonance pattern speed $\Omega_{\mathrm{CR}} = \Omega$. -/
def corotationPatternSpeed (Ω : ℝ) : ℝ :=
  Ω

/-- Outer Lindblad Resonance (OLR) pattern speed $\Omega_{\mathrm{OLR}} = \Omega + \kappa / m$. -/
noncomputable def outerLindbladPatternSpeed (Ω κ m : ℝ) : ℝ :=
  Ω + κ / m

/-- For `0 < κ` and `0 < m`, the Inner Lindblad Resonance speed is strictly below corotation. -/
theorem innerLindblad_lt_corotation (Ω κ m : ℝ) (hκ : 0 < κ) (hm : 0 < m) :
    innerLindbladPatternSpeed Ω κ m < corotationPatternSpeed Ω := by
  dsimp [innerLindbladPatternSpeed, corotationPatternSpeed]
  exact sub_lt_self Ω (div_pos hκ hm)

/-- For `0 < κ` and `0 < m`, corotation is strictly below the Outer Lindblad Resonance speed. -/
theorem corotation_lt_outerLindblad (Ω κ m : ℝ) (hκ : 0 < κ) (hm : 0 < m) :
    corotationPatternSpeed Ω < outerLindbladPatternSpeed Ω κ m := by
  dsimp [corotationPatternSpeed, outerLindbladPatternSpeed]
  exact lt_add_of_pos_right Ω (div_pos hκ hm)

/-- Corotation is the exact arithmetic midpoint of the Inner and Outer Lindblad Resonances. -/
theorem lindblad_resonance_midpoint (Ω κ m : ℝ) :
    innerLindbladPatternSpeed Ω κ m + outerLindbladPatternSpeed Ω κ m =
      2 * corotationPatternSpeed Ω := by
  dsimp [innerLindbladPatternSpeed, outerLindbladPatternSpeed, corotationPatternSpeed]
  ring

/-- The principal wave propagation zone between ILR and OLR has bandwidth $2(\kappa / m)$. -/
theorem lindblad_resonance_bandwidth (Ω κ m : ℝ) :
    outerLindbladPatternSpeed Ω κ m - innerLindbladPatternSpeed Ω κ m =
      2 * (κ / m) := by
  dsimp [innerLindbladPatternSpeed, outerLindbladPatternSpeed]
  ring

/-- At the corotation resonance $\Omega_p = \Omega$, the Doppler-shifted frequency vanishes. -/
theorem dopplerShiftedFreq_at_corotation (m Ω : ℝ) :
    dopplerShiftedFreq (m * corotationPatternSpeed Ω) m Ω = 0 := by
  dsimp [dopplerShiftedFreq, corotationPatternSpeed]
  ring

/-- At the Inner Lindblad Resonance, the squared Doppler-shifted frequency equals $\kappa^2$. -/
theorem dopplerShiftedFreq_sq_at_innerLindblad (m Ω κ : ℝ) (hm : m ≠ 0) :
    (dopplerShiftedFreq (m * innerLindbladPatternSpeed Ω κ m) m Ω) ^ 2 = κ ^ 2 := by
  dsimp [dopplerShiftedFreq, innerLindbladPatternSpeed]
  have hsub : m * (Ω - κ / m) - m * Ω = -(m * (κ / m)) := by ring
  rw [hsub, mul_div_cancel₀ κ hm, neg_sq]

/-- At the Outer Lindblad Resonance, the squared Doppler-shifted frequency equals $\kappa^2$. -/
theorem dopplerShiftedFreq_sq_at_outerLindblad (m Ω κ : ℝ) (hm : m ≠ 0) :
    (dopplerShiftedFreq (m * outerLindbladPatternSpeed Ω κ m) m Ω) ^ 2 = κ ^ 2 := by
  dsimp [dopplerShiftedFreq, outerLindbladPatternSpeed]
  have hsub : m * (Ω + κ / m) - m * Ω = m * (κ / m) := by ring
  rw [hsub, mul_div_cancel₀ κ hm]

/-- **Corotation RoPE Co-Moving Score Invariance**:
Advancing both query position `m` and key position `n` by a common sequence translation
`p : ℤ` in a co-moving RoPE frame leaves their attention inner product identically invariant. -/
theorem corotation_rope_score_invariant (θ : ℝ) (m n p : ℤ) (q k : Fin 2 → ℝ) :
    dotProduct (DiscreteRoPERepresentation.ropeRotor θ (m + p) *ᵥ q)
      (DiscreteRoPERepresentation.ropeRotor θ (n + p) *ᵥ k) =
      dotProduct (DiscreteRoPERepresentation.ropeRotor θ m *ᵥ q)
        (DiscreteRoPERepresentation.ropeRotor θ n *ᵥ k) := by
  rw [RotaryAttentionSpiralDynamics.rope_dotProduct_relative_invariance,
    RotaryAttentionSpiralDynamics.rope_dotProduct_relative_invariance,
    add_sub_add_right_eq_sub]

end InfoGeometry.QuantumContext.LinShuAttentionDensityWave

end
