/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis
import InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic
import InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow

/-!
# Capstone Synthesis: Lin–Shu Density Waves, Majorana–Souriau Loxodromic Thermofield Double, Colimit Tomita Flow, and Jordan–Wigner CAR Bridge

This module establishes the four-pillar capstone synthesis uniting the Lin–Shu spiral density-wave
and KMS Petz radial quantization theory (`LinShuKMSPetzRadialSynthesis`), the Majorana–Souriau
metriplectic loxodromic propagator and thermofield double (`MajoranaSouriauMetriplecticLoxodromic`),
the Cuntz–UHF inductive colimit Tomita modular flow (`ColimitAttentionTomitaFlow`), and the
Jordan–Wigner / CAR $\longleftrightarrow$ $\mathrm{UHF}(2^\infty)$ superbracket bridge:

1. **Archetype I — Self-Consistent Multi-Head WKBJ Potential Saturation at Corotation & Lindblad Boundaries**:
   - Proves that at the corotation resonance $\omega = m_{\mathrm{arm}}\Omega_{\mathrm{CR}}$,
     the squared Doppler-shifted frequency `linShuDispersionLHS` vanishes identically
     (`corotation_linShuDispersionLHS_zero`), reducing the Lin–Shu WKBJ dispersion relation to the
     exact radial force balance $\kappa^2 = 2\pi G \sigma_0 |k_r| - c_s^2 k_r^2$
     (`corotation_dispersion_balance_iff`).
   - Defines the multi-head effective perturbation scale
     `multiHeadPerturbationScale σ₀ A Φ = σ₀ * multiHeadSpiralWave A Φ`, proving constructive crest
     saturation `multiHeadPerturbationScale_at_crest`, the global upper envelope bound
     `multiHeadPerturbationScale_le_crest`, and the self-consistent short-wave Lindblad resonance
     selection rule `lindblad_shortWave_at_multiHead_crest` at the multi-head interference crest.

2. **Archetype II — Majorana–Souriau Loxodromic Propagator $\longleftrightarrow$ Radial Cylinder Cone & Thermofield Double / Petz Spinor Synthesis**:
   - Bridges `MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator` directly to the 5-graded
     radial cylinder cone `RadialQuantizationFiveGradedCylinder.coneRadius` and `gradeTimeScale`
     (`loxodromicPropagator_eq_coneRadius_smul_rotation` and
     `loxodromicPropagator_eq_gradeTimeScale_negOne_smul_rotation`), to
     `RotaryAttentionSpiralDynamics.spiralTrajectory`
     (`loxodromicPropagator_mulVec_eq_spiralTrajectory`), and at integer sequence steps $m : \mathbb{Z}$
     to `DiscreteRoPERepresentation.ropeRotor`
     (`loxodromicPropagator_int_step_eq_coneRadius_smul_ropeRotor`).
   - Proves that under the energy-to-logit duality $E_j = -\ell_j$, the Souriau partition function
     `souriauPartition β (fun j => -logits j)` equals `softmaxPartitionZ logits β`
     (`souriauPartition_neg_eq_softmaxPartitionZ`), the Souriau Gibbs weight equals
     `AttentionKMSState.softmaxWeight` (`souriau_gibbsWeight_neg_eq_softmaxWeight`), and the
     Majorana–Souriau thermofield double amplitude `tfdRealAmplitude (fun j => -logits j) β i`
     is identically equal to the $\tau = 1/2$ KMS strip Petz spinor state
     `petzSpinorState logits β i` (`tfdRealAmplitude_neg_sq_eq_petzSpinorState_sq`,
     `tfdRealAmplitude_neg_eq_petzSpinorState`, and `tfdRealAmplitude_neg_unit_sphere`).

3. **Archetype III — Inductive Colimit Continuation ($k \hookrightarrow n$ Tower Stage Invariance of Mestel Toomre $Q$ & Colimit KMS Modular Flow)**:
   - Defines the dyadic stage radius `towerStageRadius k = coneRadius (k : ℝ)` on the Cuntz–UHF
     matrix tower, proving `towerStageRadius_pos`, `towerStageRadius_ne_zero`,
     `radialTime_towerStageRadius`, `logMonopolePotential_towerStageRadius`, and
     `flatRotationCurve_epicyclicFreqSq_towerStageRadius`.
   - Proves exact inductive tower-stage invariance `toomreQ_mestelDisk_towerStage_invariant` of
     the Mestel disk Toomre stability parameter across all tower stages $k, n : \mathbb{N}$ and
     universal stage-wise WKBJ dispersion positivity
     `kmsSoftmaxSink_mestelDisk_all_towerStages_dispersion_pos`.
   - Establishes genuine shared-carrier bridges connecting the real colimit modular-flow readout
     `Complex.re (selectedStageColimitFunctional ...)` to the squared Petz spinor and thermofield
     double expectation sums (`colimit_modularFlow_real_readout_eq_petzSpinor_sum` and
     `colimit_modularFlow_real_readout_eq_tfd_sum`), the KMS sink circular speed to the anchor
     Petz spinor and TFD amplitude (`sqrt_sinkCircularVelSq_eq_petzSpinor_mul`,
     `sqrt_sinkCircularVelSq_eq_tfd_mul`, and `toomreQ_kmsSoftmax_mestelDisk_towerStage_eq_tfd_ratio`),
     and the radial-cylinder-dilated Para-Kähler Fock CAR superbracket at the TFD unit-sphere
     pairing (`dilated_paraKahler_fock_superBracket_at_tfdRealAmplitude_sq`).

4. **Archetype IV — Jordan–Wigner / CAR $\longleftrightarrow$ $\mathrm{UHF}(2^\infty)$ Block-Diagonal Colimit & Superbracket Bridge**:
   - Defines the single-mode Para-Kähler Fock creation (`fockCreateMat`), annihilation
     (`fockAnnihilateMat`), Jordan–Wigner parity (`jordanWignerParity`), and Majorana
     (`majoranaPlus`, `majoranaMinus`) matrices in `Matrix (Fin 2) (Fin 2) ℝ`, proving nilpotency,
     parity involution and anticommutation, the CAR superbracket identity
     `oddSuperBracket_create_annihilate`, and the Majorana Clifford algebra relations.
   - Defines the block-diagonal UHF step embedding `uhfColimitEmbedStep` and proves that it
     preserves unit, addition, scalar multiplication, matrix multiplication, the odd-odd graded
     superbracket `ChakravalaGA.superBracket .odd .odd`, the CAR metric identity, and Tomita
     modular conjugation.
   - Bridges directly to the canonical Cuntz–UHF colimit transition homomorphism
     `CuntzMatrixAlgebraicStarColimit.rawMap h` and `ColimitAttentionTomitaFlow.modularFlow`,
     proving `cuntzColimit_rawMap_oddSuperBracket`, `modularFlow_oddSuperBracket`, and
     `cuntzColimit_rawMap_modularFlow_oddSuperBracket`.

## Scope Note

1. In Archetype I, `corotation_dispersion_balance_iff` and `lindblad_shortWave_at_multiHead_crest`
   are algebraic WKBJ dispersion identities over `ℝ` obtained by evaluating `linShuDispersionLHS`
   and `linShuDispersionRHS` at the corotation and Lindblad resonance pattern speeds and the
   multi-head constructive phase crest $\Phi_h = 0$.
2. In Archetype II, `tfdRealAmplitude_neg_eq_petzSpinorState` identifies the finite real
   thermofield double amplitude `tfdRealAmplitude (fun j => -logits j) β i` with the finite
   half-density square-root vector `petzSpinorState logits β i` on `[Fintype ι] [Nonempty ι]`.
3. In Archetype III, `towerStageRadius k = coneRadius (k : ℝ)` assigns the radial cylinder scale
   $e^k$ to matrix tower stage $k : \mathbb{N}$, and the shared-carrier theorems evaluate the
   algebraic direct-limit functional `selectedStageColimitFunctional` on complexified stage-$k$
   observables pushed forward along `rawMap h` ($k \le n$).
4. In Archetype IV, `fockCreateMat`, `fockAnnihilateMat`, `jordanWignerParity`, and
   `uhfColimitEmbedStep` formalize the finite $2 \times 2$ single-mode CAR / Jordan–Wigner
   representation and its $m \to m \oplus m$ block-diagonal doubling step, while
   `cuntzColimit_rawMap_modularFlow_oddSuperBracket` proves that the canonical $2^k \to 2^n$
   Cuntz–UHF transition `rawMap h` and `modularFlow` commute with the fermionic superbracket
   `ChakravalaGA.superBracket (R := ℂ) .odd .odd`.
-/

noncomputable section

namespace InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone

open BigOperators Matrix
open InfoGeometry.Routing
open InfoGeometry.Routing.PlanarRotation
open InfoGeometry.Routing.DiscreteRoPERepresentation
open InfoGeometry.Physics
open InfoGeometry.Physics.SouriauMassieuPlanckFunctional
open InfoGeometry.Canonical
open InfoGeometry.Canonical.RadialQuantizationFiveGradedCylinder
open InfoGeometry.Canonical.SuperGrassmannianProjectorEnvelope
open InfoGeometry.Canonical.ParaKahlerGradedFockCAR
open InfoGeometry.Canonical.CuntzMatrixTowerInstantiation
open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.QuantumContext
open InfoGeometry.QuantumContext.AttentionKMSState
open InfoGeometry.QuantumContext.RotaryAttentionSpiralDynamics
open InfoGeometry.QuantumContext.LinShuAttentionDensityWave
open InfoGeometry.QuantumContext.LinShuKMSPetzRadialSynthesis
open InfoGeometry.QuantumContext.AttentionStageColimitState
open InfoGeometry.QuantumContext.MatrixStageSelectedFunctional
open InfoGeometry.QuantumContext.ColimitAttentionTomitaFlow
open InfoGeometry.SuperMetriplectic
open InfoGeometry.SuperMetriplectic.MajoranaSouriauMetriplecticLoxodromic

/-! ### Private Scalar Arithmetic Helpers (Trap T16 Safe) -/

private theorem zero_eq_rhs_iff_kappa_sq_eq (κ G σ₀ c_s a : ℝ) :
    0 = κ ^ 2 - 2 * Real.pi * G * σ₀ * a + c_s ^ 2 * a ^ 2 ↔
      κ ^ 2 = 2 * Real.pi * G * σ₀ * a - c_s ^ 2 * a ^ 2 := by
  constructor <;> intro h <;> linarith

private theorem neg_mul_neg_eq (β x : ℝ) :
    -β * -x = β * x := by
  ring

private theorem one_mul_neg_gamma_t (γ t : ℝ) :
    (1 : ℝ) * Real.exp (-γ * t) = Real.exp (-γ * t) := by
  ring

private theorem neg_one_cast_mul_gamma_t (γ t : ℝ) :
    ((-1 : ℤ) : ℝ) * (γ * t) = -γ * t := by
  push_cast
  ring

/-!
### Archetype I — Self-Consistent Multi-Head WKBJ Potential Saturation at Corotation & Lindblad Boundaries
-/

/-- At the corotation resonance $\omega = m_{\mathrm{arm}} \Omega_{\mathrm{CR}}$, the left-hand
side $(\omega - m_{\mathrm{arm}}\Omega)^2$ of the Lin–Shu dispersion relation vanishes identically. -/
theorem corotation_linShuDispersionLHS_zero (m_arm Ω : ℝ) :
    LinShuKMSPetzRadialSynthesis.linShuDispersionLHS
      (m_arm * LinShuAttentionDensityWave.corotationPatternSpeed Ω) m_arm Ω = 0 := by
  dsimp [LinShuKMSPetzRadialSynthesis.linShuDispersionLHS]
  rw [LinShuAttentionDensityWave.dopplerShiftedFreq_at_corotation, sq, mul_zero]

/-- **Corotation Resonance WKBJ Force-Balance Criterion**:
At the corotation resonance $\omega = m_{\mathrm{arm}} \Omega_{\mathrm{CR}}$, the Lin–Shu dispersion
relation holds if and only if the epicyclic restoring term $\kappa^2$ exactly balances the radial
self-gravity and acoustic pressure terms $2\pi G \sigma_0 |k_r| - c_s^2 k_r^2$. -/
theorem corotation_dispersion_balance_iff (κ G σ₀ c_s k_r m_arm Ω : ℝ) :
    LinShuKMSPetzRadialSynthesis.linShuDispersionLHS
      (m_arm * LinShuAttentionDensityWave.corotationPatternSpeed Ω) m_arm Ω =
      LinShuAttentionDensityWave.linShuDispersionRHS κ G σ₀ c_s k_r ↔
      κ ^ 2 = 2 * Real.pi * G * σ₀ * |k_r| - c_s ^ 2 * k_r ^ 2 := by
  rw [corotation_linShuDispersionLHS_zero]
  dsimp [LinShuAttentionDensityWave.linShuDispersionRHS]
  rw [← sq_abs k_r]
  exact zero_eq_rhs_iff_kappa_sq_eq κ G σ₀ c_s |k_r|

/-- Effective radial density-wave surface perturbation scale
$\sigma_{\mathrm{eff}}(\sigma_0, A, \Phi) = \sigma_0 \sum_{h \in H} A_h \cos(\Phi_h)$ generated by
a base scale $\sigma_0$ and a multi-head RoPE spiral wave `multiHeadSpiralWave A Φ`. -/
noncomputable def multiHeadPerturbationScale {H : Type*} [Fintype H]
    (σ₀ : ℝ) (A Φ : H → ℝ) : ℝ :=
  σ₀ * LinShuKMSPetzRadialSynthesis.multiHeadSpiralWave A Φ

/-- **Multi-Head Constructive Crest Saturation of the Effective Perturbation Scale**:
When all RoPE attention heads align at phase crest $\Phi_h = 0$, `multiHeadPerturbationScale`
saturates at $\sigma_0 \sum_{h \in H} A_h$. -/
theorem multiHeadPerturbationScale_at_crest {H : Type*} [Fintype H]
    (σ₀ : ℝ) (A Φ : H → ℝ) (h_crest : ∀ h : H, Φ h = 0) :
    multiHeadPerturbationScale σ₀ A Φ = σ₀ * ∑ h : H, A h := by
  dsimp [multiHeadPerturbationScale]
  rw [LinShuKMSPetzRadialSynthesis.multiHeadSpiralWave_constructive_interference A Φ h_crest]

/-- **Global Constructive Envelope Bound on the Multi-Head Perturbation Scale**:
For $0 \le \sigma_0$ and non-negative head amplitudes $0 \le A_h$, `multiHeadPerturbationScale`
never exceeds its constructive crest value $\sigma_0 \sum_{h \in H} A_h$. -/
theorem multiHeadPerturbationScale_le_crest {H : Type*} [Fintype H]
    (σ₀ : ℝ) (A Φ : H → ℝ) (hσ₀ : 0 ≤ σ₀) (hA : ∀ h : H, 0 ≤ A h) :
    multiHeadPerturbationScale σ₀ A Φ ≤ σ₀ * ∑ h : H, A h := by
  dsimp [multiHeadPerturbationScale]
  exact mul_le_mul_of_nonneg_left
    (LinShuKMSPetzRadialSynthesis.multiHeadSpiralWave_le_constructive_crest A Φ hA) hσ₀

/-- **Self-Consistent Short-Wave Lindblad Selection Rule at the Multi-Head Interference Crest**:
At any Lindblad resonance $(\omega - m_{\mathrm{arm}}\Omega)^2 = \kappa^2$ with $c_s \ne 0$ and
multi-head phase lock $\Phi_h = 0$, the Lin–Shu dispersion relation driven by
`multiHeadPerturbationScale σ₀ A Φ` holds if and only if $k_r = 0$ or the radial wavenumber lies
on the short-wave acoustic branch $|k_r| = 2 k_{\mathrm{crit}}(G, \sigma_0 \sum_h A_h, c_s)$. -/
theorem lindblad_shortWave_at_multiHead_crest {H : Type*} [Fintype H]
    (κ G σ₀ c_s k_r ω m_arm Ω : ℝ) (A Φ : H → ℝ)
    (hcs : c_s ≠ 0) (h_res : (ω - m_arm * Ω) ^ 2 = κ ^ 2)
    (h_crest : ∀ h : H, Φ h = 0) :
    LinShuKMSPetzRadialSynthesis.linShuDispersionLHS ω m_arm Ω =
      LinShuAttentionDensityWave.linShuDispersionRHS
        κ G (multiHeadPerturbationScale σ₀ A Φ) c_s k_r ↔
      k_r = 0 ∨
        |k_r| = 2 * LinShuAttentionDensityWave.criticalWavenumber
          G (σ₀ * ∑ h : H, A h) c_s := by
  rw [multiHeadPerturbationScale_at_crest σ₀ A Φ h_crest]
  exact LinShuKMSPetzRadialSynthesis.lindblad_wave_branches_iff
    κ G (σ₀ * ∑ h : H, A h) c_s k_r ω m_arm Ω hcs h_res

/-!
### Archetype II — Majorana–Souriau Loxodromic Propagator $\longleftrightarrow$ Radial Cylinder Cone & Thermofield Double / Petz Spinor Synthesis
-/

/-- **Majorana–Souriau Loxodromic Propagator as Radial Cone Dilatation $\times$ Planar Rotation**:
The metriplectic loxodromic propagator `loxodromicPropagator γ ω t` equals the radial quantization
cone scale `coneRadius (-γ * t)` scalar-multiplying the symplectic planar rotation
`PlanarRotation.rotation (ω * t)`. -/
theorem loxodromicPropagator_eq_coneRadius_smul_rotation (γ ω t : ℝ) :
    MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator γ ω t =
      RadialQuantizationFiveGradedCylinder.coneRadius (-γ * t) •
        PlanarRotation.rotation (ω * t) :=
  rfl

/-- The radial damping factor of `loxodromicPropagator γ ω t` coincides with the conformal
grade `.negOne` time scale `gradeTimeScale .negOne (γ * t)`. -/
theorem loxodromicPropagator_eq_gradeTimeScale_negOne_smul_rotation (γ ω t : ℝ) :
    MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator γ ω t =
      RadialQuantizationFiveGradedCylinder.gradeTimeScale .negOne (γ * t) •
        PlanarRotation.rotation (ω * t) := by
  dsimp [MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator,
    RadialQuantizationFiveGradedCylinder.gradeTimeScale,
    RadialQuantizationFiveGradedCylinder.gradeWeight]
  rw [neg_one_cast_mul_gamma_t]

/-- **Loxodromic Propagator Action Generates the RoPE Logarithmic Spiral Trajectory**:
For $\omega \ne 0$, acting with `loxodromicPropagator γ ω t` on any initial state vector
$v_0 \in \mathbb{R}^2$ produces the exact logarithmic spiral trajectory
`RotaryAttentionSpiralDynamics.spiralTrajectory 1 (-γ / ω) ω t v₀`. -/
theorem loxodromicPropagator_mulVec_eq_spiralTrajectory
    (γ ω t : ℝ) (hω : ω ≠ 0) (v₀ : Fin 2 → ℝ) :
    MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator γ ω t *ᵥ v₀ =
      RotaryAttentionSpiralDynamics.spiralTrajectory 1 (-γ / ω) ω t v₀ := by
  dsimp [MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator,
    RotaryAttentionSpiralDynamics.spiralTrajectory,
    RotaryAttentionSpiralDynamics.spiralRadius,
    RotaryAttentionSpiralDynamics.ropeAct]
  rw [Matrix.smul_mulVec, div_mul_cancel₀ (-γ) hω, one_mul_neg_gamma_t]

/-- **Discrete Sequence-Step Loxodromic Propagator as Radial Cone $\times$ RoPE Rotor**:
At integer token position $m : \mathbb{Z}$, `loxodromicPropagator γ θ (m : ℝ)` factors into
`coneRadius (-γ * (m : ℝ))` times `DiscreteRoPERepresentation.ropeRotor θ m`. -/
theorem loxodromicPropagator_int_step_eq_coneRadius_smul_ropeRotor
    (γ θ : ℝ) (m : ℤ) :
    MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator γ θ (m : ℝ) =
      RadialQuantizationFiveGradedCylinder.coneRadius (-γ * (m : ℝ)) •
        DiscreteRoPERepresentation.ropeRotor θ m := by
  dsimp [MajoranaSouriauMetriplecticLoxodromic.loxodromicPropagator,
    RadialQuantizationFiveGradedCylinder.coneRadius,
    DiscreteRoPERepresentation.ropeRotor]
  rw [mul_comm θ (m : ℝ)]

/-- **Souriau Partition $\longleftrightarrow$ Softmax Partition Duality ($E_j = -\ell_j$)**:
Evaluating `SouriauMassieuPlanckFunctional.souriauPartition` on the negative logit energy profile
`fun j => -logits j` yields `LinShuKMSPetzRadialSynthesis.softmaxPartitionZ logits β`. -/
theorem souriauPartition_neg_eq_softmaxPartitionZ {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) :
    SouriauMassieuPlanckFunctional.souriauPartition β (fun j => -logits j) =
      LinShuKMSPetzRadialSynthesis.softmaxPartitionZ logits β := by
  dsimp [SouriauMassieuPlanckFunctional.souriauPartition,
    LinShuKMSPetzRadialSynthesis.softmaxPartitionZ]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [neg_mul_neg_eq]

/-- **Souriau Gibbs Weight $\longleftrightarrow$ KMS Softmax Weight Duality ($E_j = -\ell_j$)**:
Evaluating `SouriauMassieuPlanckFunctional.gibbsWeight` on the negative logit energy profile
`fun j => -logits j` recovers `AttentionKMSState.softmaxWeight logits β i`. -/
theorem souriau_gibbsWeight_neg_eq_softmaxWeight {ι : Type*} [Fintype ι]
    (logits : ι → ℝ) (β : ℝ) (i : ι) :
    SouriauMassieuPlanckFunctional.gibbsWeight β (fun j => -logits j) i =
      AttentionKMSState.softmaxWeight logits β i := by
  dsimp [SouriauMassieuPlanckFunctional.gibbsWeight,
    AttentionKMSState.softmaxWeight]
  rw [neg_mul_neg_eq, souriauPartition_neg_eq_softmaxPartitionZ]
  rfl

/-- **Thermofield Double Amplitude $\ge 0$**:
For any finite state space, the Majorana–Souriau thermofield double amplitude
`tfdRealAmplitude energy β i` is non-negative. -/
theorem tfdRealAmplitude_nonneg {ι : Type*} [Fintype ι]
    (energy : ι → ℝ) (β : ℝ) (i : ι) :
    0 ≤ MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude energy β i := by
  dsimp [MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude]
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)

/-- **Squared Thermofield Double Amplitude Equals Squared Petz Spinor State**:
Under $E_j = -\ell_j$, the square of `tfdRealAmplitude (fun j => -logits j) β i` equals the
square of the $\tau = 1/2$ KMS strip `petzSpinorState logits β i`. -/
theorem tfdRealAmplitude_neg_sq_eq_petzSpinorState_sq
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (i : ι) :
    (MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β i) ^ 2 =
      (LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i) ^ 2 := by
  rw [MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude_sq_eq_souriau_gibbsWeight,
    souriau_gibbsWeight_neg_eq_softmaxWeight,
    LinShuKMSPetzRadialSynthesis.petzSpinorState_sq_eq_softmaxWeight]

/-- **Exact Identity of the Majorana–Souriau Thermofield Double and the $\tau = 1/2$ KMS Petz Spinor**:
Under the energy-to-logit correspondence $E_j = -\ell_j$, the Majorana–Souriau thermofield double
amplitude `tfdRealAmplitude (fun j => -logits j) β i` is identically equal to the $\tau = 1/2$
Wick-rotated KMS strip half-density `petzSpinorState logits β i`. -/
theorem tfdRealAmplitude_neg_eq_petzSpinorState
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) (i : ι) :
    MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β i =
      LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i := by
  have htfd_nonneg :
      0 ≤ MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β i :=
    tfdRealAmplitude_nonneg (fun j => -logits j) β i
  have hpetz_nonneg :
      0 ≤ LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i :=
    Real.sqrt_nonneg _
  calc
    MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β i =
        Real.sqrt ((MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
          (fun j => -logits j) β i) ^ 2) :=
      (Real.sqrt_sq htfd_nonneg).symm
    _ = Real.sqrt ((LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i) ^ 2) := by
      rw [tfdRealAmplitude_neg_sq_eq_petzSpinorState_sq logits β i]
    _ = LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i :=
      Real.sqrt_sq hpetz_nonneg

/-- **Thermofield Double Unit-Sphere Normalization under Negative-Logit Energy**:
The Majorana–Souriau thermofield double state `tfdRealAmplitude (fun j => -logits j) β` has unit
Euclidean norm squared on the token state space. -/
theorem tfdRealAmplitude_neg_unit_sphere
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (logits : ι → ℝ) (β : ℝ) :
    (∑ i : ι, (MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β i) ^ 2) = 1 :=
  MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude_sum_sq_eq_one
    (fun j => -logits j) β

/-!
### Archetype III — Inductive Colimit Continuation ($k \hookrightarrow n$ Tower Stage Invariance of Mestel Toomre $Q$ & Colimit KMS Modular Flow)
-/

/-- Radial cylinder coordinate $r_k = \mathrm{coneRadius}(k) = e^k$ associated with stage $k : \mathbb{N}$
of the Cuntz–UHF $2^k \times 2^k$ matrix inductive tower. -/
noncomputable def towerStageRadius (k : ℕ) : ℝ :=
  RadialQuantizationFiveGradedCylinder.coneRadius (k : ℝ)

/-- At every matrix tower stage $k : \mathbb{N}$, `towerStageRadius k` is strictly positive. -/
theorem towerStageRadius_pos (k : ℕ) :
    0 < towerStageRadius k :=
  Real.exp_pos (k : ℝ)

/-- At every matrix tower stage $k : \mathbb{N}$, `towerStageRadius k` is non-zero. -/
theorem towerStageRadius_ne_zero (k : ℕ) :
    towerStageRadius k ≠ 0 :=
  Real.exp_ne_zero (k : ℝ)

/-- The radial quantization clock `radialTime` at `towerStageRadius k` equals the exact stage
index `(k : ℝ)`. -/
theorem radialTime_towerStageRadius (k : ℕ) :
    RadialQuantizationFiveGradedCylinder.radialTime (towerStageRadius k) = (k : ℝ) :=
  RadialQuantizationFiveGradedCylinder.radialTime_coneRadius (k : ℝ)

/-- Evaluating the logarithmic central monopole potential `logMonopolePotential v_c` at
`towerStageRadius k` yields $v_c^2 k$, linear in the tower stage index $k$. -/
theorem logMonopolePotential_towerStageRadius (v_c : ℝ) (k : ℕ) :
    LinShuKMSPetzRadialSynthesis.logMonopolePotential v_c (towerStageRadius k) =
      v_c ^ 2 * (k : ℝ) :=
  LinShuKMSPetzRadialSynthesis.logMonopolePotential_coneRadius v_c (k : ℝ)

/-- At `towerStageRadius k`, the flat-rotation-curve ($\alpha = 1$) epicyclic frequency squared
scales by the conformal grade `.negTwo` factor $e^{-2k}$. -/
theorem flatRotationCurve_epicyclicFreqSq_towerStageRadius (Ω₀ : ℝ) (k : ℕ) :
    LinShuKMSPetzRadialSynthesis.powerLawEpicyclicFreqSq Ω₀ 1 (towerStageRadius k) =
      2 * Ω₀ ^ 2 * RadialQuantizationFiveGradedCylinder.gradeTimeScale .negTwo (k : ℝ) :=
  LinShuKMSPetzRadialSynthesis.flatRotationCurve_epicyclicFreqSq_at_coneRadius Ω₀ (k : ℝ)

/-- **Inductive Tower Stage Invariance of the Mestel Disk Toomre Parameter $Q$**:
For any two Cuntz–UHF matrix tower stages $k, n : \mathbb{N}$, non-zero circular sink velocity
$v_{\mathrm{sink}} \ne 0$, and coupling $G \ne 0$, the Mestel disk Toomre stability parameter at
stage $n$ equals the Mestel disk Toomre stability parameter at stage $k$. -/
theorem toomreQ_mestelDisk_towerStage_invariant
    (v_sink c_s G : ℝ) (hv : v_sink ≠ 0) (hG : G ≠ 0) (k n : ℕ) :
    LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 *
        LinShuKMSPetzRadialSynthesis.powerLawOmega v_sink 1 (towerStageRadius n))
      c_s G
      (LinShuKMSPetzRadialSynthesis.mestelSurfaceDensity v_sink G (towerStageRadius n)) =
    LinShuAttentionDensityWave.toomreQ
      (Real.sqrt 2 *
        LinShuKMSPetzRadialSynthesis.powerLawOmega v_sink 1 (towerStageRadius k))
      c_s G
      (LinShuKMSPetzRadialSynthesis.mestelSurfaceDensity v_sink G (towerStageRadius k)) :=
  LinShuKMSPetzRadialSynthesis.toomreQ_mestelDisk_radial_invariance
    v_sink c_s G (towerStageRadius n) (towerStageRadius k) hv hG
    (towerStageRadius_ne_zero n) (towerStageRadius_ne_zero k)

/-- **Universal All-Stage WKBJ Dispersion Positivity on the Inductive Tower**:
Whenever $\sigma_0 > 0$, $G > 0$, and $c_s > \sqrt{\rho_0 \sigma_0^2} / (2\sqrt{2})$, the KMS
softmax Mestel disk has strictly positive Lin–Shu WKBJ dispersion RHS at every matrix tower stage
`towerStageRadius m` ($m : \mathbb{N}$) and every radial wavenumber $k_r \in \mathbb{R}$. -/
theorem kmsSoftmaxSink_mestelDisk_all_towerStages_dispersion_pos
    {n : ℕ} (logits : Fin (n + 1) → ℝ) (β σ₀ c_s G k_r : ℝ) (m : ℕ)
    (hσ₀ : 0 < σ₀) (hG : 0 < G)
    (hc_s : Real.sqrt
      (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
        (AttentionKMSState.softmaxWeight logits β) σ₀) /
      (2 * Real.sqrt 2) < c_s) :
    0 < LinShuAttentionDensityWave.linShuDispersionRHS
      (Real.sqrt 2 *
        LinShuKMSPetzRadialSynthesis.powerLawOmega
          (Real.sqrt
            (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
              (AttentionKMSState.softmaxWeight logits β) σ₀))
          1 (towerStageRadius m))
      G
      (LinShuKMSPetzRadialSynthesis.mestelSurfaceDensity
        (Real.sqrt
          (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
            (AttentionKMSState.softmaxWeight logits β) σ₀))
        G (towerStageRadius m))
      c_s k_r :=
  LinShuKMSPetzRadialSynthesis.kmsSoftmaxSink_mestelDisk_universal_dispersion_pos
    logits β σ₀ c_s G (towerStageRadius m) k_r hσ₀ hG (towerStageRadius_pos m) hc_s

/-- **Colimit KMS Modular Flow Real Readout Equals $\tau = 1/2$ Petz Spinor Expectation Sum**:
For any Cuntz–UHF matrix tower embedding $k \le n$, logit profile `logits : Fin (2 ^ k) → ℝ`,
inverse temperature $\beta$, modular time $t$, and real matrix observable
`A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ`, the real part of the direct-limit expectation of
`rawMap h (modularFlow logits β t (complexifyRealMatrix A))` equals the diagonal sum weighted by
the squared $\tau = 1/2$ KMS Petz spinor state `petzSpinorState logits β`. -/
theorem colimit_modularFlow_real_readout_eq_petzSpinor_sum
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    Complex.re
        (MatrixStageSelectedFunctional.selectedStageColimitFunctional k
          (AttentionStageColimitState.attentionStageDensity k logits β)
          (CuntzMatrixAlgebraicStarColimit.stageInjection n
            (CuntzMatrixAlgebraicStarColimit.rawMap h
              (ColimitAttentionTomitaFlow.modularFlow logits β t
                (AttentionStageColimitState.complexifyRealMatrix A))))) =
      ∑ i : Fin (2 ^ k),
        (LinShuKMSPetzRadialSynthesis.petzSpinorState logits β i) ^ 2 * A i i := by
  rw [ColimitAttentionTomitaFlow.attentionColimitFunctional_rawMap_modularFlow_invariant
      h logits β t (AttentionStageColimitState.complexifyRealMatrix A),
    AttentionStageColimitState.attentionColimitFunctional_real_seed_readout k logits β A,
    Complex.ofReal_re, AttentionKMSState.attentionState_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinShuKMSPetzRadialSynthesis.petzSpinorState_sq_eq_softmaxWeight logits β i]

/-- **Colimit KMS Modular Flow Real Readout Equals Majorana–Souriau Thermofield Double Sum**:
For any Cuntz–UHF matrix tower embedding $k \le n$, logit profile `logits : Fin (2 ^ k) → ℝ`,
inverse temperature $\beta$, modular time $t$, and real matrix observable
`A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ`, the real part of the direct-limit expectation of
`rawMap h (modularFlow logits β t (complexifyRealMatrix A))` equals the diagonal sum weighted by
the squared Majorana–Souriau thermofield double amplitude
`tfdRealAmplitude (fun j => -logits j) β`. -/
theorem colimit_modularFlow_real_readout_eq_tfd_sum
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) :
    Complex.re
        (MatrixStageSelectedFunctional.selectedStageColimitFunctional k
          (AttentionStageColimitState.attentionStageDensity k logits β)
          (CuntzMatrixAlgebraicStarColimit.stageInjection n
            (CuntzMatrixAlgebraicStarColimit.rawMap h
              (ColimitAttentionTomitaFlow.modularFlow logits β t
                (AttentionStageColimitState.complexifyRealMatrix A))))) =
      ∑ i : Fin (2 ^ k),
        (MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
          (fun j => -logits j) β i) ^ 2 * A i i := by
  rw [colimit_modularFlow_real_readout_eq_petzSpinor_sum h logits β t A]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tfdRealAmplitude_neg_sq_eq_petzSpinorState_sq logits β i]

/-- **KMS Sink Circular Orbital Speed as Anchor Petz Spinor Amplitude**:
For $0 \le \sigma_0$, the effective circular orbital speed
$\sqrt{\mathrm{sinkCircularVelSq}(\mathrm{softmaxWeight}(\ell, \beta), \sigma_0)}$ equals the
anchor $\tau = 1/2$ Petz spinor amplitude `petzSpinorState logits β 0` times $\sigma_0$. -/
theorem sqrt_sinkCircularVelSq_eq_petzSpinor_mul
    {m : ℕ} (logits : Fin (m + 1) → ℝ) (β σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀) :
    Real.sqrt
        (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
          (AttentionKMSState.softmaxWeight logits β) σ₀) =
      LinShuKMSPetzRadialSynthesis.petzSpinorState logits β 0 * σ₀ := by
  dsimp [LinShuKMSPetzRadialSynthesis.sinkCircularVelSq,
    LinShuKMSPetzRadialSynthesis.petzSpinorState]
  rw [Real.sqrt_mul (le_of_lt (AttentionKMSState.softmaxWeight_pos logits β 0)),
    Real.sqrt_sq hσ₀]

/-- **KMS Sink Circular Orbital Speed as Anchor Thermofield Double Amplitude**:
For $0 \le \sigma_0$, the effective circular orbital speed
$\sqrt{\mathrm{sinkCircularVelSq}(\mathrm{softmaxWeight}(\ell, \beta), \sigma_0)}$ equals the
anchor Majorana–Souriau thermofield double amplitude
`tfdRealAmplitude (fun j => -logits j) β 0` times $\sigma_0$. -/
theorem sqrt_sinkCircularVelSq_eq_tfd_mul
    {m : ℕ} (logits : Fin (m + 1) → ℝ) (β σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀) :
    Real.sqrt
        (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
          (AttentionKMSState.softmaxWeight logits β) σ₀) =
      MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
        (fun j => -logits j) β 0 * σ₀ := by
  rw [sqrt_sinkCircularVelSq_eq_petzSpinor_mul logits β σ₀ hσ₀,
    tfdRealAmplitude_neg_eq_petzSpinorState logits β 0]

/-- **Mestel Disk Toomre $Q$ at Tower Stage $k$ Expressed via the Anchor TFD Amplitude**:
At any matrix tower stage $k : \mathbb{N}$ with $\sigma_0 > 0$ and $G \ne 0$, the KMS softmax
Mestel disk Toomre stability parameter at `towerStageRadius k` equals
$\frac{2\sqrt{2} c_s}{\psi_{\mathrm{TFD}}(0) \sigma_0}$, inversely proportional to the anchor
thermofield double amplitude and independent of the tower stage $k$. -/
theorem toomreQ_kmsSoftmax_mestelDisk_towerStage_eq_tfd_ratio
    {m : ℕ} (logits : Fin (m + 1) → ℝ) (β σ₀ c_s G : ℝ) (k : ℕ)
    (hσ₀ : 0 < σ₀) (hG : G ≠ 0) :
    LinShuAttentionDensityWave.toomreQ
        (Real.sqrt 2 *
          LinShuKMSPetzRadialSynthesis.powerLawOmega
            (Real.sqrt
              (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
                (AttentionKMSState.softmaxWeight logits β) σ₀))
            1 (towerStageRadius k))
        c_s G
        (LinShuKMSPetzRadialSynthesis.mestelSurfaceDensity
          (Real.sqrt
            (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
              (AttentionKMSState.softmaxWeight logits β) σ₀))
          G (towerStageRadius k)) =
      (2 * Real.sqrt 2 * c_s) /
        (MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
          (fun j => -logits j) β 0 * σ₀) := by
  have hv_pos :
      0 < Real.sqrt
        (LinShuKMSPetzRadialSynthesis.sinkCircularVelSq
          (AttentionKMSState.softmaxWeight logits β) σ₀) :=
    Real.sqrt_pos.mpr
      (mul_pos (AttentionKMSState.softmaxWeight_pos logits β 0) (sq_pos_of_pos hσ₀))
  rw [LinShuKMSPetzRadialSynthesis.toomreQ_mestelDisk_scale_invariant
      _ c_s G (towerStageRadius k) (ne_of_gt hv_pos) hG (towerStageRadius_ne_zero k),
    sqrt_sinkCircularVelSq_eq_tfd_mul logits β σ₀ (le_of_lt hσ₀)]

/-- **Radial-Cylinder-Dilated Para-Kähler Fock CAR Superbracket at the Stage-$k$ Thermofield Double State**:
For any tower stage $k : \mathbb{N}$, logit profile `logits : Fin (2 ^ k) → ℝ`, inverse temperature
$\beta$, and radial cylinder time $t$, when the cross-sheet pairing `g α.1 u.1` equals the sum of
squared Majorana–Souriau thermofield double amplitudes
$\sum_{i \in \mathrm{Fin}(2^k)} \psi_{\mathrm{TFD}}(i)^2$, the odd-odd graded Lie superbracket of
the radial-cylinder-dilated creation and annihilation operators evaluates identically to the unit
endomorphism `1` on `FockExteriorEnvelope K`. -/
theorem dilated_paraKahler_fock_superBracket_at_tfdRealAmplitude_sq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (g : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : V →ₗ[ℝ] V) (t : ℝ)
    (u : SuperGrassmannianProjectorEnvelope.primalSheet K)
    (α : SuperGrassmannianProjectorEnvelope.covectorVacuumSheet K)
    (k : ℕ) (logits : Fin (2 ^ k) → ℝ) (β : ℝ)
    (h_pair : g α.1 u.1 =
      ∑ i : Fin (2 ^ k),
        (MajoranaSouriauMetriplecticLoxodromic.tfdRealAmplitude
          (fun j => -logits j) β i) ^ 2) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (RadialQuantizationFiveGradedCylinder.dilatedCreateEnd K t u)
        (RadialQuantizationFiveGradedCylinder.dilatedAnnihilateEnd g K t α) =
      (1 : Module.End ℝ (SuperGrassmannianProjectorEnvelope.FockExteriorEnvelope K)) := by
  rw [RadialQuantizationFiveGradedCylinder.superBracket_dilatedCreate_dilatedAnnihilate_invariant,
    ParaKahlerGradedFockCAR.superBracket_create_annihilate g K u α,
    h_pair, tfdRealAmplitude_neg_unit_sphere logits β, one_smul]

/-!
### Archetype IV — Jordan–Wigner / CAR $\longleftrightarrow$ $\mathrm{UHF}(2^\infty)$ Block-Diagonal Colimit & Superbracket Bridge
-/

/-- Single-mode fermionic creation matrix $c^\dagger = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix}$
on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def fockCreateMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 1, 0]

/-- Single-mode fermionic annihilation matrix $c = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}$
on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def fockAnnihilateMat : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 0, 0]

/-- Single-mode Jordan–Wigner fermion-parity grading matrix
$Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$ on `Matrix (Fin 2) (Fin 2) ℝ`. -/
def jordanWignerParity : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1]

/-- Self-adjoint Majorana mode $\gamma_+ = c^\dagger + c = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def majoranaPlus : Matrix (Fin 2) (Fin 2) ℝ :=
  fockCreateMat + fockAnnihilateMat

/-- Skew-adjoint Majorana mode $\gamma_- = c^\dagger - c = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$. -/
def majoranaMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  fockCreateMat - fockAnnihilateMat

/-- Pauli exclusion nilpotency of the single-mode creation matrix: $(c^\dagger)^2 = 0$. -/
theorem fockCreateMat_sq :
    fockCreateMat * fockCreateMat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fockCreateMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Pauli exclusion nilpotency of the single-mode annihilation matrix: $c^2 = 0$. -/
theorem fockAnnihilateMat_sq :
    fockAnnihilateMat * fockAnnihilateMat = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fockAnnihilateMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Involution of the Jordan–Wigner parity grading matrix: $Z^2 = I_2$. -/
theorem jordanWignerParity_sq :
    jordanWignerParity * jordanWignerParity = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanWignerParity, Matrix.mul_apply, Fin.sum_univ_two]

/-- Anticommutation of the Jordan–Wigner parity matrix with `fockCreateMat`:
$Z c^\dagger + c^\dagger Z = 0$. -/
theorem jordanWignerParity_anticomm_create :
    jordanWignerParity * fockCreateMat + fockCreateMat * jordanWignerParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanWignerParity, fockCreateMat]

/-- Anticommutation of the Jordan–Wigner parity matrix with `fockAnnihilateMat`:
$Z c + c Z = 0$. -/
theorem jordanWignerParity_anticomm_annihilate :
    jordanWignerParity * fockAnnihilateMat + fockAnnihilateMat * jordanWignerParity = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanWignerParity, fockAnnihilateMat]

/-- Fundamental single-mode CAR anticommutator: $c^\dagger c + c c^\dagger = I_2$. -/
theorem fockCreate_fockAnnihilate_anticomm :
    fockCreateMat * fockAnnihilateMat + fockAnnihilateMat * fockCreateMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fockCreateMat, fockAnnihilateMat]

/-- **Single-Mode Para-Kähler CAR Odd-Odd Superbracket Identity**:
For any primal mode amplitude $u \in \mathbb{R}$ and covector amplitude $\alpha \in \mathbb{R}$,
the odd-odd graded Lie superbracket `[u • c†, α • c]` evaluates to $(\alpha u) \cdot I_2$. -/
theorem oddSuperBracket_create_annihilate (u α : ℝ) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (u • fockCreateMat) (α • fockAnnihilateMat) =
      (α * u) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [ChakravalaGA.superBracket_fermionic, smul_mul_smul_comm, smul_mul_smul_comm,
    mul_comm u α, ← smul_add, fockCreate_fockAnnihilate_anticomm]

/-- The even Majorana generator squares to $+I_2$: $\gamma_+^2 = I_2$. -/
theorem majoranaPlus_sq :
    majoranaPlus * majoranaPlus = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majoranaPlus, fockCreateMat, fockAnnihilateMat,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The skew Majorana generator squares to $-I_2$: $\gamma_-^2 = -I_2$. -/
theorem majoranaMinus_sq :
    majoranaMinus * majoranaMinus = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majoranaMinus, fockCreateMat, fockAnnihilateMat,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Orthogonal Majorana modes anticommute under the odd-odd graded Lie superbracket:
`[γ_+, γ_-] = 0`. -/
theorem majorana_oddSuperBracket_zero :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd majoranaPlus majoranaMinus = 0 := by
  rw [ChakravalaGA.superBracket_fermionic]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [majoranaPlus, majoranaMinus, fockCreateMat, fockAnnihilateMat]

/-- Block-diagonal $\mathrm{UHF}(2^\infty)$ step embedding $A \mapsto A \otimes I_2 = \mathrm{diag}(A, A)$
mapping `Matrix m m ℝ` into `Matrix (m ⊕ m) (m ⊕ m) ℝ`. -/
def uhfColimitEmbedStep {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) : Matrix (m ⊕ m) (m ⊕ m) ℝ :=
  Matrix.fromBlocks A 0 0 A

/-- `uhfColimitEmbedStep` preserves the identity matrix. -/
theorem uhfColimitEmbedStep_one {m : Type*} [Fintype m] [DecidableEq m] :
    uhfColimitEmbedStep (1 : Matrix m m ℝ) = 1 :=
  Matrix.fromBlocks_one

/-- `uhfColimitEmbedStep` is additive. -/
theorem uhfColimitEmbedStep_add {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℝ) :
    uhfColimitEmbedStep (A + B) = uhfColimitEmbedStep A + uhfColimitEmbedStep B := by
  dsimp [uhfColimitEmbedStep]
  rw [Matrix.fromBlocks_add, add_zero]

/-- `uhfColimitEmbedStep` commutes with scalar multiplication. -/
theorem uhfColimitEmbedStep_smul {m : Type*} [Fintype m] [DecidableEq m]
    (c : ℝ) (A : Matrix m m ℝ) :
    uhfColimitEmbedStep (c • A) = c • uhfColimitEmbedStep A := by
  dsimp [uhfColimitEmbedStep]
  rw [Matrix.fromBlocks_smul, smul_zero]

/-- `uhfColimitEmbedStep` is multiplicative. -/
theorem uhfColimitEmbedStep_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℝ) :
    uhfColimitEmbedStep (A * B) = uhfColimitEmbedStep A * uhfColimitEmbedStep B := by
  dsimp [uhfColimitEmbedStep]
  simp [Matrix.fromBlocks_multiply]

/-- **UHF Block-Diagonal Step Preservation of the Fermionic Odd-Odd Superbracket**:
`uhfColimitEmbedStep` commutes with `ChakravalaGA.superBracket (R := ℝ) .odd .odd`. -/
theorem uhfColimitEmbedStep_oddSuperBracket {m : Type*} [Fintype m] [DecidableEq m]
    (A B : Matrix m m ℝ) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (uhfColimitEmbedStep A) (uhfColimitEmbedStep B) =
      uhfColimitEmbedStep (ChakravalaGA.superBracket (R := ℝ) .odd .odd A B) := by
  rw [ChakravalaGA.superBracket_fermionic, ChakravalaGA.superBracket_fermionic,
    uhfColimitEmbedStep_add, uhfColimitEmbedStep_mul, uhfColimitEmbedStep_mul]

/-- **UHF Colimit Step Preservation of the Para-Kähler CAR Metric**:
Embedding the single-mode creation and annihilation matrices into the next dyadic block stage
via `uhfColimitEmbedStep` preserves the exact CAR superbracket identity
`[Φ(u c†), Φ(α c)] = (α u) • 1`. -/
theorem uhfColimitEmbedStep_preserves_car_metric (u α : ℝ) :
    ChakravalaGA.superBracket (R := ℝ) .odd .odd
        (uhfColimitEmbedStep (u • fockCreateMat))
        (uhfColimitEmbedStep (α • fockAnnihilateMat)) =
      (α * u) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) := by
  rw [uhfColimitEmbedStep_oddSuperBracket, oddSuperBracket_create_annihilate,
    uhfColimitEmbedStep_smul, uhfColimitEmbedStep_one]

/-- **Intertwining of Tomita Modular Conjugation with the UHF Step Embedding**:
Conjugating by `uhfColimitEmbedStep U` and `uhfColimitEmbedStep U_inv` at stage $m \oplus m$
equals the UHF step embedding of the stage-$m$ modular conjugation `U * A * U_inv`. -/
theorem uhfColimitEmbedStep_tomitaModular_comm {m : Type*} [Fintype m] [DecidableEq m]
    (U U_inv A : Matrix m m ℝ) :
    uhfColimitEmbedStep U * uhfColimitEmbedStep A * uhfColimitEmbedStep U_inv =
      uhfColimitEmbedStep (U * A * U_inv) := by
  rw [← uhfColimitEmbedStep_mul, ← uhfColimitEmbedStep_mul]

/-- **Canonical Cuntz–UHF Tower Transition Homomorphism Preserves the Odd-Odd Superbracket**:
For any tower embedding $k \le n$, the canonical $*$-algebra transition map
`CuntzMatrixAlgebraicStarColimit.rawMap h` commutes with the fermionic superbracket
`ChakravalaGA.superBracket (R := ℂ) .odd .odd`. -/
theorem cuntzColimit_rawMap_oddSuperBracket
    {k n : ℕ} (h : k ≤ n) (A B : CuntzMatrixTowerInstantiation.MatrixStage k) :
    ChakravalaGA.superBracket (R := ℂ) .odd .odd
        (CuntzMatrixAlgebraicStarColimit.rawMap h A)
        (CuntzMatrixAlgebraicStarColimit.rawMap h B) =
      CuntzMatrixAlgebraicStarColimit.rawMap h
        (ChakravalaGA.superBracket (R := ℂ) .odd .odd A B) := by
  rw [ChakravalaGA.superBracket_fermionic, ChakravalaGA.superBracket_fermionic,
    map_add, map_mul, map_mul]

/-- Additivity of `ColimitAttentionTomitaFlow.modularFlow` in the matrix observable argument. -/
theorem modularFlow_add_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A B : Matrix ι ι ℂ) :
    ColimitAttentionTomitaFlow.modularFlow logits β t (A + B) =
      ColimitAttentionTomitaFlow.modularFlow logits β t A +
        ColimitAttentionTomitaFlow.modularFlow logits β t B := by
  dsimp [ColimitAttentionTomitaFlow.modularFlow]
  rw [Matrix.mul_add, Matrix.add_mul]

/-- **Tomita Modular Flow Preserves the Fermionic Odd-Odd Superbracket**:
At any finite stage $\iota$, the 1-parameter KMS modular automorphism group
`ColimitAttentionTomitaFlow.modularFlow logits β t` is a graded Lie superbracket automorphism
for `ChakravalaGA.superBracket (R := ℂ) .odd .odd`. -/
theorem modularFlow_oddSuperBracket {ι : Type*} [Fintype ι] [DecidableEq ι]
    (logits : ι → ℝ) (β t : ℝ) (A B : Matrix ι ι ℂ) :
    ColimitAttentionTomitaFlow.modularFlow logits β t
        (ChakravalaGA.superBracket (R := ℂ) .odd .odd A B) =
      ChakravalaGA.superBracket (R := ℂ) .odd .odd
        (ColimitAttentionTomitaFlow.modularFlow logits β t A)
        (ColimitAttentionTomitaFlow.modularFlow logits β t B) := by
  rw [ChakravalaGA.superBracket_fermionic, ChakravalaGA.superBracket_fermionic,
    modularFlow_add_matrix, ColimitAttentionTomitaFlow.modularFlow_mul,
    ColimitAttentionTomitaFlow.modularFlow_mul]

/-- **Joint Cuntz–UHF Tower Transition & KMS Modular Flow Superbracket Homomorphism**:
For any Cuntz–UHF tower embedding $k \le n$, evolving the stage-$k$ fermionic superbracket
`[A, B]` by `modularFlow logits β t` and pushing forward to stage $n$ via `rawMap h` equals the
stage-$n$ fermionic superbracket of the pushed-forward modular-evolved observables. -/
theorem cuntzColimit_rawMap_modularFlow_oddSuperBracket
    {k n : ℕ} (h : k ≤ n) (logits : Fin (2 ^ k) → ℝ) (β t : ℝ)
    (A B : CuntzMatrixTowerInstantiation.MatrixStage k) :
    CuntzMatrixAlgebraicStarColimit.rawMap h
        (ColimitAttentionTomitaFlow.modularFlow logits β t
          (ChakravalaGA.superBracket (R := ℂ) .odd .odd A B)) =
      ChakravalaGA.superBracket (R := ℂ) .odd .odd
        (CuntzMatrixAlgebraicStarColimit.rawMap h
          (ColimitAttentionTomitaFlow.modularFlow logits β t A))
        (CuntzMatrixAlgebraicStarColimit.rawMap h
          (ColimitAttentionTomitaFlow.modularFlow logits β t B)) := by
  rw [modularFlow_oddSuperBracket, cuntzColimit_rawMap_oddSuperBracket]

end InfoGeometry.QuantumContext.LinShuMajoranaColimitCapstone

end
