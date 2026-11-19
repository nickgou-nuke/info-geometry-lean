/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.MannheimCOWAndSpinorPrecession
import InfoGeometry.Optics.MannheimDoubleSlitSpacetimeCoherence
import InfoGeometry.Conformal.MannheimConformalLuminosityHorizon
import InfoGeometry.Conformal.MannheimCriticalScalingAndHiggsWidth
import InfoGeometry.Synthesis.MannheimDoubledMinkowskiYangMillsBridge
import InfoGeometry.Meta.Trust

/-!
# End-to-End Verification Suite for Philip Mannheim Part 2 Formalization & Dual-Lane Bridge

Opaque-box Tier 1–4 verification suite covering all features F1–F13 (requirements R1–R5):
- **F1–F3 (R1)**: Colella–Overhauser–Werner (COW 1975) gravitational action & phase shift,
  quantum equivalence principle via de Broglie / Compton wavelengths, and Werner–Bernstein
  $4\pi$ $SU(2)$ spinor precession (`MannheimCOWAndSpinorPrecession`).
- **F4–F5 (R2)**: Double-slit equal-emission propagation phase cancellation, earlier-emission
  source phase restoration, finite coherence cutoff, and unitary interferometer / Bloch
  bridge (`MannheimDoubleSlitSpacetimeCoherence`).
- **F6–F8 (R3)**: Closed-form conformal luminosity distance $d_L(z; H_0, q_0)$ for
  $q_0 \in (-1, 0)$, Taylor derivatives $d_L'(0)$ and $d_L''(0)$, and horizon-free conformal
  cosmology vs bounded Einstein horizons (`MannheimConformalLuminosityHorizon`).
- **F9–F10 (R4)**: Johnson–Baker–Willey / Mannheim anomalous dimension $\gamma_{\bar\psi\psi}$
  potential trichotomy ($\gamma \in (-1, 0), -1, -2$) and above-threshold dynamical Higgs
  positive decay width vs zero elementary Higgs width (`MannheimCriticalScalingAndHiggsWidth`).
- **F11–F13 (R5)**: Dual-lane `src/` mirrors and typed scale–phase unification bridge across
  Doubled-Minkowski Layers 0–3 (`MannheimDoubledMinkowskiYangMillsBridge`), including
  `circularEvenOmega` vs `circularGradedOmega` separation, `collectHardEvidenceBatch`, and
  `#print axioms` checks.
-/

set_option autoImplicit false

noncomputable section

open Lean Elab Command Filter _root_.Topology MeasureTheory Set
open InfoGeometry.Meta
open InfoGeometry.Quantum.PauliSoldering (σ0 σ1 σ2 σ3)
open InfoGeometry.Canonical.ZitterbewegungMassEmergence (comptonFrequency)
open InfoGeometry.Quantum.MannheimCOWAndSpinorPrecession
open InfoGeometry.Physics.PenroseEikonalTwistorRay (IsMinkowskiNull minkowskiNorm pauliSoldering)
open InfoGeometry.Conformal.MannheimWeylKazanasCosmology
open InfoGeometry.Conformal.MannheimOpenDebtConstructiveClosure
  (njlDressedInvPropagatorS njlInvPropagatorS njlInvPropagatorP njlPseudoscalarPolarization)
open InfoGeometry.Algebra.ChiralFluidNLSLaxAndDynamicalVacuumMass
  (dynamicalDoubleWell renormalizedFermionPotential)
open InfoGeometry.Krein.BenderMannheimPTPaisUhlenbeckResonance
  (conjPoleLorentzC bwResonanceSq breitWignerPhase)
open InfoGeometry.Synthesis.MannheimTwistorBlochWavefrontEpistemicSynthesis
open InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
  (quantumUmegakiGibbs coherenceRelEntropy blochZ blochNormSq)
open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants (bregmanPhi meanSpin)
open InfoGeometry.Optics.MannheimDoubleSlitSpacetimeCoherence
open InfoGeometry.Conformal.MannheimConformalLuminosityHorizon
open InfoGeometry.Conformal.MannheimCriticalScalingAndHiggsWidth
open InfoGeometry.Lie
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (frame coordinateEquiv coordinateEquiv_apply_frame)
open InfoGeometry.Lie.SplitOctonionEllCrossChannel (uPlus uMinus)
open InfoGeometry.Lie.SplitOctonionEllPolarization (rootPlus rootMinus)
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
  (wittNorm symmSection antiSection)
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge (pauliSolder2x2)
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame (frameBasis)
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein (chiralKreinForm)
open InfoGeometry.OperatorAlgebra.PeirceSpine (genJ genV evenGrade)
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge (peirceGradingDeriv)
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
  (matrixExteriorDerivative matrixTraceForm)
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge (curvatureFromConnection)
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge (covariantDerivative)
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
  (IsHomogeneousExteriorDegree MatrixIsHomogeneous homogeneous_one_iff_exists_generator)
open InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills
  (extBasisOneForm blade2Coeff blade2Coeff_eval)
open InfoGeometry.Synthesis.MannheimDoubledMinkowskiYangMillsBridge
open scoped Matrix MatrixOrder ComplexOrder BigOperators Interval

namespace InfoGeometry.Synthesis.MannheimPart2E2ETest

/-! ## Noncommutativity Regression Witnesses (T16 Matrix Carriers) -/

/-- T16 noncommutativity regression for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2c_noncomm_regression :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  pauli_mat2_noncomm_exists

/-- T16 noncommutativity regression for `Matrix (Fin 4) (Fin 4) ℂ`. -/
theorem mat4c_noncomm_regression :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A :=
  mannheim_circularConnection_mat4C_noncomm_witness

/-- T16 noncommutativity regression for `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem mat2r_noncomm_regression :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  conformal_luminosity_mat2_noncomm_witness

/-- T16 noncommutativity regression for `Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))`. -/
theorem mat4_ext_noncomm_regression :
    ∃ A B : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A :=
  mannheim_mat4_exterior_noncomm_witness

/-! ## Tier 1: Happy-Path Concrete & Symbolic Contract Tests (F1–F13, 65 Cases) -/

/-! ### F1: COW 1975 Gravitational Action & Phase Shift (5 Tier 1 Cases) -/

/-- T1-F1-01: Concrete square-loop gravitational action difference evaluation. -/
theorem t1_f1_01_concrete_square_action :
    cowActionDiff 2 10 3 3 5 = -36 ∧ cowSquareActionDiff 2 10 3 5 = -36 := by
  rw [cowSquareActionDiff_eq]
  unfold cowSquareActionDiff
  norm_num

/-- T1-F1-02: Concrete COW quantum phase shift evaluation. -/
theorem t1_f1_02_concrete_phase_shift :
    cowPhaseShift 2 10 3 (1 / 2) 5 = -72 := by
  rw [cowPhaseShift_eq]
  norm_num

/-- T1-F1-03: Symbolic equivalence between rectangular `L = H` and square COW action difference. -/
theorem t1_f1_03_rect_to_square_symbolic (m_g g H v : ℝ) :
    cowActionDiff m_g g H H v = cowSquareActionDiff m_g g H v :=
  cowSquareActionDiff_eq m_g g H v

/-- T1-F1-04: Classical free-fall acceleration is mass-independent while COW phase separates masses. -/
theorem t1_f1_04_classical_vs_cow_concrete_masses :
    classicalFreeFallAccel 1 1 (98 / 10) = classicalFreeFallAccel 3 3 (98 / 10) ∧
    cowSquareActionDiff 1 (98 / 10) 2 7 ≠ cowSquareActionDiff 3 (98 / 10) 2 7 ∧
    cowPhaseShift 1 (98 / 10) 2 1 7 ≠ cowPhaseShift 3 (98 / 10) 2 1 7 :=
  classical_free_fall_mass_independent_vs_cow_mass_dependent 1 3 (98 / 10) 2 7 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- T1-F1-05: Concrete COW phase shift expressed via Zitterbewegung Compton frequency. -/
theorem t1_f1_05_cow_compton_bridge_concrete :
    cowPhaseShift 2 10 3 (1 / 2) 5 =
      -(comptonFrequency 2 3 (1 / 2) * 10 * 3 ^ 2) / (2 * 3 ^ 2 * 5) :=
  cowPhaseShift_eq_comptonFrequency 2 10 3 (1 / 2) 5 3 (by norm_num) (by norm_num)

/-! ### F2: Quantum Equivalence Principle via de Broglie Wavelength (5 Tier 1 Cases) -/

/-- T1-F2-01: Concrete de Broglie wavelength evaluation. -/
theorem t1_f2_01_concrete_deBroglie_eval :
    deBroglieWavelength 2 4 5 = 1 / 10 := by
  unfold deBroglieWavelength
  norm_num

/-- T1-F2-02: Symbolic quantum equivalence `λ_I = λ_G ↔ m_I = m_g`. -/
theorem t1_f2_02_deBroglie_iff_symbolic (hbar m_I m_g v : ℝ)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0) :
    deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔ m_I = m_g :=
  quantum_equivalence_deBroglie_iff hbar m_I m_g v hhbar hv

/-- T1-F2-03: Concrete de Broglie wavelength and Compton frequency product invariant. -/
theorem t1_f2_03_deBroglie_compton_product :
    deBroglieWavelength 3 2 5 * comptonFrequency 2 7 3 = 98 / 5 := by
  rw [deBroglieWavelength_mul_comptonFrequency 3 2 5 7 (by norm_num) (by norm_num)]
  norm_num

/-- T1-F2-04: Symbolic 3-way equivalence of de Broglie wavelength, Compton frequency, and mass equality. -/
theorem t1_f2_04_tri_equivalence_symbolic (hbar m_I m_g v c : ℝ)
    (hhbar : hbar ≠ 0) (hv : v ≠ 0) (hc : c ≠ 0) :
    (deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔ m_I = m_g) ∧
    (comptonFrequency m_I c hbar = comptonFrequency m_g c hbar ↔ m_I = m_g) ∧
    (deBroglieWavelength hbar m_I v = deBroglieWavelength hbar m_g v ↔
      comptonFrequency m_I c hbar = comptonFrequency m_g c hbar) :=
  quantum_equivalence_deBroglie_compton_iff hbar m_I m_g v c hhbar hv hc

/-- T1-F2-05: Distinct inertial/gravitational masses yield distinct wavelengths and Compton frequencies. -/
theorem t1_f2_05_distinct_masses_separate_wavelength_and_compton :
    deBroglieWavelength 1 2 4 ≠ deBroglieWavelength 1 5 4 ∧
    comptonFrequency 2 3 1 ≠ comptonFrequency 5 3 1 := by
  have h := quantum_equivalence_deBroglie_compton_iff 1 2 5 4 3
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · intro heq
    have hm : (2 : ℝ) = 5 := h.1.mp heq
    norm_num at hm
  · intro heq
    have hm : (2 : ℝ) = 5 := h.2.1.mp heq
    norm_num at hm

/-! ### F3: Werner–Bernstein $4\pi$ Spinor Rotation (5 Tier 1 Cases) -/

/-- T1-F3-01: Euler formula on the z-axis at `θ = π` gives `-i σ₃`. -/
theorem t1_f3_01_euler_z_axis_pi :
    let e3 : Fin 3 → ℝ := ![0, 0, 1]
    IsUnitAxis e3 ∧ spinHalfSU2Rot e3 Real.pi = -Complex.I • σ3 := by
  intro e3
  have hn : IsUnitAxis e3 := by
    unfold IsUnitAxis
    simp [e3]
  refine ⟨hn, ?_⟩
  rw [spinHalfSU2Rot_euler hn Real.pi]
  simp only [Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul, zero_sub,
    Real.sin_pi_div_two, Complex.ofReal_one, mul_one]
  have hp : pauliDir e3 = σ3 := by
    unfold pauliDir
    simp [e3]
  rw [hp, neg_smul]

/-- T1-F3-02: Arbitrary oblique unit axis rotation belongs to `SU(2)` with unit determinant. -/
theorem t1_f3_02_su2_membership_arbitrary_axis :
    let n : Fin 3 → ℝ := ![3 / 5, 4 / 5, 0]
    spinHalfSU2Rot n (7 / 3) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    (spinHalfSU2Rot n (7 / 3)).det = 1 := by
  intro n
  have hn : IsUnitAxis n := by
    unfold IsUnitAxis
    simp [n]
    norm_num
  have h := spinHalfSU2Rot_unitary_and_det_one hn (7 / 3)
  exact ⟨h.2.2.2, h.2.2.1⟩

/-- T1-F3-03: $2\pi$ spinor precession yields `-I₂ ≠ I₂`. -/
theorem t1_f3_03_two_pi_sign_flip :
    let e1 : Fin 3 → ℝ := ![1, 0, 0]
    spinHalfSU2Rot e1 (2 * Real.pi) = -1 ∧ spinHalfSU2Rot e1 (2 * Real.pi) ≠ 1 := by
  intro e1
  have hn : IsUnitAxis e1 := by
    unfold IsUnitAxis
    simp [e1]
  exact spinHalfSU2Rot_two_pi hn

/-- T1-F3-04: $4\pi$ spinor precession restores the identity `+I₂`. -/
theorem t1_f3_04_four_pi_restoration :
    let e2 : Fin 3 → ℝ := ![0, 1, 0]
    spinHalfSU2Rot e2 (4 * Real.pi) = 1 := by
  intro e2
  have hn : IsUnitAxis e2 := by
    unfold IsUnitAxis
    simp [e2]
  exact spinHalfSU2Rot_four_pi hn

/-- T1-F3-05: Group composition law along a fixed unit axis and Pauli T16 noncommutativity. -/
theorem t1_f3_05_group_composition_and_pauli_T16 :
    let e3 : Fin 3 → ℝ := ![0, 0, 1]
    spinHalfSU2Rot e3 (Real.pi / 3 + 2 * Real.pi / 3) =
      spinHalfSU2Rot e3 (Real.pi / 3) * spinHalfSU2Rot e3 (2 * Real.pi / 3) ∧
    σ1 * σ2 ≠ σ2 * σ1 :=
  ⟨spinHalfSU2Rot_add ![0, 0, 1] (Real.pi / 3) (2 * Real.pi / 3), pauli_noncomm_witness⟩

/-! ### F4: Equal-Emission Propagation Phase Cancellation (5 Tier 1 Cases) -/

/-- T1-F4-01: Concrete equal-emission propagation phase cancellation `k ΔL - ω Δt = 0`. -/
theorem t1_f4_01_concrete_cancellation :
    propPhaseDiff 2 6 12 4 = 0 ∧
    Complex.exp (Complex.I * (propPhaseDiff 2 6 12 4 : ℂ)) = 1 := by
  have h := equal_emission_phase_cancellation 3 2 6 12 4 (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1⟩

/-- T1-F4-02: Slit ray displacement lies on the Minkowski null cone and Pauli soldering has zero det. -/
theorem t1_f4_02_null_ray_and_pauli_det :
    IsMinkowskiNull (slitRayDisplacement 3 4 12) ∧
    (pauliSoldering (slitRayDisplacement 3 4 12)).det = 0 := by
  have h := equal_emission_phase_cancellation 3 2 6 12 4 (by norm_num) (by norm_num)
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- T1-F4-03: Wave four-vector satisfies the Minkowski null dispersion relation. -/
theorem t1_f4_03_wave_four_vector_null :
    IsMinkowskiNull (waveFourVector 3 6 2) := by
  have h := equal_emission_phase_cancellation 3 2 6 12 4 (by norm_num) (by norm_num)
  exact h.2.2.2.2 (by norm_num)

/-- T1-F4-04: Symbolic propagation phase cancellation for arbitrary `(c, k, Δt)`. -/
theorem t1_f4_04_symbolic_cancellation (c k Δt : ℝ) :
    propPhaseDiff k (c * k) (c * Δt) Δt = 0 :=
  (equal_emission_phase_cancellation c k (c * k) (c * Δt) Δt rfl rfl).1

/-- T1-F4-05: Conformal factor `Ω^2` preserves Minkowski nullity of slit ray displacement. -/
theorem t1_f4_05_conformal_null_rescaling :
    (5 : ℝ) ^ 2 * minkowskiNorm (slitRayDisplacement 3 4 12) = 0 :=
  (doubleSlit_null_ray_and_leaflet_bridge.1 3 2 6 4 12 5 (by norm_num) (by norm_num)
    (by norm_num)).2.2.1

/-! ### F5: Source Phase Restoration & Coherence Cutoff (5 Tier 1 Cases) -/

/-- T1-F5-01: Earlier-emission source phase offset `Δt_src = ΔL / c` restores `k ΔL`. -/
theorem t1_f5_01_source_phase_restoration :
    sourcePhaseDiff 6 4 = 24 ∧ totalSlitPhaseDiff 2 6 12 4 4 = 24 := by
  have h := earlier_emission_phase_restoration 3 2 6 12 4 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩ <;> linarith [h.2.1, h.2.2.1]

/-- T1-F5-02: Inside coherence window `|ΔL| < c τ_coh`, visibility is strictly positive. -/
theorem t1_f5_02_inside_window_positive_visibility :
    IsWithinCoherenceWindow 5 2 ∧
    coherenceVisibility 5 2 = 3 / 5 ∧
    0 < coherenceVisibility 5 2 := by
  have h := coherence_window_and_fringe_cutoff 3 5 6 2 1 2 6 2
    (by norm_num) (by norm_num) (by norm_num)
  have hWin : IsWithinCoherenceWindow 5 2 := h.1.mpr (by norm_num)
  have hPos : 0 < coherenceVisibility 5 2 := h.2.2.1.mpr (by norm_num)
  have hVal : coherenceVisibility 5 2 = 3 / 5 := by
    unfold coherenceVisibility
    norm_num
  exact ⟨hWin, hVal, hPos⟩

/-- T1-F5-03: Outside coherence window `|ΔL| > c τ_coh`, fringes are cut off to `2 I₀`. -/
theorem t1_f5_03_outside_window_fringe_cutoff :
    ¬ IsWithinCoherenceWindow 5 6 ∧
    coherenceVisibility 5 6 = 0 ∧
    twoSlitIntensity 7 5 2 6 18 6 6 = 14 := by
  have h := coherence_window_and_fringe_cutoff 3 5 18 6 7 2 6 6
    (by norm_num) (by norm_num) (by norm_num)
  have hCut := h.2.2.2.1 (by norm_num)
  refine ⟨hCut.1, hCut.2.1, ?_⟩
  linarith [hCut.2.2]

/-- T1-F5-04: Unitary two-slit interferometer operator reproduces cosine interference fringe. -/
theorem t1_f5_04_unitary_interferometer_fringe :
    (twoSlitInterferometerOp (Real.pi / 3))ᴴ * twoSlitInterferometerOp (Real.pi / 3) = 1 ∧
    2 * Complex.normSq ((twoSlitInterferometerOp (Real.pi / 3)) 0 0) = 3 / 2 := by
  refine ⟨(twoSlitInterferometerOp_unitary_and_det_ne_zero (Real.pi / 3)).1, ?_⟩
  rw [twoSlitInterferometerOp_fringe_normSq (Real.pi / 3), Real.cos_pi_div_three]
  norm_num

/-- T1-F5-05: T16 noncommutativity of phase shifter and Hadamard beam splitter. -/
theorem t1_f5_05_doubleSlit_T16_witness :
    slitPhaseMatrix Real.pi * beamSplitterHadamard ≠
      beamSplitterHadamard * slitPhaseMatrix Real.pi ∧
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨slitPhaseMatrix_pi_beamSplitter_ne, doubleSlit_matrix2_noncommutative⟩

/-! ### F6: Closed-Form Conformal Luminosity Distance (5 Tier 1 Cases) -/

/-- T1-F6-01: Concrete conformal radicand evaluation and positivity. -/
theorem t1_f6_01_radicand_concrete :
    conformalRadicand (-1 / 2) 1 = 5 / 8 ∧ 0 < conformalRadicand (-1 / 2) 1 := by
  refine ⟨?_, conformalRadicand_pos ⟨by norm_num, by norm_num⟩ (by norm_num)⟩
  unfold conformalRadicand
  norm_num

/-- T1-F6-02: Luminosity distance vanishes at redshift `z = 0`. -/
theorem t1_f6_02_dL_zero :
    conformalLuminosityDist 3 70 (-1 / 2) 0 = 0 :=
  conformalLuminosityDist_zero 3 70 (-1 / 2)

/-- T1-F6-03: Strictly positive luminosity distance for positive redshift `z = 1`. -/
theorem t1_f6_03_dL_positive_concrete :
    0 < conformalLuminosityDist 3 2 (-1 / 2) 1 :=
  conformalLuminosityDist_pos (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- T1-F6-04: Exact algebraic evaluation of `conformalLuminosityDist` at `q₀ = -1/2, z = 1`. -/
theorem t1_f6_04_dL_exact_algebraic_q_minus_half :
    conformalLuminosityDist 1 1 (-1 / 2) 1 = 8 * (1 - Real.sqrt (5 / 8)) := by
  unfold conformalLuminosityDist conformalRadicand
  norm_num

/-- T1-F6-05: Symbolic positivity across the entire open interval `q₀ ∈ (-1, 0)` and `z > 0`. -/
theorem t1_f6_05_symbolic_Ioo_pos {c H₀ q₀ z : ℝ}
    (hc : 0 < c) (hH : 0 < H₀) (hq : q₀ ∈ Set.Ioo (-1 : ℝ) 0) (hz : 0 < z) :
    0 < conformalLuminosityDist c H₀ q₀ z :=
  conformalLuminosityDist_pos hc hH hq hz

/-! ### F7: Luminosity Distance Taylor Derivatives (5 Tier 1 Cases) -/

/-- T1-F7-01: First derivative at `z = 0` matches Hubble law `c / H₀`. -/
theorem t1_f7_01_deriv1_zero_concrete :
    deriv (conformalLuminosityDist 300 70 (-1 / 2)) 0 = 300 / 70 :=
  (conformalLuminosityDist_deriv1_zero (by norm_num) ⟨by norm_num, by norm_num⟩).1

/-- T1-F7-02: `iteratedDeriv 1` at `z = 0` equals `c / H₀`. -/
theorem t1_f7_02_iteratedDeriv1_zero :
    iteratedDeriv 1 (conformalLuminosityDist 300 70 (-1 / 2)) 0 = 300 / 70 :=
  (conformalLuminosityDist_deriv1_zero (by norm_num) ⟨by norm_num, by norm_num⟩).2

/-- T1-F7-03: Second derivative at `z = 0` equals `(c / H₀) * (1 - q₀)`. -/
theorem t1_f7_03_deriv2_zero_concrete :
    deriv (deriv (conformalLuminosityDist 300 70 (-1 / 2))) 0 = (300 / 70) * (3 / 2) := by
  have h := (conformalLuminosityDist_deriv2_zero (c := 300) (H₀ := 70) (q₀ := -1 / 2)
    (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩).1
  linarith

/-- T1-F7-04: `iteratedDeriv 2` exhibits strict upward acceleration `d_L''(0) > c / H₀`. -/
theorem t1_f7_04_iteratedDeriv2_strict_acceleration :
    iteratedDeriv 2 (conformalLuminosityDist 1 2 (-1 / 3)) 0 = 2 / 3 ∧
    (1 / 2 : ℝ) < (1 / 2) * (1 - (-1 / 3 : ℝ)) := by
  have h := conformalLuminosityDist_deriv2_zero (c := 1) (H₀ := 2) (q₀ := -1 / 3)
    (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  refine ⟨?_, h.2.2⟩
  linarith [h.2.1]

/-- T1-F7-05: Pointwise derivative at `z = 1` matches explicit `conformalLumDistDeriv1`. -/
theorem t1_f7_05_pointwise_deriv_at_z1 :
    deriv (conformalLuminosityDist 1 2 (-1 / 2)) 1 = conformalLumDistDeriv1 1 2 (-1 / 2) 1 :=
  conformal_luminosity_dist_deriv1_eq (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)

/-! ### F8: Horizon-Free Conformal Cosmology & Growth Ratios (5 Tier 1 Cases) -/

/-- T1-F8-01: Closed-form FTC evaluation of the conformal particle horizon. -/
theorem t1_f8_01_conformal_horizon_ftc_eval :
    conformalHorizon 1 1 2 (-1) 1 2 =
      (1 / Real.sqrt 1) *
        (Real.log (Real.tanh (mannheimCosmoRate 1 2 * 2 / 2)) -
         Real.log (Real.tanh (mannheimCosmoRate 1 2 * 1 / 2))) := by
  simpa using (conformalHorizon_eq_and_tendsto_atTop (c := 1) (S₀ := 1) (lam := 2) (k := -1) (t := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 1 (by norm_num)

/-- T1-F8-02: Conformal particle horizon diverges to `+∞` as `t_i → 0⁺` (horizon-free). -/
theorem t1_f8_02_conformal_horizon_divergence :
    Tendsto (fun t_i => conformalHorizon 1 1 2 (-1) t_i 2) (𝓝[>] 0) Filter.atTop :=
  (conformalHorizon_eq_and_tendsto_atTop (c := 1) (S₀ := 1) (lam := 2) (k := -1) (t := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2

/-- T1-F8-03: Standard Einstein radiation-era horizon (`p = 1/2`) remains uniformly bounded. -/
theorem t1_f8_03_einstein_radiation_horizon_bounded :
    einsteinPowerHorizon 1 (1 / 2) (1 / 4) 4 = 3 ∧
    einsteinPowerHorizon 1 (1 / 2) (1 / 4) 4 ≤ 4 := by
  have h := einsteinPowerHorizon_bounded (c := 1) (p := 1 / 2) (t_i := 1 / 4) (t := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hEval : einsteinPowerHorizon 1 (1 / 2) (1 / 4) 4 = 3 := by
    rw [h.1]
    have h4 : (4 : ℝ) ^ (1 - 1 / 2 : ℝ) = 2 := by
      rw [show (1 - 1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
      norm_num
    have hq : (1 / 4 : ℝ) ^ (1 - 1 / 2 : ℝ) = 1 / 2 := by
      rw [show (1 - 1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
      norm_num
    rw [h4, hq]
    norm_num
  exact ⟨hEval, by linarith⟩

/-- T1-F8-04: Conformal `sinh` expansion outpaces linear time ratio and Einstein `√(t₂/t₁)`. -/
theorem t1_f8_04_sinh_outpaces_linear_and_sqrt :
    3 < mannheimScaleFactor 1 2 (-1) 3 / mannheimScaleFactor 1 2 (-1) 1 ∧
    (3 : ℝ) ^ (1 / 2 : ℝ) < 3 := by
  have h := conformal_vs_standard_nucleosynthesis_and_planck_ratios
    (S₀ := 1) (lam := 2) (k := -1) (t₁ := 1) (t₂ := 3) (T₁ := 100) (T₂ := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  refine ⟨?_, ?_⟩
  · simpa using h.1
  · simpa using h.2.1

/-- T1-F8-05: Nucleosynthesis/Planck temperature ratio `R = 1000` separation between conformal and standard time ratios. -/
theorem t1_f8_05_standard_vs_conformal_time_ratio_gap :
    (∀ r_std : ℝ, 0 ≤ r_std → r_std ^ (1 / 2 : ℝ) = 1000 → r_std = 1000 ^ 2) ∧
    (∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
      mannheimScaleFactor 1 2 (-1) t₂ / mannheimScaleFactor 1 2 (-1) t₁ = 1000 →
      t₂ / t₁ < 1000 ∧ t₂ / t₁ < 1000 ^ 2) := by
  refine ⟨fun r_std hr0 hr => ?_, fun t₁ t₂ ht₁ ht₁₂ hmatch => ?_⟩
  · have h := conformal_vs_standard_nucleosynthesis_and_planck_ratios
      (S₀ := 1) (lam := 2) (k := -1) (t₁ := 1) (t₂ := 2) (T₁ := 1000) (T₂ := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
    simpa using h.2.2.2.2.2 r_std hr0 (by simpa using hr)
  · have h := conformal_vs_standard_nucleosynthesis_and_planck_ratios
      (S₀ := 1) (lam := 2) (k := -1) (t₁ := t₁) (t₂ := t₂) (T₁ := 1000) (T₂ := 1)
      (by norm_num) (by norm_num) (by norm_num) ht₁ ht₁₂ (by norm_num) (by norm_num)
    simpa using h.2.2.2.2.1 (by simpa using hmatch)

/-! ### F9: Anomalous Dimension `γ` Critical Potential Trichotomy (5 Tier 1 Cases) -/

/-- T1-F9-01: Marginal four-fermion dimension `2(3 + γ) = 4` holds iff `γ = -1`. -/
theorem t1_f9_01_marginal_scaling_iff :
    dressedBilinearDim (-1) = 2 ∧ fourFermionDim (-1) = 4 := by
  refine ⟨by unfold dressedBilinearDim; norm_num, ?_⟩
  exact anomalous_dim_uv_integrability_trichotomy.1 (-1) |>.mpr rfl

/-- T1-F9-02: UV integral `∫_{1}^{∞} u^{-2} du = 1` and finite cutoff integral evaluation. -/
theorem t1_f9_02_uv_integral_gamma_minus_two :
    (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ)) = 1 ∧
    (∫ u in (1 : ℝ)..4, u ^ (-2 : ℝ)) = 3 / 4 := by
  have h := anomalous_dim_uv_integrability_trichotomy.2.2.2.2
  refine ⟨h.2.1, ?_⟩
  have hcut := h.2.2.2.1 4 (by norm_num)
  linarith [hcut.1]

/-- T1-F9-03: Single-well regime `-1 < γ < 0` yields `SingleWellShape`. -/
theorem t1_f9_03_single_well_gamma_minus_half :
    SingleWellShape (mannheimCriticalPotential (-1 / 2) 2 1 1) :=
  mannheim_anomalous_dimension_potential_trichotomy.1 (-1 / 2) 2 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- T1-F9-04: Marginal regime `γ = -1` yields `DoubleWellShape` with minima `-(M^4/2)` and positive curvature. -/
theorem t1_f9_04_double_well_gamma_minus_one :
    DoubleWellShape 2 (mannheimCriticalPotential (-1) 2 1 1) ∧
    mannheimCriticalPotential (-1) 2 1 1 2 = -8 ∧
    deriv (deriv (mannheimCriticalPotential (-1) 2 1 1)) 2 = 32 := by
  have hDW := (mannheim_anomalous_dimension_potential_trichotomy.2.1 2 1 1 (by norm_num)).1
  refine ⟨hDW, ?_, ?_⟩
  · linarith [hDW.2.2.1]
  · linarith [hDW.2.2.2.2.2.2.2.1]

/-- T1-F9-05: Inverted regime `γ = -2` yields `UpsideDownShape` for arbitrary positive `c₄` and `c_uv = 1`. -/
theorem t1_f9_05_upside_down_gamma_minus_two :
    UpsideDownShape (mannheimCriticalPotential (-2) 2 1 1) ∧
    UpsideDownShape (mannheimCriticalPotential (-2) 2 1 (∫ u : ℝ in Set.Ioi (1 : ℝ), u ^ (-2 : ℝ))) :=
  ⟨mannheim_anomalous_dimension_potential_trichotomy.2.2.1 2 1 1 (by norm_num),
   (mannheim_anomalous_dimension_potential_trichotomy.2.2.2 2 1).2.2⟩

/-! ### F10: Above-Threshold Dynamical Higgs Decay Width vs Elementary Zero (5 Tier 1 Cases) -/

/-- T1-F10-01: Scalar bubble imaginary part is strictly positive above threshold `q² > 4 m²`. -/
theorem t1_f10_01_bubble_im_above_threshold :
    0 < scalarBubbleImPart 1 1 8 :=
  scalarBubbleImPart_threshold_dichotomy.2 1 1 8 (by norm_num) (by norm_num)

/-- T1-F10-02: Dynamical bound-state Higgs (`M_H > 2m`) has strictly positive decay width `Γ_dyn > 0`. -/
theorem t1_f10_02_dynamical_higgs_positive_width :
    ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      (dynamicalHiggsComplexInvProp 1 1 3 1 1 9).im = 3 * Γ_dyn := by
  obtain ⟨Γ_dyn, hΓ, _, _, hIm, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Γ_dyn, hΓ, by simpa [show (3 : ℝ) ^ 2 = 9 by norm_num] using hIm⟩

/-- T1-F10-03: Complex second-sheet pole `s_pole.im < 0` and positive Wigner phase derivative. -/
theorem t1_f10_03_pole_and_wigner_time_delay :
    ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      (((3 ^ 2 : ℝ) : ℂ) - Complex.I * ((3 * Γ_dyn : ℝ) : ℂ)).im < 0 ∧
      0 < deriv (breitWignerPhase (3 ^ 2) (3 * Γ_dyn)) 9 := by
  obtain ⟨Γ_dyn, hΓ, _, _, _, _, hPole, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Γ_dyn, hΓ, hPole.1, (hPole.2.2.2 9).2.2.2⟩

/-- T1-F10-04: NJL dressed inverse scalar propagator vanishes at `q² = M_H²`. -/
theorem t1_f10_04_njl_dressed_real_part_zero_at_MH :
    njlDressedInvPropagatorS 1 1 2 1 (4 * 1 ^ 2 - 3 ^ 2) (3 ^ 2) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, hNJL, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (hNJL 1 2 (3 ^ 2) (by norm_num) (by norm_num)).2.1.mpr rfl

/-- T1-F10-05: Elementary tree-level Higgs propagator has zero imaginary part everywhere. -/
theorem t1_f10_05_elementary_higgs_zero_width :
    (elementaryHiggsInvProp 3 9).im = 0 ∧
    elementaryHiggsInvProp 3 9 = 0 ∧
    (elementaryHiggsInvProp 3 10).im = 0 ∧
    elementaryHiggsInvProp 3 10 ≠ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hElem, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨(hElem 9).1, (hElem 9).2.mpr (by norm_num),
    (hElem 10).1, fun hz => by have := (hElem 10).2.mp hz; norm_num at this⟩

/-! ### F11: Dual-Lane `src/` Mirrors & Layer 0 Scale–Phase / Weyl–Bloch Invariance (5 Tier 1 Cases) -/

/-- T1-F11-01: Combined `4×4` Mannheim conformal-plus-chiral-gauge matrix group law and norm scaling. -/
theorem t1_f11_01_chiral_gauge_mat4_group_law :
    mannheimChiralGaugeMat4 (0.7 + (-0.3)) (1.1 + 0.5) =
      mannheimChiralGaugeMat4 0.7 1.1 * mannheimChiralGaugeMat4 (-0.3) 0.5 ∧
    (mannheimChiralGaugeMat4 0.7 1.1)ᴴ * mannheimChiralGaugeMat4 0.7 1.1 =
      (Real.exp (2 * 0.7) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) :=
  ⟨mannheimChiralGaugeMat4_add 0.7 1.1 (-0.3) 0.5, mannheimChiralGaugeMat4_conjTranspose_mul 0.7 1.1⟩

/-- T1-F11-02: Witt–Krein conformal scaling and Pauli soldering determinant rescaling by `exp(2β)`. -/
theorem t1_f11_02_witt_krein_pauli_conformal_scaling :
    let x := coordinateEquiv (uPlus + uMinus)
    let r := ‖scaleGaugeMultiplier 0.4 1.3‖
    wittNorm x = 1 ∧
    r = Real.exp 0.4 ∧
    wittNorm (r • x) = Real.exp (2 * 0.4) * wittNorm x ∧
    (pauliSolder2x2 (r * 5) (r * 1) (r * 2) (r * 2)).det -
        (pauliSolder2x2 (r * 3) (r * 1) (r * 0) (r * 1)).det =
      (Real.exp (2 * 0.4) : ℂ) *
        ((pauliSolder2x2 5 1 2 2).det - (pauliSolder2x2 3 1 0 1).det) := by
  have hx : coordinateEquiv (uPlus + uMinus) = Pi.single 0 1 + Pi.single 4 1 := by
    rw [map_add]
    change coordinateEquiv (frame 0) + coordinateEquiv (frame 4) = Pi.single 0 1 + Pi.single 4 1
    rw [coordinateEquiv_apply_frame 0, coordinateEquiv_apply_frame 4]
  have hw : wittNorm (coordinateEquiv (uPlus + uMinus)) = 1 := by
    rw [hx]
    norm_num [wittNorm, Pi.single_apply]
  have h := mannheim_witt_krein_conformal_scaling 0.4 1.3
    (coordinateEquiv (uPlus + uMinus)) 5 1 2 2 3 1 0 1
  exact ⟨hw, h.1, h.2.2.1, h.2.2.2.2.2.1.1⟩

/-- T1-F11-03: Weyl–Bloch state invariance under combined conformal scale and chiral phase. -/
theorem t1_f11_03_weyl_bloch_scale_gauge_invariance :
    let x := coordinateEquiv (uPlus + rootPlus 1)
    let U_g := scaleGaugeMultiplier 1.2 0.8 • weylUpperMat x
    let L_g := scaleGaugeMultiplier 1.2 (-0.8) • weylLowerMat x
    mannheimChiralGaugeMat4 1.2 0.8 * circularConnectionMat4 x = chiralOffBlock4 U_g L_g ∧
    gramBlochState U_g = gramBlochState (weylUpperMat x) ∧
    gramBlochState L_g = gramBlochState (weylLowerMat x) := by
  have h := mannheim_weyl_bloch_scale_gauge_invariance 1.2 0.8
    (coordinateEquiv (uPlus + rootPlus 1)) 0.5
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- T1-F11-04: Layer 0 curvature covariance, `vol4Scale` trace law, and `tailTowerCone` colimit transport. -/
theorem t1_f11_04_chiral_phase_curvature_colimit_tail :
    let x := coordinateEquiv (uPlus + uMinus)
    let Uα := mannheimChiralGaugeMat4 0 0.9
    let x_sc := Real.exp (-0.5) • x
    let A_g := Uα * circularConnectionMat4 x_sc * Uαᴴ
    let F_g := A_g * A_g
    let cone := CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C
    let ι := diagTowerStarHom 2
    let ψ := (cone.toColimit 2).toRingHom.comp ι.toRingHom
    F_g = (Real.exp (2 * (-0.5)) : ℂ) • circularCurvatureMat4 x ∧
    (F_gᴴ * F_g).trace =
      (vol4Scale (-0.5) : ℂ) * ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace ∧
    CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling (ψ chiralProjMat4) (ψ A_g) (ψ A_g) = ψ F_g := by
  have h := mannheim_chiral_phase_curvature_action_covariant (-0.5) 0.9
    (coordinateEquiv (uPlus + uMinus))
    (CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C) 2 (diagTowerStarHom 2)
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- T1-F11-05: Layer 3 fiber Krein pairing Dirac-spinor weight compensation at `w = -3/2`. -/
theorem t1_f11_05_fiber_krein_dirac_weight_compensation :
    let β : FourSpace → ℝ := fun z => z 0 ^ 2 + 1
    let α : FourSpace → ℝ := fun z => 2 * z 1
    let x : FourSpace := frameBasis 0 + frameBasis 1
    let u : ChiralFiber := ![1, 0, 0, 0]
    let v : ChiralFiber := ![0, 0, 1, 0]
    fiberKreinPairing u v = 1 ∧
    fiberKreinPairing u v ≠ 0 ∧
    vol4Scale (β x) * invTetradScale (β x) *
        fiberKreinPairing
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • u)
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • v) =
      fiberKreinPairing u v := by
  intro β α x u v
  have huv : fiberKreinPairing u v = 1 := by
    dsimp only [fiberKreinPairing]
    rw [InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein.chiralKreinForm_to_doubled,
      EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    simp [u, v, chiralFiberToKreinFrame, dotProduct, Fin.sum_univ_four]
  have h := mannheim_fiberKreinPairing_scale_phase_law (-(3 / 2 : ℝ)) β α x u v
  exact ⟨huv, by rw [huv]; exact one_ne_zero, (h.2.2.2 rfl).2⟩

/-! ### F12: Typed Bridge across Doubled-Minkowski Layers 1–3 (5 Tier 1 Cases) -/

/-- T1-F12-01: Layer 1 graded and even differential compatibility preserved under `mannheimChiralGaugeMat4`. -/
theorem t1_f12_01_graded_even_compat_preserved :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let U := (chiralDiagBlock4
      (scaleGaugeMultiplier (3 / 10) (6 / 5) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier (-2 / 5) (7 / 10) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
      (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    let Uinv := (chiralDiagBlock4
      (scaleGaugeMultiplier (-(3 / 10)) (-(6 / 5)) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier (-(-2 / 5)) (-(7 / 10)) • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
      (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
    let x := coordinateEquiv (uPlus + uMinus)
    let A_gr' := U * circularGaugeConnection4 (circularGradedOmega x) * Uinv
    let A_ev' := U * circularGaugeConnection4 (circularEvenOmega x) * Uinv
    evenGrade P (curvatureFromConnection circularGradedDiff A_gr') = genV P A_gr' A_gr' ∧
    MatrixIsHomogeneous 1 A_ev' ∧
    covariantDerivative A_ev' circularEvenDiff (genV P A_ev' A_ev') = 0 := by
  intro P U Uinv x A_gr' A_ev'
  have h := mannheim_graded_even_compat_preserved (3 / 10) (6 / 5) (-2 / 5) (7 / 10) x
  exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- T1-F12-02: Layer 1 abelian 1-form shift preserves homogeneity and squares identically on `circularEvenOmega`. -/
theorem t1_f12_02_even_oneForm_abelian_shift :
    let x := coordinateEquiv (uPlus + rootMinus 1)
    let η : ExteriorAlgebra ℂ (Fin 4 → ℂ) := ExteriorAlgebra.ι ℂ (Pi.single 2 1)
    let A := circularGaugeConnection4 (circularEvenOmega x)
    let S := Matrix.diagonal (fun _ : Fin 4 => η)
    MatrixIsHomogeneous 1 (A + S) ∧
    (A + S) * (A + S) = A * A ∧
    matrixTraceForm ((A + S) * (A + S)) = 0 ∧
    curvatureFromConnection circularEvenDiff (A + S) =
      curvatureFromConnection circularEvenDiff A + matrixExteriorDerivative circularEvenDiff S := by
  have hη : IsHomogeneousExteriorDegree 1 (ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ))) :=
    (homogeneous_one_iff_exists_generator (R := ℂ) (V := Fin 4 → ℂ) _).mpr
      ⟨Pi.single (2 : Fin 4) (1 : ℂ), rfl⟩
  have h := mannheim_even_oneForm_abelian_shift circularEvenDiff
    (coordinateEquiv (uPlus + rootMinus 1)) _ hη
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1⟩

section Layer2TestSection

open scoped Matrix.Norms.Operator

/-- T1-F12-03: Layer 2 smooth lattice–continuum gauge covariance and `Tendsto` continuum limits. -/
theorem t1_f12_03_lattice_continuum_cov_non_trivial_fields (y : FourSpace) (μ ν : Fin 4) :
    let β : FourSpace → ℝ := fun z => z 0 ^ 2 + 2 * z 1
    let α : FourSpace → ℝ := fun z => z 2 * z 3 + z 0
    let U := chiralDiagBlock4
      (scaleGaugeMultiplier 0 (0.6 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier 0 (-1.1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    let A : FourSpace → Fin 4 → Mat4C := fun z ρ => circularConnectionMat4 (witnessCircularField z ρ)
    let S := mannheimGaugeShiftMat4 β α
    let A_full : FourSpace → Fin 4 → Mat4C := fun z ρ => U * A z ρ * U⁻¹ + S z ρ
    ContDiff ℝ 2 A_full ∧
    continuumCurvature A_full y μ ν = U * continuumCurvature A y μ ν * U⁻¹ ∧
    continuumPlaquetteAction A_full y μ ν = continuumPlaquetteAction A y μ ν ∧
    Tendsto (fun a => (a ^ 2)⁻¹ • (wilsonPlaquette A_full y μ ν a - 1))
      (𝓝[≠] 0) (𝓝 (U * continuumCurvature A y μ ν * U⁻¹)) := by
  intro β α U A S A_full
  let proj0 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj1 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj2 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj3 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 3, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hβ : ContDiff ℝ 3 β :=
    ((proj0.contDiff.pow 2).add (contDiff_const.mul proj1.contDiff))
  have hα : ContDiff ℝ 3 α :=
    ((proj2.contDiff.mul proj3.contDiff).add proj0.contDiff)
  have hA : ContDiff ℝ 2 A := by
    have hEq : A = fun _ ρ => circularConnectionMat4 (witnessCircularField 0 ρ) := rfl
    rw [hEq]
    exact contDiff_const
  have h := mannheim_lattice_continuum_gauge_covariance.{0, 0} 0.6 (-1.1) β α hβ hα
    witnessCircularField A hA (fun _ => 1) y (differentiableAt_const 1) μ ν
  exact ⟨h.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end Layer2TestSection

section Layer3TestSection

open scoped Matrix.Norms.Elementwise

/-- T1-F12-04: Layer 3 4D bundle covariant derivative equivariance under `mannheimFiberScalar`. -/
theorem t1_f12_04_bundle_covariant_derivative_4d :
    let β : FourSpace → ℝ := fun z => z 0 ^ 2
    let α : FourSpace → ℝ := fun z => z 1 + z 3
    let σ : FourSpace → ChiralFiber := fun z _ => (z 0 : ℂ)
    circularBundleConnection (circularGaugeForm - mannheimGradOneForm (-1.5) β α)
        (fun y => mannheimFiberScalar (-1.5) β α y • σ y) (frameBasis 0) (frameBasis 1) =
      mannheimFiberScalar (-1.5) β α (frameBasis 0) •
        circularBundleConnection circularGaugeForm σ (frameBasis 0) (frameBasis 1) := by
  intro β α σ
  let proj0 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj1 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj3 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 3, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hβ : DifferentiableAt ℝ β (frameBasis 0) :=
    (proj0.differentiableAt.pow 2)
  have hα : DifferentiableAt ℝ α (frameBasis 0) :=
    (proj1.differentiableAt.add proj3.differentiableAt)
  have hσ : DifferentiableAt ℝ σ (frameBasis 0) :=
    differentiableAt_pi.mpr fun _ => Complex.ofRealCLM.differentiableAt.comp _ proj0.differentiableAt
  exact mannheim_bundle_covariant_derivative_4d (-1.5) β α circularGaugeForm σ
    (frameBasis 0) (frameBasis 1) hβ hα hσ

/-- T1-F12-05: Layer 3 shifted Euclidean instanton `circularGaugeForm` and Lorentzian wave solutions. -/
theorem t1_f12_05_shifted_instanton_and_waveForm_solutions :
    let β : FourSpace → ℝ := fun z => z 0 ^ 2 - z 2
    let α : FourSpace → ℝ := fun z => z 1 * z 3
    let f : ℝ → ℝ := fun s => Real.sin s + 2
    (ymCurvature (circularGaugeForm - mannheimGradOneForm 1 β α) ≠ 0 ∧
     IsSelfDualForm4 (circularGaugeForm - mannheimGradOneForm 1 β α) ∧
     YangMillsPDE (circularGaugeForm - mannheimGradOneForm 1 β α)) ∧
    (ymCurvature (circularMinkowskiWaveForm f - mannheimGradOneForm 1 β α) ≠ 0 ∧
     YangMillsPDEMinkowski (circularMinkowskiWaveForm f - mannheimGradOneForm 1 β α)) := by
  intro β α f
  let proj0 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj1 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj2 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj3 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 3, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hβ : ContDiff ℝ 2 β := (proj0.contDiff.pow 2).sub proj2.contDiff
  have hα : ContDiff ℝ 2 α := proj1.contDiff.mul proj3.contDiff
  have hf : ContDiff ℝ 2 f := Real.contDiff_sin.add contDiff_const
  have hf0 : f 0 ≠ 0 := by simp [f]
  exact mannheim_shifted_circularGaugeForm_and_waveForm_solutions 1 β α hβ hα hf hf0

end Layer3TestSection

/-! ### F13: Dual-Lane Mirrors, `AllExhaustive` Registration & Cross-Layer Synthesis (5 Tier 1 Cases) -/

/-- T1-F13-01: R1 spinor $4\pi$ rotation paired with R5 chiral phase unitarity at `β = 0`. -/
theorem t1_f13_01_r1_to_r5_cross_layer_cow_spinor_gauge :
    spinHalfSU2Rot ![0, 0, 1] (4 * Real.pi) = 1 ∧
    (mannheimChiralGaugeMat4 0 Real.pi)ᴴ * mannheimChiralGaugeMat4 0 Real.pi = 1 ∧
    cowPhaseShift 1 10 2 1 5 = -8 := by
  have hn : IsUnitAxis ![0, 0, 1] := by unfold IsUnitAxis; simp
  refine ⟨spinHalfSU2Rot_four_pi hn, (mannheimChiralGaugeMat4_unitary_of_beta_zero Real.pi).1, ?_⟩
  rw [cowPhaseShift_eq]
  norm_num

/-- T1-F13-02: R2 null propagation cancellation paired with R5 Weyl–Bloch scale–gauge invariance. -/
theorem t1_f13_02_r2_to_r5_coherence_and_bloch_invariance :
    let x := coordinateEquiv (uPlus + rootPlus 0)
    propPhaseDiff 3 6 12 6 = 0 ∧
    IsMinkowskiNull (slitRayDisplacement 2 6 12) ∧
    gramBlochState (scaleGaugeMultiplier 0.5 1.0 • weylUpperMat x) = gramBlochState (weylUpperMat x) := by
  have h2 := equal_emission_phase_cancellation 2 3 6 12 6 (by norm_num) (by norm_num)
  have h5 := mannheim_weyl_bloch_scale_gauge_invariance 0.5 1.0 (coordinateEquiv (uPlus + rootPlus 0)) 0
  exact ⟨h2.1, h2.2.2.1, h5.2.1⟩

/-- T1-F13-03: R3 constructive conformal cosmology paired with R5 `d = 4` conformal weight cancellation. -/
theorem t1_f13_03_r3_to_r5_conformal_cosmology_and_witt_scaling :
    0 < mannheimHubble 1 2 (-1) 2 ∧
    mannheimDeceleration 1 2 (-1) 2 ∈ Set.Ioo (-1 : ℝ) 0 ∧
    vol4Scale 0.7 * spinorScale 0.7 * invTetradScale 0.7 * spinorScale 0.7 = 1 ∧
    vol4Scale 0.7 * (confScalarScale 0.7) ^ 4 = 1 := by
  have h3 := mannheim_friedmann_luminosity_horizon_instantiation
    (c := 1) (S₀ := 1) (lam := 2) (k := -1) (t := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := mannheim_witt_krein_conformal_scaling 0.7 0.2 (coordinateEquiv uPlus) 1 0 0 0 0 0 0 0
  exact ⟨h3.1, h3.2.1, h5.2.2.2.2.2.2.1, h5.2.2.2.2.2.2.2.2⟩

/-- T1-F13-04: R4 marginal four-fermion dimension `γ = -1` paired with R5 `w = -3/2` Dirac fiber weight. -/
theorem t1_f13_04_r4_to_r5_critical_dim_and_bundle_weight :
    fourFermionDim (-1) = 4 ∧
    DoubleWellShape 1 (mannheimCriticalPotential (-1) 1 1 1) ∧
    (∀ (β α : FourSpace → ℝ) (x : FourSpace) (u v : ChiralFiber),
      vol4Scale (β x) * invTetradScale (β x) *
        fiberKreinPairing (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • u)
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • v) = fiberKreinPairing u v) :=
  ⟨(anomalous_dim_uv_integrability_trichotomy.1 (-1)).mpr rfl,
   (mannheim_anomalous_dimension_potential_trichotomy.2.1 1 1 1 (by norm_num)).1,
   fun β α x u v => ((mannheim_fiberKreinPairing_scale_phase_law (-(3 / 2 : ℝ)) β α x u v).2.2.2 rfl).2⟩

/-- T1-F13-05: Master `TypedArchetype` evidence witnesses across R5 and epistemic synthesis. -/
theorem t1_f13_05_arch_mannheim_ym_bridge_witness :
    (∀ (β α : ℝ) (x : Coordinate),
      gramBlochState (scaleGaugeMultiplier β α • weylUpperMat x) = gramBlochState (weylUpperMat x)) ∧
    Nonempty (archMasterMannheimEpistemicCoagulation.claim ()) := by
  refine ⟨fun β α x => ((archMannheimDoubledMinkowskiYangMillsBridge.evidence ()).2.1 β α x).1,
    ⟨mannheim_master_epistemic_coagulation_holds.1⟩⟩

/-! ## Tier 2: Boundary & Corner Cases (BVA + Non-Vacuity, F1–F13, 65 Cases) -/

/-! ### F1 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F1-01: Zero loop height `H = 0` annihilates COW action and phase shift (non-vacuity of `H ≠ 0`). -/
theorem t2_f1_01_zero_height_action_vanishes (m_g g hbar v : ℝ) :
    cowSquareActionDiff m_g g 0 v = 0 ∧ cowPhaseShift m_g g 0 hbar v = 0 := by
  simp [cowSquareActionDiff, cowPhaseShift]

/-- T2-F1-02: Zero gravity `g = 0` annihilates COW action difference. -/
theorem t2_f1_02_zero_gravity_action_vanishes (m_g H v : ℝ) :
    cowSquareActionDiff m_g 0 H v = 0 := by
  simp [cowSquareActionDiff]

/-- T2-F1-03: Zero horizontal arm `L = 0` yields zero rectangular action even when `H ≠ 0`. -/
theorem t2_f1_03_zero_horizontal_arm (m_g g H v : ℝ) :
    cowActionDiff m_g g H 0 v = 0 := by
  simp [cowActionDiff]

/-- T2-F1-04: Mass sign inversion reverses COW quantum phase shift. -/
theorem t2_f1_04_negative_mass_sign_inversion (m_g g H hbar v : ℝ) :
    cowPhaseShift (-m_g) g H hbar v = -cowPhaseShift m_g g H hbar v := by
  simp only [cowPhaseShift, cowSquareActionDiff]
  ring

/-- T2-F1-05: Concrete separation between classical free-fall equality and quantum COW phase ratio. -/
theorem t2_f1_05_distinct_masses_classical_vs_quantum_witness :
    classicalFreeFallAccel 1 1 9 = classicalFreeFallAccel 2 2 9 ∧
    cowPhaseShift 1 9 2 1 3 = -12 ∧
    cowPhaseShift 2 9 2 1 3 = -24 := by
  refine ⟨by unfold classicalFreeFallAccel; norm_num, ?_, ?_⟩ <;>
  · rw [cowPhaseShift_eq]
    norm_num

/-! ### F2 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F2-01: Degenerate `ħ = 0` collapses distinct masses (non-vacuity of `ħ ≠ 0`). -/
theorem t2_f2_01_degenerate_hbar_zero_nonvacuity :
    deBroglieWavelength 0 1 1 = deBroglieWavelength 0 2 1 ∧ (1 : ℝ) ≠ 2 := by
  simp [deBroglieWavelength]

/-- T2-F2-02: Degenerate `v = 0` collapses distinct masses (non-vacuity of `v ≠ 0`). -/
theorem t2_f2_02_degenerate_v_zero_nonvacuity :
    deBroglieWavelength 1 1 0 = deBroglieWavelength 1 2 0 ∧ (1 : ℝ) ≠ 2 := by
  simp [deBroglieWavelength]

/-- T2-F2-03: Opposite-sign masses produce distinct de Broglie wavelengths. -/
theorem t2_f2_03_opposite_sign_masses_separated :
    deBroglieWavelength 1 2 3 ≠ deBroglieWavelength 1 (-2) 3 := by
  unfold deBroglieWavelength
  norm_num

/-- T2-F2-04: Doubling mass halves the de Broglie wavelength. -/
theorem t2_f2_04_wavelength_halving_on_doubled_mass (hbar m v : ℝ) :
    deBroglieWavelength hbar (2 * m) v = deBroglieWavelength hbar m v / 2 := by
  unfold deBroglieWavelength
  ring

/-- T2-F2-05: Degenerate `c = 0` collapses Compton frequencies (non-vacuity of `c ≠ 0`). -/
theorem t2_f2_05_compton_zero_c_nonvacuity :
    comptonFrequency 1 0 1 = comptonFrequency 2 0 1 ∧ (1 : ℝ) ≠ 2 := by
  simp [comptonFrequency, InfoGeometry.Canonical.ZitterbewegungMassEmergence.restEnergyGap]

/-! ### F3 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F3-01: Zero rotation angle `θ = 0` produces the identity matrix `1`. -/
theorem t2_f3_01_theta_zero_identity :
    spinHalfSU2Rot ![0, 0, 1] 0 = 1 := by
  have hn : IsUnitAxis ![0, 0, 1] := by unfold IsUnitAxis; simp
  rw [spinHalfSU2Rot_euler hn 0]
  simp

/-- T2-F3-02: Negative `2π` rotation also produces `-1`. -/
theorem t2_f3_02_theta_neg_two_pi :
    spinHalfSU2Rot ![0, 0, 1] (-2 * Real.pi) = -1 := by
  have hn : IsUnitAxis ![0, 0, 1] := by unfold IsUnitAxis; simp
  rw [spinHalfSU2Rot_euler hn (-2 * Real.pi)]
  have hdiv : (-2 * Real.pi) / 2 = -Real.pi := by ring
  rw [hdiv, Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi]
  simp

/-- T2-F3-03: Non-unit axis `![1, 1, 1]` fails `IsUnitAxis` and `(pauliDir n)^2 ≠ 1` (non-vacuity). -/
theorem t2_f3_03_nonunit_axis_failure :
    let n : Fin 3 → ℝ := ![1, 1, 1]
    ¬ IsUnitAxis n ∧ pauliDir n * pauliDir n = (3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro n
  refine ⟨?_, ?_⟩
  · intro h
    unfold IsUnitAxis at h
    norm_num [n] at h
  · rw [pauliDir_mul_self n]
    norm_num [n]

/-- T2-F3-04: Oblique unit axis `![3/5, 4/5, 0]` is Hermitian, traceless, and flips sign at `2π`. -/
theorem t2_f3_04_oblique_unit_axis_pi :
    let n : Fin 3 → ℝ := ![3 / 5, 4 / 5, 0]
    (pauliDir n)ᴴ = pauliDir n ∧
    Matrix.trace (pauliDir n) = 0 ∧
    spinHalfSU2Rot n (2 * Real.pi) = -1 := by
  intro n
  have hn : IsUnitAxis n := by unfold IsUnitAxis; simp [n]; norm_num
  exact ⟨pauliDir_hermitian n, pauliDir_trace n, (spinHalfSU2Rot_two_pi hn).1⟩

/-- T2-F3-05: Arbitrary angle `θ = π/4` satisfies `2π` anti-periodicity and `4π` periodicity. -/
theorem t2_f3_05_shift_2pi_and_4pi :
    let e2 : Fin 3 → ℝ := ![0, 1, 0]
    spinHalfSU2Rot e2 (Real.pi / 4 + 2 * Real.pi) = -spinHalfSU2Rot e2 (Real.pi / 4) ∧
    spinHalfSU2Rot e2 (Real.pi / 4 + 4 * Real.pi) = spinHalfSU2Rot e2 (Real.pi / 4) := by
  have hn : IsUnitAxis ![0, 1, 0] := by unfold IsUnitAxis; simp
  exact ⟨spinHalfSU2Rot_add_two_pi hn (Real.pi / 4), spinHalfSU2Rot_add_four_pi hn (Real.pi / 4)⟩

/-! ### F4 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F4-01: Zero spacetime displacement is trivially null with zero propagation phase. -/
theorem t2_f4_01_zero_displacement_null (c k ω : ℝ) :
    slitRayDisplacement c 0 0 = ⟨0, 0, 0, 0⟩ ∧
    IsMinkowskiNull (slitRayDisplacement c 0 0) ∧
    propPhaseDiff k ω 0 0 = 0 := by
  have hNull := (equal_emission_phase_cancellation c 0 0 0 0 (by simp) (by simp)).2.2.1
  exact ⟨by unfold slitRayDisplacement; rw [mul_zero], hNull, by unfold propPhaseDiff; ring⟩

/-- T2-F4-02: Backward lightcone displacement (`Δt = -2, ΔL = -6`) remains null with zero phase. -/
theorem t2_f4_02_negative_time_backward_cone :
    propPhaseDiff 1 3 (-6) (-2) = 0 ∧ IsMinkowskiNull (slitRayDisplacement 3 (-2) (-6)) := by
  have h := equal_emission_phase_cancellation 3 1 3 (-6) (-2) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.2.1⟩

/-- T2-F4-03: Off-lightcone path (`ΔL ≠ c Δt`) breaks phase cancellation and nullity. -/
theorem t2_f4_03_off_lightcone_breaks_cancellation :
    propPhaseDiff 1 3 7 2 = 1 ∧
    propPhaseDiff 1 3 7 2 ≠ 0 ∧
    ¬ IsMinkowskiNull (slitRayDisplacement 3 2 7) := by
  refine ⟨by unfold propPhaseDiff; norm_num, by unfold propPhaseDiff; norm_num, ?_⟩
  intro hNull
  simp [IsMinkowskiNull, minkowskiNorm, slitRayDisplacement] at hNull
  norm_num at hNull

/-- T2-F4-04: Off-dispersion frequency (`ω ≠ c k`) breaks phase cancellation even on the lightcone. -/
theorem t2_f4_04_off_dispersion_breaks_cancellation :
    propPhaseDiff 1 5 6 2 = -4 ∧ propPhaseDiff 1 5 6 2 ≠ 0 := by
  unfold propPhaseDiff
  norm_num

/-- T2-F4-05: Degenerate `c = 0` breaks nullity of `waveFourVector` (explaining `c ≠ 0` guard). -/
theorem t2_f4_05_wave_zero_c_boundary :
    IsMinkowskiNull (slitRayDisplacement 0 2 0) ∧
    minkowskiNorm (waveFourVector 0 0 1) = -1 := by
  refine ⟨(equal_emission_phase_cancellation 0 1 0 0 2 (by norm_num) (by norm_num)).2.2.1, ?_⟩
  simp [minkowskiNorm, waveFourVector]

/-! ### F5 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F5-01: Exact coherence boundary `|ΔL| = c τ_coh` satisfies window predicate yet visibility = 0. -/
theorem t2_f5_01_exact_coherence_boundary :
    IsWithinCoherenceWindow 3 3 ∧
    coherenceVisibility 3 3 = 0 ∧
    twoSlitIntensity 5 3 1 2 6 3 3 = 10 := by
  have h := coherence_window_and_fringe_cutoff 2 3 6 3 5 1 2 3
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨h.1.mpr (by norm_num), ?_, ?_⟩
  · unfold coherenceVisibility; norm_num
  · unfold twoSlitIntensity coherenceVisibility; norm_num

/-- T2-F5-02: Negative path difference visibility symmetry. -/
theorem t2_f5_02_negative_path_diff_symmetry :
    coherenceVisibility 3 (-2) = coherenceVisibility 3 2 := by
  unfold coherenceVisibility
  norm_num

/-- T2-F5-03: Unit visibility holds iff source time offset vanishes. -/
theorem t2_f5_03_zero_src_offset_peak_iff (Δt_src : ℝ) :
    coherenceVisibility 3 Δt_src = 1 ↔ Δt_src = 0 :=
  (doubleSlit_null_ray_and_leaflet_bridge.2.2.2.1 2 3 1 1 1 (by norm_num) (by norm_num)).2.2.2.2.1
    Δt_src |>.2

/-- T2-F5-04: Constructive (`totalPhase = 0`) vs destructive (`totalPhase = π`) fringe bounds inside window. -/
theorem t2_f5_04_constructive_vs_destructive_fringe :
    twoSlitIntensity 2 4 1 1 0 2 2 = 6 ∧
    twoSlitIntensity 2 4 1 1 Real.pi 2 2 = 2 := by
  unfold twoSlitIntensity coherenceVisibility totalSlitPhaseDiff propPhaseDiff sourcePhaseDiff
  refine ⟨?_, ?_⟩
  · norm_num [Real.cos_zero]
  · norm_num

/-- T2-F5-05: Asymptotic tail separation outside coherence window (`coherenceVisibility = 0` vs `0 < fisherLeaflet < 1`). -/
theorem t2_f5_05_asymptotic_tail_separation :
    coherenceVisibility 3 (10 / 2) = 0 ∧
    0 < fisherLeaflet (10 / (2 * 3)) ∧
    fisherLeaflet (10 / (2 * 3)) < 1 := by
  have h := (doubleSlit_null_ray_and_leaflet_bridge.2.2.2.1 2 3 1 1 1
    (by norm_num) (by norm_num)).2.2.2.2.2.1 10 (by norm_num)
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-! ### F6 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F6-01: Blueshift domain `-1 < z = -1/2 < 0` yields positive radicand and negative `d_L`. -/
theorem t2_f6_01_blueshift_domain :
    conformalRadicand (-1 / 2) (-1 / 2) = 5 / 2 ∧
    0 < conformalRadicand (-1 / 2) (-1 / 2) ∧
    conformalLuminosityDist 1 1 (-1 / 2) (-1 / 2) < 0 := by
  refine ⟨by unfold conformalRadicand; norm_num,
    conformalRadicand_pos ⟨by norm_num, by norm_num⟩ (by norm_num), ?_⟩
  unfold conformalLuminosityDist conformalRadicand
  have hsq : 1 < Real.sqrt (5 / 2 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  nlinarith

/-- T2-F6-02: Near-boundary `q₀ = -99/100 ∈ (-1, 0)` maintains positive radicand and `d_L`. -/
theorem t2_f6_02_q0_near_minus_one :
    0 < conformalRadicand (-99 / 100) 2 ∧ 0 < conformalLuminosityDist 1 1 (-99 / 100) 2 :=
  ⟨conformalRadicand_pos ⟨by norm_num, by norm_num⟩ (by norm_num),
   conformalLuminosityDist_pos (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)⟩

/-- T2-F6-03: Near-zero `q₀ = -1/100 ∈ (-1, 0)` maintains positive radicand and `d_L`. -/
theorem t2_f6_03_q0_near_zero_minus :
    0 < conformalRadicand (-1 / 100) 2 ∧ 0 < conformalLuminosityDist 1 1 (-1 / 100) 2 :=
  ⟨conformalRadicand_pos ⟨by norm_num, by norm_num⟩ (by norm_num),
   conformalLuminosityDist_pos (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)⟩

/-- T2-F6-04: Outside `q₀ ∈ (-1, 0)` (`q₀ = -2`), radicand can turn negative (non-vacuity of `hq`). -/
theorem t2_f6_04_non_Ioo_radicand_negative_witness :
    conformalRadicand (-2) 1 = -1 / 2 ∧ conformalRadicand (-2) 1 < 0 := by
  unfold conformalRadicand
  norm_num

/-- T2-F6-05: De Sitter `q₀ = -1` endpoint and `z → -1⁺` blueshift / `z = -1` singularity boundary. -/
theorem t2_f6_05_z_lt_minus_one_singularity_side :
    conformalRadicand (-1) 1 = 1 / 4 ∧
    0 < conformalRadicand (-1) 1 ∧
    conformalLuminosityDist 1 1 (-1) 1 = 2 ∧
    conformalRadicand (-1 / 2) (-9 / 10) = 101 / 2 ∧
    conformalLuminosityDist 1 1 (-1 / 2) (-9 / 10) < 0 ∧
    conformalLuminosityDist 1 1 (-1 / 2) (-1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold conformalRadicand
    norm_num
  · unfold conformalRadicand
    norm_num
  · unfold conformalLuminosityDist conformalRadicand
    have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num [hsqrt]
  · unfold conformalRadicand
    norm_num
  · unfold conformalLuminosityDist conformalRadicand
    have hrad : (1 + (-1 / 2 : ℝ) - (-1 / 2 : ℝ) / (1 + (-9 / 10 : ℝ)) ^ 2) = 101 / 2 := by
      norm_num
    rw [hrad]
    have hsq : 1 < Real.sqrt (101 / 2 : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    nlinarith
  · unfold conformalLuminosityDist
    norm_num

/-! ### F7 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F7-01: Near-zero `q₀ = -1/100` still satisfies strict `d_L''(0) > c / H₀`. -/
theorem t2_f7_01_q0_near_zero_second_deriv :
    deriv (deriv (conformalLuminosityDist 1 1 (-1 / 100))) 0 = 101 / 100 ∧
    (1 : ℝ) < 101 / 100 := by
  have h := conformalLuminosityDist_deriv2_zero (c := 1) (H₀ := 1) (q₀ := -1 / 100)
    (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  exact ⟨by linarith [h.1], by norm_num⟩

/-- T2-F7-02: Near-de Sitter `q₀ = -99/100` satisfies `1 < d_L''(0) < 2` for `c = H₀ = 1`. -/
theorem t2_f7_02_q0_near_minus_one_second_deriv :
    deriv (deriv (conformalLuminosityDist 1 1 (-99 / 100))) 0 = 199 / 100 ∧
    (1 : ℝ) < 199 / 100 ∧
    (199 / 100 : ℝ) < 2 := by
  have h := conformalLuminosityDist_deriv2_zero (c := 1) (H₀ := 1) (q₀ := -99 / 100)
    (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  exact ⟨by linarith [h.1], by norm_num, by norm_num⟩

/-- T2-F7-03: `HasDerivAt` holds on the blueshift branch `z = -1/2 > -1`. -/
theorem t2_f7_03_has_deriv_at_blueshift :
    HasDerivAt (conformalLuminosityDist 1 2 (-1 / 2))
      (conformalLumDistDeriv1 1 2 (-1 / 2) (-1 / 2)) (-1 / 2) :=
  has_deriv_at_conformal_luminosity_dist (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)

/-- T2-F7-04: `deriv` and `iteratedDeriv` agree at orders `1` and `2` for `q₀ = -3/4`. -/
theorem t2_f7_04_deriv1_and_iteratedDeriv1_agree :
    let f := conformalLuminosityDist 2 5 (-3 / 4)
    deriv f 0 = iteratedDeriv 1 f 0 ∧ deriv (deriv f) 0 = iteratedDeriv 2 f 0 := by
  have h1 := conformalLuminosityDist_deriv1_zero (c := 2) (H₀ := 5) (q₀ := -3 / 4)
    (by norm_num) ⟨by norm_num, by norm_num⟩
  have h2 := conformalLuminosityDist_deriv2_zero (c := 2) (H₀ := 5) (q₀ := -3 / 4)
    (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
  exact ⟨h1.1.trans h1.2.symm, h2.1.trans h2.2.1.symm⟩

/-- T2-F7-05: Positive deceleration `q₀ = 1/2 > 0` gives `d_L'(0) = 1`, `d_L''(0) = 1/2 < 1` (non-vacuity of `q₀ < 0`). -/
theorem t2_f7_05_positive_q0_deceleration_contrast :
    conformalLumDistDeriv1 1 1 (1 / 2) 0 = 1 ∧
    deriv (conformalLuminosityDist 1 1 (1 / 2)) 0 = 1 ∧
    deriv (deriv (conformalLuminosityDist 1 1 (1 / 2))) 0 = 1 / 2 ∧
    ¬ ((1 : ℝ) / 1 < deriv (deriv (conformalLuminosityDist 1 1 (1 / 2))) 0) := by
  have h1z_nhds : ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4), 0 < 1 + z := fun z hz => by
    linarith [hz.1]
  have hrad_pos : ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4),
      0 < conformalRadicand (1 / 2) z := by
    intro z hz
    have h34 : (3 / 4 : ℝ) < 1 + z := by linarith [hz.1]
    have hsq : (9 / 16 : ℝ) < (1 + z) ^ 2 := by nlinarith
    have hdiv : (1 / 2 : ℝ) / (1 + z) ^ 2 < 8 / 9 := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    unfold conformalRadicand
    linarith
  have hd_on : ∀ z ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4),
      HasDerivAt (conformalLuminosityDist 1 1 (1 / 2))
        (conformalLumDistDeriv1 1 1 (1 / 2) z) z := by
    intro z hz
    have hz1 : 0 < 1 + z := h1z_nhds z hz
    have hr_pos : 0 < conformalRadicand (1 / 2) z := hrad_pos z hz
    have hsqrt_pos : 0 < Real.sqrt (conformalRadicand (1 / 2) z) := Real.sqrt_pos.mpr hr_pos
    have h1z : HasDerivAt (fun x : ℝ => 1 + x) 1 z := (hasDerivAt_id' z).const_add 1
    have hsq : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + z)) z :=
      (h1z.fun_pow 2).congr_deriv (by simp)
    have hpref : HasDerivAt (fun x : ℝ => -((1 : ℝ) * (1 + x) ^ 2 / ((1 : ℝ) * (1 / 2))))
        (-(2 * (1 : ℝ) * (1 + z) / ((1 : ℝ) * (1 / 2)))) z := by
      refine (((hsq.const_mul 1).div_const (1 * (1 / 2))).fun_neg).congr_deriv ?_
      ring
    have hr : HasDerivAt (conformalRadicand (1 / 2)) (2 * (1 / 2 : ℝ) / (1 + z) ^ 3) z :=
      has_deriv_at_conformal_radicand (1 / 2) (by linarith [hz.1])
    have hsqrt := hr.sqrt hr_pos.ne'
    have hfac : HasDerivAt (fun x : ℝ => 1 - Real.sqrt (conformalRadicand (1 / 2) x))
        (-((1 / 2 : ℝ) / ((1 + z) ^ 3 * Real.sqrt (conformalRadicand (1 / 2) z)))) z := by
      refine (hsqrt.const_sub 1).congr_deriv ?_
      field_simp [hz1.ne', hsqrt_pos.ne']
    refine (hpref.fun_mul hfac).congr_deriv ?_
    unfold conformalLumDistDeriv1
    field_simp [hz1.ne', hsqrt_pos.ne']
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4) := ⟨by norm_num, by norm_num⟩
  have heval0 : conformalLumDistDeriv1 1 1 (1 / 2) 0 = 1 := by
    simp [conformalLumDistDeriv1, conformalRadicand]
  have hd1_0 : deriv (conformalLuminosityDist 1 1 (1 / 2)) 0 = 1 := by
    rw [(hd_on 0 h0_mem).deriv, heval0]
  have hev : deriv (conformalLuminosityDist 1 1 (1 / 2)) =ᶠ[𝓝 0]
      conformalLumDistDeriv1 1 1 (1 / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0_mem] with z hz
    exact (hd_on z hz).deriv
  have hr0 : conformalRadicand (1 / 2) 0 = 1 := by simp [conformalRadicand]
  have hr0_sqrt : Real.sqrt (conformalRadicand (1 / 2) 0) = 1 := by rw [hr0, Real.sqrt_one]
  have h1z : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id' 0).const_add 1
  have hr : HasDerivAt (conformalRadicand (1 / 2)) (2 * (1 / 2 : ℝ)) 0 :=
    (has_deriv_at_conformal_radicand (1 / 2) (by norm_num : (-1 : ℝ) < 0)).congr_deriv (by norm_num)
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (conformalRadicand (1 / 2) x)) (1 / 2) 0 := by
    refine (hr.sqrt (by rw [hr0]; exact one_ne_zero)).congr_deriv ?_
    rw [hr0_sqrt]
    ring
  have hfac : HasDerivAt (fun x : ℝ => 1 - Real.sqrt (conformalRadicand (1 / 2) x)) (-(1 / 2)) 0 :=
    hsqrt.const_sub 1
  have hT1_left : HasDerivAt (fun x : ℝ => -(2 * (1 : ℝ) * (1 + x) / (1 * (1 / 2))))
      (-(2 * (1 : ℝ) / (1 * (1 / 2)))) 0 := by
    refine (((h1z.const_mul (2 * 1)).div_const (1 * (1 / 2))).fun_neg).congr_deriv ?_
    ring
  have hT1 : HasDerivAt
      (fun x : ℝ =>
        -(2 * (1 : ℝ) * (1 + x) / (1 * (1 / 2))) *
          (1 - Real.sqrt (conformalRadicand (1 / 2) x)))
      2 0 := by
    refine (hT1_left.fun_mul hfac).congr_deriv ?_
    rw [hr0_sqrt]
    norm_num
  have hg : HasDerivAt (fun x : ℝ => (1 : ℝ) * (1 + x) * Real.sqrt (conformalRadicand (1 / 2) x))
      (1 + (1 / 2 : ℝ)) 0 := by
    refine ((h1z.const_mul 1).fun_mul hsqrt).congr_deriv ?_
    rw [hr0_sqrt]
    ring
  have hg0_ne : (1 : ℝ) * (1 + (0 : ℝ)) * Real.sqrt (conformalRadicand (1 / 2) 0) ≠ 0 := by
    rw [hr0_sqrt]
    norm_num
  have hT2 : HasDerivAt
      (fun x : ℝ => (1 : ℝ) / (1 * (1 + x) * Real.sqrt (conformalRadicand (1 / 2) x)))
      (-(1 + (1 / 2 : ℝ))) 0 := by
    refine ((hasDerivAt_const 0 (1 : ℝ)).fun_div hg hg0_ne).congr_deriv ?_
    rw [hr0_sqrt]
    norm_num
  have htot : HasDerivAt (conformalLumDistDeriv1 1 1 (1 / 2)) (1 / 2) 0 := by
    unfold conformalLumDistDeriv1
    exact (hT1.fun_add hT2).congr_deriv (by norm_num)
  have hd2_0 : deriv (deriv (conformalLuminosityDist 1 1 (1 / 2))) 0 = 1 / 2 := by
    rw [hev.deriv_eq]
    exact htot.deriv
  refine ⟨heval0, hd1_0, hd2_0, ?_⟩
  rw [hd2_0]
  norm_num

/-! ### F8 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F8-01: Degenerate interval `t_i = t` gives zero conformal and Einstein horizons. -/
theorem t2_f8_01_degenerate_interval_t_i_eq_t :
    conformalHorizon 1 1 2 (-1) 2 2 = 0 ∧ einsteinPowerHorizon 1 (1 / 2) 2 2 = 0 := by
  simp [conformalHorizon, einsteinPowerHorizon]

/-- T2-F8-02: Matter-dominated Einstein horizon (`p = 2/3`) from `t_i = 0` to `t = 8` equals `6`. -/
theorem t2_f8_02_einstein_zero_lower_bound :
    einsteinPowerHorizon 1 (2 / 3) 0 8 = 6 := by
  have h := einsteinPowerHorizon_bounded (c := 1) (p := 2 / 3) (t_i := 0) (t := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h.1]
  have hExp : (1 - 2 / 3 : ℝ) = 1 / 3 := by norm_num
  have h0 : (0 : ℝ) ^ (1 / 3 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    calc
      (8 : ℝ) ^ (1 / 3 : ℝ) = ((2 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ (((3 : ℕ) : ℝ) * (1 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      _ = 2 := by norm_num
  rw [hExp, h0, h8]
  norm_num

/-- T2-F8-03: Reversed interval `t_i = 4 > t = 1` makes Einstein integral negative (non-vacuity of `t_i ≤ t`). -/
theorem t2_f8_03_einstein_reversed_interval_nonneg_fails :
    einsteinPowerHorizon 1 (1 / 2) 4 1 < 0 := by
  have h := einsteinPowerHorizon_bounded (c := 1) (p := 1 / 2) (t_i := 1) (t := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hPos : 0 < einsteinPowerHorizon 1 (1 / 2) 1 4 := by
    rw [h.1]
    have h4 : (4 : ℝ) ^ (1 - 1 / 2 : ℝ) = 2 := by
      rw [show (1 - 1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
      norm_num
    have h1 : (1 : ℝ) ^ (1 - 1 / 2 : ℝ) = 1 := Real.one_rpow _
    rw [h4, h1]
    norm_num
  have hSwap : einsteinPowerHorizon 1 (1 / 2) 4 1 = -einsteinPowerHorizon 1 (1 / 2) 1 4 := by
    unfold einsteinPowerHorizon
    exact intervalIntegral.integral_symm 1 4
  linarith

/-- T2-F8-04: Conformal horizon exceeds an arbitrary bound `B = 1000` for sufficiently small `t_i > 0`. -/
theorem t2_f8_04_conformal_horizon_exceeds_arbitrary_bound :
    ∃ t_i : ℝ, 0 < t_i ∧ 1000 < conformalHorizon 1 1 2 (-1) t_i 2 := by
  have hT := (conformalHorizon_eq_and_tendsto_atTop (c := 1) (S₀ := 1) (lam := 2) (k := -1) (t := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  have hEv := hT.eventually (Filter.eventually_gt_atTop (1000 : ℝ))
  obtain ⟨s, hs, hB⟩ := Filter.eventually_iff_exists_mem.mp hEv
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hs
  have hmem : δ / 2 ∈ Metric.ball (0 : ℝ) δ ∩ Set.Ioi 0 := by
    refine ⟨?_, half_pos hδ⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
    linarith
  exact ⟨δ / 2, half_pos hδ, hB (δ / 2) (hsub hmem)⟩

/-- T2-F8-05: Small temperature ratio `R = 11/10` close to `1` still satisfies `t₂/t₁ < R < R²`. -/
theorem t2_f8_05_small_temperature_ratio {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₁₂ : t₁ < t₂)
    (hmatch : mannheimScaleFactor 1 2 (-1) t₂ / mannheimScaleFactor 1 2 (-1) t₁ = 11 / 10) :
    t₂ / t₁ < 11 / 10 ∧ t₂ / t₁ < (11 / 10 : ℝ) ^ 2 := by
  have h := conformal_vs_standard_nucleosynthesis_and_planck_ratios
    (S₀ := 1) (lam := 2) (k := -1) (t₁ := t₁) (t₂ := t₂) (T₁ := 11) (T₂ := 10)
    (by norm_num) (by norm_num) (by norm_num) ht₁ ht₁₂ (by norm_num) (by norm_num)
  simpa using h.2.2.2.2.1 (by simpa using hmatch)

/-! ### F9 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F9-01: Integrability boundary at `γ = -1` (non-integrable) vs `γ = -3/2` (integrable). -/
theorem t2_f9_01_integrability_boundary_gamma_neg_one :
    ¬ IntegrableOn (fun u : ℝ => u ^ (-1 : ℝ)) (Set.Ioi 1) ∧
    IntegrableOn (fun u : ℝ => u ^ (-3 / 2 : ℝ)) (Set.Ioi 1) :=
  ⟨anomalous_dim_uv_integrability_trichotomy.2.2.2.1.1,
   (anomalous_dim_uv_integrability_trichotomy.2.1 (-3 / 2)).mpr (by norm_num)⟩

/-- T2-F9-02: UV cutoff boundary `Λ = 1` produces zero integral `1 - 1/1 = 0 < 1`. -/
theorem t2_f9_02_cutoff_boundary_Lambda_one :
    (∫ u in (1 : ℝ)..1, u ^ (-2 : ℝ)) = 0 ∧
    (∫ u in (1 : ℝ)..1, u ^ (-2 : ℝ)) = 1 - 1 / 1 := by
  have h := anomalous_dim_uv_integrability_trichotomy.2.2.2.2.2.2.2.1 1 (by norm_num)
  exact ⟨intervalIntegral.integral_same, h.1⟩

/-- T2-F9-03: Single-well boundary at `γ = -1/2`: origin zero, even symmetry, positive away from 0. -/
theorem t2_f9_03_single_well_origin_and_even :
    let V := mannheimCriticalPotential (-1 / 2) 2 1 3
    V 0 = 0 ∧ 0 < V (-1) ∧ V (-2) = V 2 := by
  have hS := mannheim_anomalous_dimension_potential_trichotomy.1 (-1 / 2) 2 1 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨hS.1, hS.2.1 (-1) (by norm_num), hS.2.2.2.1 2⟩

/-- T2-F9-04: Double-well separation at `γ = -1`: `m = 1 ≠ ±2` sits strictly above minimum `-8`. -/
theorem t2_f9_04_double_well_non_min_separation :
    let V := mannheimCriticalPotential (-1) 2 1 1;
    -(2 ^ 4 / 2 : ℝ) < V 1 := by
  intro V
  have hDW := (mannheim_anomalous_dimension_potential_trichotomy.2.1 2 1 1 (by norm_num)).1
  have h1 := hDW.2.1 1 (by norm_num)
  refine lt_of_le_of_ne h1.1 ?_
  intro heq
  rcases h1.2.mp heq.symm with hm | hm <;> norm_num at hm

/-- T2-F9-05: Inverted potential at `γ = -2` is concave and diverges to `-∞` as `m → +∞`. -/
theorem t2_f9_05_upside_down_concave_and_zero :
    let V := mannheimCriticalPotential (-2) 2 1 3
    V 0 = 0 ∧ V 1 < 0 ∧ deriv (deriv V) 1 < 0 ∧ Tendsto V Filter.atTop Filter.atBot := by
  have hU := mannheim_anomalous_dimension_potential_trichotomy.2.2.1 2 1 3 (by norm_num)
  exact ⟨hU.1, hU.2.1 1 (by norm_num), hU.2.2.2.2.1 1 (by norm_num), hU.2.2.2.2.2⟩

/-! ### F10 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F10-01: Exact threshold `q² = 4 m²` yields zero imaginary part. -/
theorem t2_f10_01_exact_2m_threshold_zero_im :
    scalarBubbleImPart 1 2 16 = 0 ∧
    (dynamicalHiggsComplexInvProp 1 1 5 1 2 16).im = 0 := by
  refine ⟨scalarBubbleImPart_threshold_dichotomy.1 1 2 16 (by norm_num), ?_⟩
  simp [dynamicalHiggsComplexInvProp, scalarBubbleImPart_threshold_dichotomy.1 1 2 16 (by norm_num)]
  norm_num

/-- T2-F10-02: Below-threshold `q² = 0` yields zero imaginary part. -/
theorem t2_f10_02_below_threshold_zero_im :
    scalarBubbleImPart 1 2 0 = 0 ∧
    (dynamicalHiggsComplexInvProp 1 1 5 1 2 0).im = 0 := by
  refine ⟨scalarBubbleImPart_threshold_dichotomy.1 1 2 0 (by norm_num), ?_⟩
  simp [dynamicalHiggsComplexInvProp, scalarBubbleImPart_threshold_dichotomy.1 1 2 0 (by norm_num)]
  norm_num

/-- T2-F10-03: Immediately above threshold `q² = 4 + 1/100` activates positive bubble width. -/
theorem t2_f10_03_just_above_threshold :
    0 < scalarBubbleImPart 1 1 (4 + 1 / 100) :=
  scalarBubbleImPart_threshold_dichotomy.2 1 1 (4 + 1 / 100) (by norm_num) (by norm_num)

/-- T2-F10-04: At threshold `M_H = 2 m = 4`, dynamical Higgs width vanishes (non-vacuity of `2m < M_H`). -/
theorem t2_f10_04_at_or_below_2m_higgs_mass_nonvacuity :
    (dynamicalHiggsComplexInvProp 1 1 4 1 2 (4 ^ 2)).im = 0 := by
  simp [dynamicalHiggsComplexInvProp, scalarBubbleImPart_threshold_dichotomy.1 1 2 (4 ^ 2) (by norm_num)]

/-- T2-F10-05: Elementary Higgs imaginary part vanishes identically vs `s_pole.im < 0` for dynamical Higgs. -/
theorem t2_f10_05_elementary_complex_pole_absence (M_H qSq : ℝ) :
    (elementaryHiggsInvProp M_H qSq).im = 0 ∧
    ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      (((3 ^ 2 : ℝ) : ℂ) - Complex.I * ((3 * Γ_dyn : ℝ) : ℂ)).im < 0 := by
  obtain ⟨Γ_dyn, hΓ, _, _, _, _, hPole, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨by rw [elementaryHiggsInvProp, Complex.ofReal_im], Γ_dyn, hΓ, hPole.1⟩

/-! ### F11 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F11-01: At `β = 0`, `mannheimChiralGaugeMat4 0 α` is strictly unitary and fiber Krein is an isometry. -/
theorem t2_f11_01_beta_zero_unitary (α : ℝ) (u v : ChiralFiber) :
    (mannheimChiralGaugeMat4 0 α)ᴴ * mannheimChiralGaugeMat4 0 α = 1 ∧
    mannheimChiralGaugeMat4 0 α * (mannheimChiralGaugeMat4 0 α)ᴴ = 1 ∧
    fiberKreinPairing (mannheimFiberScalar 1 (fun _ => 0) (fun _ => α) 0 • u)
      (mannheimFiberScalar 1 (fun _ => 0) (fun _ => α) 0 • v) = fiberKreinPairing u v :=
  ⟨(mannheimChiralGaugeMat4_unitary_of_beta_zero α).1,
   (mannheimChiralGaugeMat4_unitary_of_beta_zero α).2,
   (mannheim_fiberKreinPairing_scale_phase_law 1 (fun _ => 0) (fun _ => α) 0 u v).2.1 rfl⟩

/-- T2-F11-02: Lightlike null vector preserves zero Krein bilinear form under arbitrary conformal rescale `β = 2.5`. -/
theorem t2_f11_02_null_cone_witt_zero :
    let v : Coordinate := symmSection 1 1 0 0 + antiSection 0 0 0 0
    wittNorm v = 0 ∧
    conformalRescale 2.5 chiralKreinBilin (circularCoordToKreinFrame v) (circularCoordToKreinFrame v) = 0 := by
  intro v
  have hv : wittNorm v = 0 := by
    simp [v, wittNorm, symmSection, antiSection]
  have h := mannheim_witt_krein_conformal_scaling 2.5 0 v 1 1 0 0 0 0 0 0
  exact ⟨hv, h.2.2.2.2.1.mpr hv⟩

/-- T2-F11-03: Additive inverse `(-β, -α)` exactly inverts `mannheimChiralGaugeMat4 β α` and `vol4Scale β`. -/
theorem t2_f11_03_additive_inverse_gauge_cancel (β α : ℝ) :
    mannheimChiralGaugeMat4 (-β) (-α) * mannheimChiralGaugeMat4 β α = 1 ∧
    vol4Scale (-β) * vol4Scale β = 1 := by
  refine ⟨mannheimChiralGaugeMat4_neg_mul_cancel β α, ?_⟩
  simp [vol4Scale, ← Real.exp_add]

/-- T2-F11-04: Weight `w = 1` produces the exact metric conformal factor `exp(2 β(x))` independent of `α`. -/
theorem t2_f11_04_weight_w_one_metric_factor (β α : FourSpace → ℝ) (x : FourSpace) (u v : ChiralFiber) :
    fiberKreinPairing (mannheimFiberScalar 1 β α x • u) (mannheimFiberScalar 1 β α x • v) =
      Real.exp (2 * β x) * fiberKreinPairing u v :=
  (mannheim_fiberKreinPairing_scale_phase_law 1 β α x u v).2.2.1 rfl

/-- T2-F11-05: Nondegenerate Weyl upper block preserves `IsStrictlyPositive` and nonnegative Umegaki entropy under `(β, α)`. -/
theorem t2_f11_05_nondegenerate_det_strict_positivity_umegaki :
    let x := coordinateEquiv ((2 : ℝ) • uPlus + rootPlus 0)
    let U_g := scaleGaugeMultiplier 0.8 1.4 • weylUpperMat x
    Matrix.det (weylUpperMat x) ≠ 0 ∧
    IsStrictlyPositive (gramBlochState U_g) ∧
    0 ≤ quantumUmegakiGibbs (gramBlochState U_g) 0.5 := by
  have hDet : Matrix.det (weylUpperMat (coordinateEquiv ((2 : ℝ) • uPlus + rootPlus 0))) ≠ 0 := by
    have hx : coordinateEquiv ((2 : ℝ) • uPlus + rootPlus 0) =
        (2 : ℝ) • Pi.single 0 1 + Pi.single 1 1 := by
      change coordinateEquiv ((2 : ℝ) • frame 0 + frame 1) = (2 : ℝ) • Pi.single 0 1 + Pi.single 1 1
      rw [map_add, map_smul, coordinateEquiv_apply_frame 0, coordinateEquiv_apply_frame 1]
    intro hd
    have hd_val : Matrix.det (weylUpperMat (coordinateEquiv ((2 : ℝ) • uPlus + rootPlus 0))) = 3 := by
      rw [hx]
      simp [weylUpperMat, pauliSolder2x2, InfoGeometry.Quantum.PauliSoldering.solder,
        InfoGeometry.Quantum.PauliSoldering.σ0, InfoGeometry.Quantum.PauliSoldering.σ1,
        InfoGeometry.Quantum.PauliSoldering.σ2, InfoGeometry.Quantum.PauliSoldering.σ3,
        Matrix.det_fin_two]
      norm_num
    rw [hd_val] at hd
    norm_num at hd
  have hW := (mannheim_weyl_bloch_scale_gauge_invariance 0.8 1.4
    (coordinateEquiv ((2 : ℝ) • uPlus + rootPlus 0)) 0.5).2.2.2.1 hDet
  exact ⟨hDet, hW.1, hW.2.1⟩

/-! ### F12 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F12-01: Closed 1-form shift (`d η = 0`) leaves `matrixExteriorDerivative` and `curvatureFromConnection` strictly invariant. -/
theorem t2_f12_01_closed_oneForm_shift_full_curv_invariance
    (x : Coordinate) (η : ExteriorAlgebra ℂ (Fin 4 → ℂ)) (hη : IsHomogeneousExteriorDegree 1 η) :
    let A := circularGaugeConnection4 (circularEvenOmega x)
    let S := Matrix.diagonal (fun _ : Fin 4 => η)
    matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) (A + S) =
      matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) A ∧
    curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) (A + S) =
      curvatureFromConnection (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) A :=
  (mannheim_even_oneForm_abelian_shift 0 x η hη).2.2.2.2.2.2 rfl

section Layer2BoundarySection

open scoped Matrix.Norms.Operator

/-- T2-F12-02: Pure abelian shift (`α₁ = 0, α₂ = 0`, `U = 1`) leaves lattice covariant diff and continuum curvature exact. -/
theorem t2_f12_02_lattice_shift_only_exact_invariance
    (β α : FourSpace → ℝ) (hβ : ContDiff ℝ 3 β) (hα : ContDiff ℝ 3 α)
    (A : FourSpace → Fin 4 → Mat4C) (hA : ContDiff ℝ 2 A)
    (Φ : FourSpace → Mat4C) (y : FourSpace) (hΦ : DifferentiableAt ℝ Φ y) (μ ν : Fin 4) :
    let S := mannheimGaugeShiftMat4 β α
    let A_shift : FourSpace → Fin 4 → Mat4C := fun z ρ => A z ρ + S z ρ
    (∀ a : ℝ, latticeCovariantDiff A_shift Φ y μ a = latticeCovariantDiff A Φ y μ a) ∧
    continuumCurvature A_shift y μ ν = continuumCurvature A y μ ν := by
  have h := mannheim_lattice_continuum_gauge_covariance.{0, 0} 0 0 β α hβ hα
    witnessCircularField A hA Φ y hΦ μ ν
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1⟩

/-- T2-F12-03: Constant scale and phase fields produce zero `mannheimGaugeShiftMat4` and zero `mannheimGradOneForm`. -/
theorem t2_f12_03_constant_beta_alpha_zero_grad (w : ℝ) (y : FourSpace) (μ : Fin 4) :
    mannheimGaugeShiftMat4 (fun _ => 3) (fun _ => -2) y μ = 0 ∧
    mannheimGradOneForm w (fun _ => 3) (fun _ => -2) = 0 := by
  refine ⟨?_, ?_⟩
  · unfold mannheimGaugeShiftMat4
    simp
  · ext x v i j
    have hv : v = fun _ => v 0 := funext fun k => by fin_cases k; rfl
    rw [hv]
    change (((w • fderiv ℝ (fun _ : FourSpace => (3 : ℝ)) x).smulRight (1 : Mat4C) +
      (fderiv ℝ (fun _ : FourSpace => (-2 : ℝ)) x).smulRight (Complex.I • (1 : Mat4C))) (v 0)) i j = 0
    simp

section Layer2TailTowerHelper
private lemma coord0_contDiff : ContDiff ℝ 3 (fun z : FourSpace => z 0) :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun z : FourSpace => z 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).contDiff

private lemma coord1_contDiff : ContDiff ℝ 3 (fun z : FourSpace => z 1) :=
  (LinearMap.toContinuousLinearMap
    { toFun := fun z : FourSpace => z 1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).contDiff

set_option backward.isDefEq.respectTransparency false in
private lemma tailTower_cont_zero :
    Continuous
      (((CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C).toColimit 0).toRingHom.comp
        (diagTowerStarHom 0).toRingHom) := by
  have hψ_eq :
      ((((CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C).toColimit 0).toRingHom.comp
          (diagTowerStarHom 0).toRingHom : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) :
        Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) = fun M _ => M := by
    funext M n
    change CanonicalTwoSheetedInductiveColimit.towerColimitFn 0 (fun _ => M, M) n = M
    simp [CanonicalTwoSheetedInductiveColimit.towerColimitFn]
  change Continuous
    ((((CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C).toColimit 0).toRingHom.comp
        (diagTowerStarHom 0).toRingHom : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) :
      Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
  rw [hψ_eq]
  exact continuous_pi fun _ => continuous_id
end Layer2TailTowerHelper

set_option backward.isDefEq.respectTransparency false in
/-- T2-F12-04: Layer 2 `tailTowerCone` colimit transport at `k = 0` certifies all 4 `Tendsto` limits. -/
theorem t2_f12_04_lattice_colimit_transport_tailTower (y : FourSpace) :
    let β : FourSpace → ℝ := fun z => z 0
    let α : FourSpace → ℝ := fun z => z 1
    let U := chiralDiagBlock4
      (scaleGaugeMultiplier 0 (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (scaleGaugeMultiplier 0 (-(1 / 2 : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    let A : FourSpace → Fin 4 → Mat4C := fun z ρ => circularConnectionMat4 (witnessCircularField z ρ)
    let A_full : FourSpace → Fin 4 → Mat4C :=
      fun z ρ => U * A z ρ * U⁻¹ + mannheimGaugeShiftMat4 β α z ρ
    let Φ_conj : FourSpace → Mat4C := fun _ => U * (1 : Mat4C) * U⁻¹
    let cone := CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C
    let ι := diagTowerStarHom 0
    let ψ : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C :=
      (cone.toColimit 0).toRingHom.comp ι.toRingHom
    Tendsto (fun a => ψ (latticeCovariantDiff A_full Φ_conj y 0 a))
      (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCovariantDeriv A (fun _ => 1) y 0) * ψ U⁻¹)) ∧
    Tendsto (fun a => ψ ((a ^ 2)⁻¹ • (wilsonPlaquette A_full y 0 1 a - 1)))
      (𝓝[≠] 0) (𝓝 (ψ U * ψ (continuumCurvature A y 0 1) * ψ U⁻¹)) ∧
    Tendsto (fun a => ψ (U * circularLinkTransport witnessCircularField y 0 a * U⁻¹))
      (𝓝 0) (𝓝 1) ∧
    Tendsto (fun a => ψ (a⁻¹ • (U * circularLinkTransport witnessCircularField y 0 a * U⁻¹ - 1)))
      (𝓝[≠] 0) (𝓝 (ψ U * ψ (circularConnectionMat4 (witnessCircularField y 0)) * ψ U⁻¹)) := by
  intro β α U A A_full Φ_conj cone ι ψ
  have hA : ContDiff ℝ 2 A := by
    have hEq : A = fun _ ρ => circularConnectionMat4 (witnessCircularField 0 ρ) := rfl
    rw [hEq]
    exact contDiff_const
  have h := mannheim_lattice_continuum_gauge_covariance.{0, 0} (1 / 2) (-(1 / 2)) β α
    coord0_contDiff coord1_contDiff
    witnessCircularField A hA (fun _ => 1) y (differentiableAt_const 1) 0 1
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 cone 0 ι tailTower_cont_zero

end Layer2BoundarySection

section Layer3BoundarySection

open scoped Matrix.Norms.Elementwise

/-- T2-F12-05: General `ymCurvature`, `covExtDeriv`, and PDE invariance for arbitrary differentiable `A`. -/
theorem t2_f12_05_general_ymCurvature_pde_invariance
    (w : ℝ) (β α : FourSpace → ℝ) (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α)
    (A : Mat4CForm 1) (hA : Differentiable ℝ A) {k : ℕ} (η : Mat4CForm k) :
    ymCurvature (A - mannheimGradOneForm w β α) = ymCurvature A ∧
    covExtDeriv (A - mannheimGradOneForm w β α) η = covExtDeriv A η := by
  have h := mannheim_ymCurvature_and_pde_invariance w β α hβ hα A hA
  exact ⟨h.1, h.2.1 η⟩

end Layer3BoundarySection

/-! ### F13 Boundary Cases (5 Tier 2 Cases) -/

/-- T2-F13-01: Comparison of spinor `2π` (`-1`), chiral gauge `α = π` (`-1`), and `2π` (`+1`). -/
theorem t2_f13_01_r1_2pi_vs_4pi_vs_chiral_phase :
    spinHalfSU2Rot ![0, 0, 1] (2 * Real.pi) = -1 ∧
    mannheimChiralGaugeMat4 0 Real.pi = (-1 : Matrix (Fin 4) (Fin 4) ℂ) ∧
    mannheimChiralGaugeMat4 0 (2 * Real.pi) = 1 := by
  have hn : IsUnitAxis ![0, 0, 1] := by unfold IsUnitAxis; simp
  refine ⟨(spinHalfSU2Rot_two_pi hn).1, ?_, ?_⟩
  · have hpi : scaleGaugeMultiplier 0 Real.pi = -1 := by
      simp [scaleGaugeMultiplier, Complex.exp_pi_mul_I]
    have hnpi : scaleGaugeMultiplier 0 (-Real.pi) = -1 := by
      simp [scaleGaugeMultiplier, Complex.exp_neg, Complex.exp_pi_mul_I]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mannheimChiralGaugeMat4, chiralDiagBlock4, hpi, hnpi]
  · have h2pi : scaleGaugeMultiplier 0 (2 * Real.pi) = 1 := by
      simp [scaleGaugeMultiplier, Complex.exp_two_pi_mul_I]
    have hn2pi : scaleGaugeMultiplier 0 (-(2 * Real.pi)) = 1 := by
      simp [scaleGaugeMultiplier, Complex.exp_neg, Complex.exp_two_pi_mul_I]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mannheimChiralGaugeMat4, chiralDiagBlock4, h2pi, hn2pi]

/-- T2-F13-02: Zero-redshift `d_L(0) = 0` paired with zero-scale/zero-phase identity gauge. -/
theorem t2_f13_02_r3_zero_redshift_vs_zero_beta (c H₀ q₀ : ℝ) :
    conformalLuminosityDist c H₀ q₀ 0 = 0 ∧
    mannheimChiralGaugeMat4 0 0 = 1 :=
  ⟨conformalLuminosityDist_zero c H₀ q₀, mannheimChiralGaugeMat4_zero⟩

/-- T2-F13-03: R4 critical scaling `γ = -1` matched with R5 quartic scalar invariance `vol4Scale * confScalarScale^4 = 1`. -/
theorem t2_f13_03_r4_scale_invariant_gamma_neg_one_vs_quartic (β : ℝ) :
    fourFermionDim (-1) = 4 ∧
    dressedBilinearDim (-1) = 2 ∧
    vol4Scale β * (confScalarScale β) ^ 4 = 1 :=
  ⟨(anomalous_dim_uv_integrability_trichotomy.1 (-1)).mpr rfl,
   by unfold dressedBilinearDim; norm_num,
   (mannheim_witt_krein_conformal_scaling β 0 (coordinateEquiv uPlus) 0 0 0 0 0 0 0 0).2.2.2.2.2.2.2.2⟩

/-- T2-F13-04: Cross-module import smoke uniting all 5 existing Mannheim owners and all 5 new R1–R5 owners. -/
theorem t2_f13_04_r5_e2e_dual_lane_import_smoke :
    cowPhaseShift 1 2 1 1 1 = -2 ∧
    propPhaseDiff 1 2 2 1 = 0 ∧
    conformalLuminosityDist 1 1 (-1 / 2) 0 = 0 ∧
    dressedBilinearDim (-1) = 2 ∧
    mannheimChiralGaugeMat4 0 0 = 1 ∧
    vol4Scale 0 = 1 ∧
    njlInvPropagatorP 1 1 0 0 = 0 ∧
    dynamicalDoubleWell 1 1 = -(1 / 2 : ℝ) ∧
    (conjPoleLorentzC 1 1 1).re = 1 ∧
    fisherLeaflet 0 = 1 := by
  refine ⟨by rw [cowPhaseShift_eq]; norm_num,
    by unfold propPhaseDiff; norm_num,
    conformalLuminosityDist_zero 1 1 (-1 / 2),
    by unfold dressedBilinearDim; norm_num,
    mannheimChiralGaugeMat4_zero,
    by simp [vol4Scale],
    ?_, ?_, ?_, ?_⟩
  · unfold njlInvPropagatorP njlPseudoscalarPolarization; norm_num
  · unfold dynamicalDoubleWell; norm_num
  · unfold conjPoleLorentzC; norm_num
  · rw [fisherLeaflet_formula]; norm_num

section Layer3HodgeBoundarySection

open scoped Matrix.Norms.Elementwise

/-- T2-F13-05: Shifted Euclidean instanton is self-dual while shifted Lorentzian wave solves Minkowski YM PDE. -/
theorem t2_f13_05_euclidean_vs_minkowski_hodge_dual_shifted :
    let β : FourSpace → ℝ := fun z => z 0
    let α : FourSpace → ℝ := fun z => z 2
    let f : ℝ → ℝ := fun _ => 1
    IsSelfDualForm4 (circularGaugeForm - mannheimGradOneForm 1 β α) ∧
    YangMillsPDEMinkowski (circularMinkowskiWaveForm f - mannheimGradOneForm 1 β α) := by
  intro β α f
  let proj0 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj2 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := mannheim_shifted_circularGaugeForm_and_waveForm_solutions 1 β α
    proj0.contDiff proj2.contDiff (f := f) contDiff_const (by norm_num)
  exact ⟨h.1.2.1, h.2.2⟩

end Layer3HodgeBoundarySection

/-! ## Tier 3: Pairwise Cross-Feature & Separation Tests (9 Cases) -/

/-- T3-01 (F1 + F2 + Zitterbewegung): Joint mass-independence of classical free fall vs mass-separation of COW, de Broglie, and Compton. -/
theorem t3_01_cow_deBroglie_compton_chain :
    classicalFreeFallAccel 1 1 10 = classicalFreeFallAccel 2 2 10 ∧
    cowPhaseShift 1 10 3 1 5 ≠ cowPhaseShift 2 10 3 1 5 ∧
    deBroglieWavelength 1 1 5 * comptonFrequency 1 3 1 = 2 * 3 ^ 2 / 5 ∧
    cowPhaseShift 1 10 3 1 5 = -(comptonFrequency 1 3 1 * 10 * 3 ^ 2) / (2 * 3 ^ 2 * 5) :=
  ⟨(classical_free_fall_mass_independent_vs_cow_mass_dependent 1 2 10 3 5 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).1,
   (classical_free_fall_mass_independent_vs_cow_mass_dependent 1 2 10 3 5 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)).2.2,
   deBroglieWavelength_mul_comptonFrequency 1 1 5 3 (by norm_num) (by norm_num),
   cowPhaseShift_eq_comptonFrequency 1 10 3 1 5 3 (by norm_num) (by norm_num)⟩

/-- T3-02 (F3 + T16 Pauli): Orthogonal π-rotations in `SU(2)` do not commute, square to `-1`, and 4th power to `+1`. -/
theorem t3_02_su2_noncomm_orthogonal_axes_and_4pi :
    let U1 := spinHalfSU2Rot ![1, 0, 0] Real.pi
    let U2 := spinHalfSU2Rot ![0, 1, 0] Real.pi
    U1 * U2 ≠ U2 * U1 ∧
    U1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    U2 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    U1 * U1 = -1 ∧
    (U1 * U1) * (U1 * U1) = 1 := by
  intro U1 U2
  have hn1 : IsUnitAxis ![1, 0, 0] := by unfold IsUnitAxis; simp
  have hn2 : IsUnitAxis ![0, 1, 0] := by unfold IsUnitAxis; simp
  have hU1 : U1 = -Complex.I • σ1 := by
    dsimp [U1]
    rw [spinHalfSU2Rot_euler hn1 Real.pi]
    simp only [Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul, zero_sub,
      Real.sin_pi_div_two, Complex.ofReal_one, mul_one]
    have hp : pauliDir ![1, 0, 0] = σ1 := by unfold pauliDir; simp
    rw [hp, neg_smul]
  have hU2 : U2 = -Complex.I • σ2 := by
    dsimp [U2]
    rw [spinHalfSU2Rot_euler hn2 Real.pi]
    simp only [Real.cos_pi_div_two, Complex.ofReal_zero, zero_smul, zero_sub,
      Real.sin_pi_div_two, Complex.ofReal_one, mul_one]
    have hp : pauliDir ![0, 1, 0] = σ2 := by unfold pauliDir; simp
    rw [hp, neg_smul]
  have hNoncomm : U1 * U2 ≠ U2 * U1 := by
    rw [hU1, hU2]
    intro heq
    apply pauli_noncomm_witness
    have hmul : ((-Complex.I : ℂ) * (-Complex.I)) • (σ1 * σ2) =
        ((-Complex.I : ℂ) * (-Complex.I)) • (σ2 * σ1) := by
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul] using heq
    have hscalar : (-Complex.I : ℂ) * (-Complex.I) = -1 := by
      calc
        (-Complex.I : ℂ) * (-Complex.I) = Complex.I * Complex.I := neg_mul_neg _ _
        _ = -1 := Complex.I_mul_I
    rw [hscalar, neg_one_smul, neg_one_smul] at hmul
    exact neg_inj.mp hmul
  have hSq : U1 * U1 = -1 := by
    dsimp [U1]
    rw [← spinHalfSU2Rot_add, show Real.pi + Real.pi = 2 * Real.pi by ring]
    exact (spinHalfSU2Rot_two_pi hn1).1
  have hQuad : (U1 * U1) * (U1 * U1) = 1 := by
    rw [hSq]
    norm_num
  exact ⟨hNoncomm,
    (spinHalfSU2Rot_unitary_and_det_one hn1 Real.pi).2.2.2,
    (spinHalfSU2Rot_unitary_and_det_one hn2 Real.pi).2.2.2,
    hSq, hQuad⟩

/-- T3-03 (F4 + F5 + Penrose + Bloch–Umegaki): Concrete double-slit bridge unifying nullity, cutoff, leaflet, and `gramBlochState`. -/
theorem t3_03_doubleSlit_null_leaflet_bloch_umegaki :
    let W := twoSlitInterferometerOp 2
    let ρ := gramBlochState W
    IsMinkowskiNull (slitRayDisplacement 2 4 8) ∧
    (5 : ℝ) ^ 2 * minkowskiNorm (slitRayDisplacement 2 4 8) = 0 ∧
    coherenceVisibility 3 (8 / 2) = 0 ∧
    0 < fisherLeaflet (8 / (2 * 3)) ∧
    gramBlochState (scaleGaugeMultiplier 1 2 • W) = ρ ∧
    0 ≤ quantumUmegakiGibbs ρ 1 := by
  have hB := doubleSlit_null_ray_and_leaflet_bridge
  have hNull := hB.1 2 1 2 4 8 5 (by norm_num) (by norm_num) (by norm_num)
  have hCut := (hB.2.2.2.1 2 3 1 4 1 (by norm_num) (by norm_num)).2.2.2.2.2.1 8 (by norm_num)
  have hBloch := hB.2.2.2.2 2 1 2 1 1 3 1 2 2 0 (by norm_num)
    (by unfold totalSlitPhaseDiff propPhaseDiff sourcePhaseDiff; norm_num)
  exact ⟨hNull.1, hNull.2.2.1, hCut.1, hCut.2.2.1, hBloch.2.2.1, hBloch.2.2.2.2.2.2.2.1⟩

/-- T3-04 (F6 + F7 + F8 + Friedmann): Constructive open Friedmann cosmology drives luminosity distance, Taylor acceleration, and diverging horizon. -/
theorem t3_04_friedmann_luminosity_and_horizon :
    let H₀ := mannheimHubble 1 2 (-1) 2
    let q₀ := mannheimDeceleration 1 2 (-1) 2
    0 < H₀ ∧
    q₀ ∈ Set.Ioo (-1 : ℝ) 0 ∧
    conformalLuminosityDist 1 H₀ q₀ 0 = 0 ∧
    0 < conformalLuminosityDist 1 H₀ q₀ 1 ∧
    deriv (conformalLuminosityDist 1 H₀ q₀) 0 = 1 / H₀ ∧
    deriv (deriv (conformalLuminosityDist 1 H₀ q₀)) 0 = (1 / H₀) * (1 - q₀) ∧
    1 / H₀ < (1 / H₀) * (1 - q₀) ∧
    Tendsto (fun t_i => conformalHorizon 1 1 2 (-1) t_i 2) (𝓝[>] 0) Filter.atTop := by
  have h := mannheim_friedmann_luminosity_horizon_instantiation
    (c := 1) (S₀ := 1) (lam := 2) (k := -1) (t := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1, h.2.2.2.1, (h.2.2.2.2.1 1 (by norm_num)).2,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- T3-05 (F9 + F10 + NJL + PT): Marginal `γ = -1` double well paired with above-threshold dynamical Higgs resonance and NJL zero. -/
theorem t3_05_critical_double_well_njl_pt_resonance :
    DoubleWellShape 1 (mannheimCriticalPotential (-1) 1 1 1) ∧
    (∀ m : ℝ, m ≠ 0 →
      Tendsto (fun Λ : ℝ => renormalizedFermionPotential Λ 1 m) Filter.atTop
        (nhds (mannheimCriticalPotential (-1) 1 1 1 m))) ∧
    ∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      (((3 ^ 2 : ℝ) : ℂ) - Complex.I * ((3 * Γ_dyn : ℝ) : ℂ)).im < 0 ∧
      njlDressedInvPropagatorS 1 1 2 1 (4 * 1 ^ 2 - 3 ^ 2) (3 ^ 2) = 0 ∧
      0 < deriv (breitWignerPhase (3 ^ 2) (3 * Γ_dyn)) 5 := by
  have h9 := mannheim_anomalous_dimension_potential_trichotomy.2.1 1 1 1 (by norm_num)
  obtain ⟨Γ_dyn, hΓ, _, _, _, _, hPole, hNJL, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
      (g := 1) (Z_H := 1) (M_H := 3) (c_ps := 1) (m := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h9.1, h9.2, Γ_dyn, hΓ, hPole.1,
    (hNJL 1 2 (3 ^ 2) (by norm_num) (by norm_num)).2.1.mpr rfl,
    (hPole.2.2.2 5).2.2.2⟩

section Tier3Layer23Section

open scoped Matrix.Norms.Elementwise

/-- T3-06 (R2/R3 + R5 Layers 0, 1, 3): Unified scale–phase covariance across Bloch, graded exterior, and 4D manifold YM sectors. -/
theorem t3_06_r5_scale_phase_unification_across_layers
    (β α : FourSpace → ℝ) (hβ : ContDiff ℝ 2 β) (hα : ContDiff ℝ 2 α)
    (x : Coordinate) (y : FourSpace) :
    gramBlochState (scaleGaugeMultiplier (β y) (α y) • weylUpperMat x) = gramBlochState (weylUpperMat x) ∧
    MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularEvenOmega x)) ∧
    ymCurvature (circularGaugeForm - mannheimGradOneForm 1 β α) = ymCurvature circularGaugeForm := by
  have h0 := (mannheim_weyl_bloch_scale_gauge_invariance (β y) (α y) x 0).2.1
  have h1 := (mannheim_graded_even_compat_preserved 0 0 0 0 x).2.2.2.2.2.2.2.1
  have h1' : MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularEvenOmega x)) := by
    have hU : (chiralDiagBlock4
        (scaleGaugeMultiplier 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        (scaleGaugeMultiplier 0 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ))).map
        (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4, scaleGaugeMultiplier_zero]
    simpa [hU] using h1
  have h3 := (mannheim_ymCurvature_and_pde_invariance 1 β α hβ hα circularGaugeForm
    (circularGaugeForm_contDiff.differentiable (by norm_num))).1
  exact ⟨h0, h1', h3⟩

end Tier3Layer23Section

/-- T3-F11 (Non-vacuity / separation): Nonzero chiral vorticity drives a strictly positive curvature and action gap. -/
theorem t3_f11_vorticity_gap_strict_pos :
    let x := coordinateEquiv (frame 1 + frame 6)
    let Uα := mannheimChiralGaugeMat4 0 0.7
    let A_g := Uα * circularConnectionMat4 (Real.exp 0.5 • x) * Uαᴴ
    let F_g := A_g * A_g
    F_g ≠ 0 ∧ (F_gᴴ * F_g).trace ≠ (F_g * F_g).trace := by
  intro x Uα A_g F_g
  have h := mannheim_chiral_phase_curvature_action_covariant 0.5 0.7 x
    (CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C) 0 (diagTowerStarHom 0)
  have hx : x = Pi.single 1 1 + Pi.single 6 1 := by
    change coordinateEquiv (frame 1 + frame 6) = Pi.single 1 1 + Pi.single 6 1
    rw [map_add, coordinateEquiv_apply_frame 1, coordinateEquiv_apply_frame 6]
  have hVort : 0 < normSq3 (chiralVorticityVec x) := by
    have hvec : chiralVorticityVec x = ![0, 0, 1] := by
      ext i
      fin_cases i <;> simp [chiralVorticityVec, hx]
    rw [hvec]
    simp [normSq3]
  have hGapPos : 0 < 8 * vol4Scale 0.5 * normSq3 (chiralVorticityVec x) := by
    have hv : 0 < vol4Scale 0.5 := Real.exp_pos _
    positivity
  have hTrNe : (F_gᴴ * F_g).trace ≠ (F_g * F_g).trace := by
    intro heq
    have hdiff := h.2.2.2.2.2.2.1.1
    rw [heq, sub_self] at hdiff
    have hR : (0 : ℝ) = 8 * vol4Scale 0.5 * normSq3 (chiralVorticityVec x) := by
      exact Complex.ofReal_injective hdiff
    linarith
  have hFne : F_g ≠ 0 := by
    intro h0
    apply hTrNe
    simp [h0]
  exact ⟨hFne, hTrNe⟩

/-- T3-F12 (Separation): `circularEvenOmega` is homogeneous degree-1 while `circularGradedOmega` contains a nonzero 2-form blade and fails `MatrixIsHomogeneous 1`. -/
theorem t3_f12_even_vs_graded_omega_separation :
    let x := coordinateEquiv uPlus
    MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularEvenOmega x)) ∧
    blade2Coeff 0 1 uPlusForm = 1 ∧
    ¬ MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularGradedOmega x)) := by
  intro x
  have hEven : MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularEvenOmega x)) :=
    (mannheim_even_oneForm_abelian_shift circularEvenDiff x 0
      (Submodule.zero_mem _)).1 |> fun h => by
      simpa using h
  have hb2 : blade2Coeff 0 1 uPlusForm = 1 := by
    unfold uPlusForm
    have h01 := (blade2Coeff_eval 0 1 0 1 0).1
    have h1 := (blade2Coeff_eval 0 1 1 0 0).2.1
    change blade2Coeff 0 1 (extBasisOneForm 0 * extBasisOneForm 1 + extBasisOneForm 1) = 1
    rw [map_add, h01, h1]
    norm_num
  have hNotHom : ¬ MatrixIsHomogeneous 1 (circularGaugeConnection4 (circularGradedOmega x)) := by
    intro hHom
    have h02Hom := hHom 0 2
    obtain ⟨v, hv⟩ := (homogeneous_one_iff_exists_generator _).mp h02Hom
    have hx0 : x = Pi.single 0 1 := by
      change coordinateEquiv (frame 0) = Pi.single 0 1
      exact coordinateEquiv_apply_frame 0
    have hω : ∀ i : Fin 8, circularGradedOmega x i = if i = 0 then uPlusForm else 0 := by
      intro i
      fin_cases i <;> simp [circularGradedOmega, hx0]
    have h02 : circularGaugeConnection4 (circularGradedOmega x) 0 2 = uPlusForm := by
      simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 1, hω 2, hω 3]
    rw [h02] at hv
    have hb_zero : blade2Coeff 0 1 (ExteriorAlgebra.ι ℂ v) = 0 := by
      have hv_sum : v = ∑ c : Fin 4, v c • Pi.single c (1 : ℂ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [hv_sum, map_sum]
      simp only [map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro c _
      have hb_c : blade2Coeff 0 1 (ExteriorAlgebra.ι ℂ (Pi.single c (1 : ℂ))) = 0 :=
        (blade2Coeff_eval 0 1 c 0 0).2.1
      rw [hb_c, smul_zero]
    rw [hv, hb2] at hb_zero
    exact one_ne_zero hb_zero
  exact ⟨hEven, hb2, hNotHom⟩

section Tier3Layer3SepSection

open scoped Matrix.Norms.Elementwise

/-- T3-F13 (Separation): Non-Abelian `ymCurvature` survives non-constant Mannheim `(β, α)` gauge shifts in both Euclidean and Minkowski signatures. -/
theorem t3_f13_nonabelian_curvature_survives_shift :
    let β : FourSpace → ℝ := fun z => z 0 ^ 2 + z 1
    let α : FourSpace → ℝ := fun z => z 2 * z 3 - z 0
    let f : ℝ → ℝ := fun s => Real.cos s + 2
    ymCurvature (circularGaugeForm - mannheimGradOneForm 1 β α) ≠ 0 ∧
    ymCurvature (circularMinkowskiWaveForm f - mannheimGradOneForm 1 β α) ≠ 0 := by
  intro β α f
  let proj0 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj1 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj2 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 2, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let proj3 : FourSpace →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun z => z 3, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hβ : ContDiff ℝ 2 β := (proj0.contDiff.pow 2).add proj1.contDiff
  have hα : ContDiff ℝ 2 α := (proj2.contDiff.mul proj3.contDiff).sub proj0.contDiff
  have hf : ContDiff ℝ 2 f := Real.contDiff_cos.add contDiff_const
  have hf0 : f 0 ≠ 0 := by simp [f]; norm_num
  have h := mannheim_shifted_circularGaugeForm_and_waveForm_solutions 1 β α hβ hα hf hf0
  exact ⟨h.1.1, h.2.1⟩

end Tier3Layer3SepSection

/-! ## Tier 4: Real-World End-to-End Scenarios (4 High-Complexity Scenarios) -/

/-- T4-01 (End-to-End R1): Neutron vs heavy test mass in a square COW interferometer coupled to $4\pi$ `SU(2)` magnetic precession. -/
theorem t4_01_cow_neutron_interferometry_and_4pi_spinor_experiment
    (m₁ m₂ g H v hbar c : ℝ) (n : Fin 3 → ℝ)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hm_ne : m₁ ≠ m₂)
    (hg : g ≠ 0) (hH : H ≠ 0) (hv : v ≠ 0) (hhbar : hbar ≠ 0) (hc : c ≠ 0)
    (hn : IsUnitAxis n) (θ : ℝ) :
    classicalFreeFallAccel m₁ m₁ g = classicalFreeFallAccel m₂ m₂ g ∧
    cowSquareActionDiff m₁ g H v ≠ cowSquareActionDiff m₂ g H v ∧
    cowPhaseShift m₁ g H hbar v ≠ cowPhaseShift m₂ g H hbar v ∧
    (deBroglieWavelength hbar m₁ v = deBroglieWavelength hbar m₂ v ↔ m₁ = m₂) ∧
    (comptonFrequency m₁ c hbar = comptonFrequency m₂ c hbar ↔ m₁ = m₂) ∧
    spinHalfSU2Rot n θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
    spinHalfSU2Rot n (θ + 2 * Real.pi) = -spinHalfSU2Rot n θ ∧
    spinHalfSU2Rot n (θ + 4 * Real.pi) = spinHalfSU2Rot n θ ∧
    spinHalfSU2Rot n (2 * Real.pi) = -1 ∧
    spinHalfSU2Rot n (2 * Real.pi) ≠ 1 ∧
    spinHalfSU2Rot n (4 * Real.pi) = 1 ∧
    σ1 * σ2 ≠ σ2 * σ1 := by
  have hCOW := classical_free_fall_mass_independent_vs_cow_mass_dependent
    m₁ m₂ g H v hbar hm₁ hm₂ hm_ne hg hH hv hhbar
  have hEquiv := quantum_equivalence_deBroglie_compton_iff hbar m₁ m₂ v c hhbar hv hc
  have hSU2 := spinHalfSU2Rot_unitary_and_det_one hn θ
  have h2pi := spinHalfSU2Rot_two_pi hn
  exact ⟨hCOW.1, hCOW.2.1, hCOW.2.2, hEquiv.1, hEquiv.2.1, hSU2.2.2.2,
    spinHalfSU2Rot_add_two_pi hn θ, spinHalfSU2Rot_add_four_pi hn θ,
    h2pi.1, h2pi.2, spinHalfSU2Rot_four_pi hn, pauli_noncomm_witness⟩

/-- T4-02 (End-to-End R2): Broadband vs monochromatic double-slit interferometer unifying null rays, source phase restoration, coherence cutoff, and Bloch–Umegaki positivity. -/
theorem t4_02_broadband_vs_monochromatic_double_slit_experiment
    (c τ_coh k ω ΔL Δt I₀ Ω β α θ : ℝ)
    (hc : 0 < c) (hτ : 0 < τ_coh) (hΩ : 0 < Ω) (hI₀ : 0 ≤ I₀)
    (h_light : ΔL = c * Δt) (h_disp : ω = c * k) :
    let dx := slitRayDisplacement c Δt ΔL
    let Δt_src := ΔL / c
    let W := twoSlitInterferometerOp (totalSlitPhaseDiff k ω ΔL Δt 0)
    let ρ := gramBlochState W
    propPhaseDiff k ω ΔL Δt = 0 ∧
    IsMinkowskiNull dx ∧
    (pauliSoldering dx).det = 0 ∧
    Ω ^ 2 * minkowskiNorm dx = 0 ∧
    totalSlitPhaseDiff k ω ΔL Δt Δt_src = k * ΔL ∧
    (IsWithinCoherenceWindow τ_coh Δt_src ↔ |ΔL| ≤ c * τ_coh) ∧
    (0 < coherenceVisibility τ_coh Δt_src ↔ |ΔL| < c * τ_coh) ∧
    (c * τ_coh < |ΔL| →
      coherenceVisibility τ_coh Δt_src = 0 ∧
      twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src = 2 * I₀ ∧
      0 < fisherLeaflet (ΔL / (c * τ_coh)) ∧
      fisherLeaflet (ΔL / (c * τ_coh)) < 1) ∧
    0 ≤ twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ∧
    twoSlitIntensity I₀ τ_coh k ω ΔL Δt Δt_src ≤ 4 * I₀ ∧
    Wᴴ * W = 1 ∧
    gramBlochState (scaleGaugeMultiplier β α • W) = ρ ∧
    0 ≤ quantumUmegakiGibbs ρ θ := by
  have hEq := equal_emission_phase_cancellation c k ω ΔL Δt h_light h_disp
  have hRest := earlier_emission_phase_restoration c k ω ΔL Δt (ΔL / c) hc.ne' h_light h_disp rfl
  have hCut := coherence_window_and_fringe_cutoff c τ_coh ΔL (ΔL / c) I₀ k ω Δt hc hτ rfl
  have hBr := doubleSlit_null_ray_and_leaflet_bridge
  have hNull := hBr.1 c k ω Δt ΔL Ω h_light h_disp hΩ
  have hLeaf := (hBr.2.2.2.1 c τ_coh k Δt I₀ hc hτ).2.2.2.2.2.1
  have hBloch := hBr.2.2.2.2 (totalSlitPhaseDiff k ω ΔL Δt 0) β α θ I₀ τ_coh k ω ΔL Δt hτ rfl
  exact ⟨hEq.1, hEq.2.2.1, hEq.2.2.2.1, hNull.2.2.1, hRest.2.2.1,
    hCut.1, hCut.2.2.1,
    fun hfar => ⟨(hLeaf ΔL hfar).1, (hCut.2.2.2.1 hfar).2.2, (hLeaf ΔL hfar).2.2.1,
      (hLeaf ΔL hfar).2.2.2⟩,
    (hCut.2.2.2.2 hI₀).1, (hCut.2.2.2.2 hI₀).2,
    hBloch.1, hBloch.2.2.1, hBloch.2.2.2.2.2.2.2.1⟩

/-- T4-03 (End-to-End R3): Constructive open Friedmann cosmology linked to SNIa $d_L(z)$ Taylor expansion and BBN/CMB horizon-free growth ratios. -/
theorem t4_03_conformal_cosmology_snia_bbn_cmb_scenario
    (c S₀ lam k t t₁ t₂ T₁ T₂ : ℝ)
    (hc : 0 < c) (hS : S₀ ≠ 0) (hlam : 0 < lam) (hk : k < 0) (ht : 0 < t)
    (ht₁ : 0 < t₁) (ht₁₂ : t₁ < t₂) (hT₂ : 0 < T₂) (hT₁₂ : T₂ < T₁) :
    let H₀ := mannheimHubble S₀ lam k t
    let q₀ := mannheimDeceleration S₀ lam k t
    0 < H₀ ∧
    q₀ ∈ Set.Ioo (-1 : ℝ) 0 ∧
    conformalLuminosityDist c H₀ q₀ 0 = 0 ∧
    (∀ z : ℝ, 0 < z → 0 < conformalLuminosityDist c H₀ q₀ z) ∧
    deriv (conformalLuminosityDist c H₀ q₀) 0 = c / H₀ ∧
    deriv (deriv (conformalLuminosityDist c H₀ q₀)) 0 = (c / H₀) * (1 - q₀) ∧
    c / H₀ < (c / H₀) * (1 - q₀) ∧
    Tendsto (fun t_i => conformalHorizon c S₀ lam k t_i t) (𝓝[>] 0) Filter.atTop ∧
    einsteinPowerHorizon c (1 / 2) 0 t ≤ c * t ^ (1 - 1 / 2 : ℝ) / (1 - 1 / 2 : ℝ) ∧
    t₂ / t₁ < mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ ∧
    (mannheimScaleFactor S₀ lam k t₂ / mannheimScaleFactor S₀ lam k t₁ = T₁ / T₂ →
      t₂ / t₁ < T₁ / T₂ ∧ t₂ / t₁ < (T₁ / T₂) ^ 2) := by
  have hInst := mannheim_friedmann_luminosity_horizon_instantiation hc hS hlam hk ht
  have hEin := einsteinPowerHorizon_bounded (c := c) (p := 1 / 2) (t_i := 0) (t := t)
    hc.le (by norm_num) (by norm_num) le_rfl ht.le
  have hRat := conformal_vs_standard_nucleosynthesis_and_planck_ratios
    (S₀ := S₀) (lam := lam) (k := k) (t₁ := t₁) (t₂ := t₂) (T₁ := T₁) (T₂ := T₂)
    hS hlam hk ht₁ ht₁₂ hT₂ hT₁₂
  exact ⟨hInst.1, hInst.2.1, hInst.2.2.2.1, fun z hz => (hInst.2.2.2.2.1 z hz).2,
    hInst.2.2.2.2.2.1, hInst.2.2.2.2.2.2.2.1, hInst.2.2.2.2.2.2.2.2.2.1,
    hInst.2.2.2.2.2.2.2.2.2.2.2, hEin.2.2.1, hRat.1, hRat.2.2.2.2.1⟩

/-- T4-04 (End-to-End R4 + R5): Johnson–Baker–Willey anomalous dimension trichotomy, dynamical bound-state Higgs width vs elementary zero width, and R5 Dirac conformal weight compensation. -/
theorem t4_04_conformal_dynamical_ewsb_and_higgs_resonance_scenario
    (M c₂ c₄ g Z_H M_H c_ps m : ℝ)
    (hM : 0 < M) (hc₂ : 0 < c₂) (hc₄ : 0 < c₄)
    (hg : 0 < g) (hZ : 0 < Z_H) (hcps : 0 < c_ps) (hm : 0 < m) (hMH : 2 * m < M_H) :
    (fourFermionDim (-1) = 4) ∧
    SingleWellShape (mannheimCriticalPotential (-1 / 2) M c₂ c₄) ∧
    DoubleWellShape M (mannheimCriticalPotential (-1) M c₂ c₄) ∧
    UpsideDownShape (mannheimCriticalPotential (-2) M c₂ c₄) ∧
    (∃ Γ_dyn : ℝ, 0 < Γ_dyn ∧
      (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m (M_H ^ 2)).im = M_H * Γ_dyn ∧
      (((M_H ^ 2 : ℝ) : ℂ) - Complex.I * ((M_H * Γ_dyn : ℝ) : ℂ)).im < 0 ∧
      (∀ qSq : ℝ, qSq ≤ 4 * m ^ 2 →
        (dynamicalHiggsComplexInvProp g Z_H M_H c_ps m qSq).im = 0) ∧
      (∀ Igap Jq : ℝ, 0 < Jq → g * Igap = 1 →
        njlDressedInvPropagatorS g Igap Jq m (4 * m ^ 2 - M_H ^ 2) (M_H ^ 2) = 0) ∧
      (∀ qSq : ℝ, (elementaryHiggsInvProp M_H qSq).im = 0)) ∧
    (∀ (β α : FourSpace → ℝ) (x : FourSpace) (u v : ChiralFiber),
      vol4Scale (β x) * invTetradScale (β x) *
        fiberKreinPairing (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • u)
          (mannheimFiberScalar (-(3 / 2 : ℝ)) β α x • v) = fiberKreinPairing u v) := by
  have hTri := mannheim_anomalous_dimension_potential_trichotomy
  obtain ⟨Γ_dyn, hΓ, _, _, hIm, hBelow, hPole, hNJL, hElem, _⟩ :=
    dynamical_higgs_above_threshold_positive_width_vs_elementary_zero hg hZ hcps hm hMH
  refine ⟨(anomalous_dim_uv_integrability_trichotomy.1 (-1)).mpr rfl,
    hTri.1 (-1 / 2) M c₂ c₄ (by norm_num) (by norm_num) hc₂ hc₄,
    (hTri.2.1 M c₂ c₄ hM).1,
    hTri.2.2.1 M c₂ c₄ hc₄,
    ⟨Γ_dyn, hΓ, hIm, hPole.1, hBelow,
      fun Igap Jq hJq hgI => (hNJL Igap Jq (M_H ^ 2) hJq hgI).2.1.mpr rfl,
      fun qSq => (hElem qSq).1⟩,
    fun β α x u v => ((mannheim_fiberKreinPairing_scale_phase_law (-(3 / 2 : ℝ)) β α x u v).2.2.2 rfl).2⟩

/-! ## Trust & Axiom Hygiene Audits (`collectHardEvidenceBatch` + `#print axioms`) -/

private def e2eAuditDecls : Array Name :=
  #[ -- R1 (`MannheimCOWAndSpinorPrecession`)
     ``cowSquareActionDiff_eq
   , ``cowPhaseShift_eq
   , ``classical_free_fall_mass_independent_vs_cow_mass_dependent
   , ``quantum_equivalence_deBroglie_iff
   , ``quantum_equivalence_deBroglie_compton_iff
   , ``cowPhaseShift_eq_comptonFrequency
   , ``pauli_noncomm_witness
   , ``pauli_mat2_noncomm_exists
   , ``spinHalfSU2Rot_euler
   , ``spinHalfSU2Rot_unitary_and_det_one
   , ``spinHalfSU2Rot_two_pi
   , ``spinHalfSU2Rot_four_pi
     -- R2 (`MannheimDoubleSlitSpacetimeCoherence`)
   , ``equal_emission_phase_cancellation
   , ``earlier_emission_phase_restoration
   , ``coherence_window_and_fringe_cutoff
   , ``twoSlitInterferometerOp_unitary_and_det_ne_zero
   , ``twoSlitInterferometerOp_fringe_normSq
   , ``slitPhaseMatrix_pi_beamSplitter_ne
   , ``doubleSlit_matrix2_noncommutative
   , ``doubleSlit_null_ray_and_leaflet_bridge
     -- R3 (`MannheimConformalLuminosityHorizon`)
   , ``conformal_luminosity_mat2_noncomm_witness
   , ``conformalRadicand_pos
   , ``conformalLuminosityDist_pos
   , ``conformalLuminosityDist_deriv1_zero
   , ``conformalLuminosityDist_deriv2_zero
   , ``conformalHorizon_eq_and_tendsto_atTop
   , ``einsteinPowerHorizon_bounded
   , ``conformal_vs_standard_nucleosynthesis_and_planck_ratios
   , ``mannheim_friedmann_luminosity_horizon_instantiation
     -- R4 (`MannheimCriticalScalingAndHiggsWidth`)
   , ``anomalous_dim_uv_integrability_trichotomy
   , ``mannheim_anomalous_dimension_potential_trichotomy
   , ``scalarBubbleImPart_threshold_dichotomy
   , ``dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
     -- R5 (`MannheimDoubledMinkowskiYangMillsBridge`)
   , ``mannheim_circularConnection_mat4C_noncomm_witness
   , ``mannheim_weyl_mat2C_noncomm_witness
   , ``mannheim_mat4_exterior_noncomm_witness
   , ``mannheimChiralGaugeMat4_unitary_of_beta_zero
   , ``mannheim_witt_krein_conformal_scaling
   , ``mannheim_weyl_bloch_scale_gauge_invariance
   , ``mannheim_chiral_phase_curvature_action_covariant
   , ``mannheim_graded_even_compat_preserved
   , ``oneForm_abelian_shift_sq_invariant
   , ``mannheim_even_oneForm_abelian_shift
   , ``mannheimGaugeShiftMat4_contDiff
   , ``mannheim_lattice_continuum_gauge_covariance
   , ``mannheim_fiberKreinPairing_scale_phase_law
   , ``mannheim_bundle_covariant_derivative_4d
   , ``mannheim_ymCurvature_and_pde_invariance
   , ``mannheim_shifted_circularGaugeForm_and_waveForm_solutions
   , ``archMannheimDoubledMinkowskiYangMillsBridge
     -- E2E Tier 3 & Tier 4 witnesses
   , ``t3_f11_vorticity_gap_strict_pos
   , ``t3_f12_even_vs_graded_omega_separation
   , ``t3_f13_nonabelian_curvature_survives_shift
   , ``t4_01_cow_neutron_interferometry_and_4pi_spinor_experiment
   , ``t4_02_broadband_vs_monochromatic_double_slit_experiment
   , ``t4_03_conformal_cosmology_snia_bbn_cmb_scenario
   , ``t4_04_conformal_dynamical_ewsb_and_higgs_resonance_scenario ]

run_cmd do
  let policy := defaultPolicySnapshot
  let batch ← liftCoreM <| collectHardEvidenceBatch policy e2eAuditDecls
  for decl in e2eAuditDecls do
    let some ev := batch[decl]?
      | throwError "missing HardEvidence for {decl}"
    unless ev.forbiddenAxioms.isEmpty do
      throwError "forbidden axioms on {decl}: {ev.forbiddenAxioms}"
    if ev.hasSorryAx then
      throwError "unexpected incomplete-proof axiom dependency on {decl}"
    if ev.unsafeLeakage then
      throwError "unexpected unsafeLeakage on {decl}"
    if ev.repDepthViolation then
      throwError "unexpected repDepthViolation on {decl}"
    if ev.forbiddenRegionKind then
      throwError "unexpected forbiddenRegionKind on {decl}"

#print axioms classical_free_fall_mass_independent_vs_cow_mass_dependent
#print axioms spinHalfSU2Rot_two_pi
#print axioms spinHalfSU2Rot_four_pi
#print axioms equal_emission_phase_cancellation
#print axioms coherence_window_and_fringe_cutoff
#print axioms doubleSlit_null_ray_and_leaflet_bridge
#print axioms conformalLuminosityDist_deriv2_zero
#print axioms conformalHorizon_eq_and_tendsto_atTop
#print axioms mannheim_friedmann_luminosity_horizon_instantiation
#print axioms mannheim_anomalous_dimension_potential_trichotomy
#print axioms dynamical_higgs_above_threshold_positive_width_vs_elementary_zero
#print axioms mannheim_witt_krein_conformal_scaling
#print axioms mannheim_weyl_bloch_scale_gauge_invariance
#print axioms mannheim_chiral_phase_curvature_action_covariant
#print axioms mannheim_graded_even_compat_preserved
#print axioms mannheim_even_oneForm_abelian_shift
#print axioms mannheim_lattice_continuum_gauge_covariance
#print axioms mannheim_fiberKreinPairing_scale_phase_law
#print axioms mannheim_bundle_covariant_derivative_4d
#print axioms mannheim_ymCurvature_and_pde_invariance
#print axioms mannheim_shifted_circularGaugeForm_and_waveForm_solutions
#print axioms t4_01_cow_neutron_interferometry_and_4pi_spinor_experiment
#print axioms t4_02_broadband_vs_monochromatic_double_slit_experiment
#print axioms t4_03_conformal_cosmology_snia_bbn_cmb_scenario
#print axioms t4_04_conformal_dynamical_ewsb_and_higgs_resonance_scenario

end InfoGeometry.Synthesis.MannheimPart2E2ETest
