import InfoGeometry.Canonical.BipolarConformalLogos
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import InfoGeometry.Canonical.ApolloniusRapidityFlowBridge
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric

/-!
# Pristine bipolar mathematical chain

This owner records the branch-independent algebraic spine.  Physical
interpretations are intentionally downstream of these kernel-checked facts.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarPristineMathematicalChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.ApolloniusGradientCircularBridge
open InfoGeometry.Canonical.ApolloniusRapidityFlowBridge
open InfoGeometry.Topology.CanonicalRapidityAngleMetriplecticFlow
open InfoGeometry.Canonical.NegativeLogReadoutBridge
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge

theorem coordinate_differential_and_lift {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      dlog01 s = 1 / (s * (1 - s)) ∧
      Matrix.det (torusLift s) = 1 := by
  exact ⟨exp_bipolarLog hs, dlog01_eq_one_div_mul hs, torusLift_det hs⟩

theorem source_sink_exchange {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ ∧
      eta (1 - s) = -eta s ∧
      (-1 : ℂ) * dlog01 (1 - s) = -dlog01 s := by
  exact ⟨crossRatio01_one_sub hs, eta_one_sub hs, pullback_one_sub_dlog01 s⟩

theorem critical_line_logistic (y t : ℝ) :
    eta (criticalLine y) = 0 ∧
      ‖crossRatio01 (criticalLine y)‖ = 1 ∧
      0 < logistic t ∧ logistic t < 1 ∧
      crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
      eta (logistic t : ℂ) = t := by
  exact ⟨eta_criticalLine y, norm_crossRatio01_criticalLine y,
    logistic_pos t, logistic_lt_one t, crossRatio01_logistic t, eta_logistic t⟩

theorem reflection_and_boundary (s : ℂ) (y : ℝ) :
    crossRatio01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (crossRatio01 s) ∧
      dlog01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dlog01 s) ∧
      eta (criticalLine y) = 0 ∧
      ‖crossRatio01 (criticalLine y)‖ = 1 := by
  exact ⟨crossRatio01_conj s, dlog01_conj s,
    eta_criticalLine y, norm_crossRatio01_criticalLine y⟩

theorem real_compactification (t : ℝ) :
    0 < logistic t ∧ logistic t < 1 ∧
      crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
      eta (logistic t : ℂ) = t ∧
      torusLift (logistic t : ℂ) =
        !![(Real.exp t : ℂ), 0; 0, (Real.exp t : ℂ)⁻¹] := by
  exact ⟨logistic_pos t, logistic_lt_one t, crossRatio01_logistic t,
    eta_logistic t, torusLift_logistic t⟩

theorem pristine_chain_packet {s : ℂ} (hs : s ∈ punctured01) (y t : ℝ) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      dlog01 s = 1 / (s * (1 - s)) ∧
      Matrix.det (torusLift s) = 1 ∧
      crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ ∧
      eta (1 - s) = -eta s ∧
      eta (criticalLine y) = 0 ∧
      ‖crossRatio01 (criticalLine y)‖ = 1 ∧
      0 < logistic t ∧ logistic t < 1 ∧
      crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
      eta (logistic t : ℂ) = t ∧
      Matrix.det (halfLogLift s) = 1 := by
  exact ⟨exp_bipolarLog hs, dlog01_eq_one_div_mul hs, torusLift_det hs,
    crossRatio01_one_sub hs, eta_one_sub hs, eta_criticalLine y,
    norm_crossRatio01_criticalLine y, logistic_pos t, logistic_lt_one t,
    crossRatio01_logistic t, eta_logistic t, halfLogLift_det s⟩

theorem soldering_action_equivariant
    (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℂ) (X : HermitianMat2) :
    lorentzSoldering (g₁ * g₂) X =
      lorentzSoldering g₁ (lorentzSoldering g₂ X) :=
  lorentzSoldering_comp g₁ g₂ X

theorem half_log_lift_kan_factorization (s : ℂ) :
    halfLogLift s =
      compactK (theta s / 2) * boostA (eta s / 2) := by
  have hsplit :
      bipolarLog s = (eta s : ℂ) + (theta s : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [eta, theta]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [halfLogLift, plusWeight, compactK, boostA, hsplit,
      ← Complex.exp_add]
    congr 1
    ring
  · simp [halfLogLift, compactK, boostA]
  · simp [halfLogLift, compactK, boostA]
  · simp [halfLogLift, minusWeight, compactK, boostA, hsplit,
      ← Complex.exp_add]
    congr 1
    ring

theorem critical_line_half_log_lift (y : ℝ) :
    halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) := by
  rw [half_log_lift_kan_factorization]
  rw [eta_criticalLine]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostA, Matrix.mul_apply, Fin.sum_univ_two]

theorem half_log_lift_is_sl2c (s : ℂ) :
    isSL2C (halfLogLift s) :=
  halfLogLift_det s

theorem critical_line_compact_factor_is_su2 (y : ℝ) :
    isSU2 (compactK (theta (criticalLine y) / 2)) :=
  compactK_isSU2 _

theorem half_log_lift_preserves_soldered_determinant
    (s : ℂ) (X : HermitianMat2) :
    (lorentzSoldering (halfLogLift s) X).mat.det = X.mat.det :=
  lorentzSoldering_isometry (halfLogLift s) (halfLogLift_det s) X

/-! The real doubled carrier readout is inherited from the native matrix clock
owner.  This is the soldering boundary for the complex Cartan calculation
above: no second real carrier is introduced here. -/

theorem real_doubled_cartan_soldering_packet {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E) matrixJ =
        InfoGeometry.Krein.modular_j ∧
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E) matrixEpsilon =
        InfoGeometry.Krein.spectral_epsilon ∧
      InfoGeometry.Krein.DoubledSpaceMatrixClockBridge.ρclock (E := E) matrixClockAxis =
        InfoGeometry.Krein.clockAxis := by
  exact ⟨ρclock_matrixJ, ρclock_matrixEpsilon, ρclock_matrixClockAxis⟩

theorem winding_period_packet :
    circulationPeriod originWinding = (2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod oneWinding = -(2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod (diagonalWinding 1) = 0 :=
  bipolar_period_packet

theorem logarithmic_principal_part_packet (s : ℂ) :
    dlog01 s - 1 / s = 1 / (1 - s) ∧
      dlog01 s - (-1 / (s - 1)) = 1 / s ∧
      residuePair.1 + residuePair.2 = 0 := by
  exact ⟨dlog01_sub_origin_pole s, dlog01_sub_one_pole s,
    residuePair_sum_zero⟩

theorem boundary_hodge_phase_packet (y : ℝ) :
    phiXY (1 / 2) y = 0 ∧
      deriv (fun t : ℝ => phiXY t y) (1 / 2) =
        1 / ((1 / 4 : ℝ) + y ^ 2) ∧
      dPhiCoeff (1 / 2) y 1 = 0 ∧
      dPhiCoeff (1 / 2) y 0 = 1 / ((1 / 4 : ℝ) + y ^ 2) ∧
      dPsiCoeff (1 / 2) y = hodgeRotate (dPhiCoeff (1 / 2) y) := by
  exact ⟨phiXY_half y, deriv_phiXY_half y,
    dPhiCoeff_half_tangent_zero y, dPhiCoeff_half_normal y,
    dPsiCoeff_eq_hodgeRotate_dPhiCoeff _ _⟩

theorem critical_phase_packet (y : ℝ) :
    crossRatio01 (criticalLine y) = criticalPhase y ∧
      ‖criticalPhase y‖ = 1 :=
  ⟨crossRatio01_criticalLine_eq_criticalPhase y, norm_criticalPhase y⟩

/-! The loxodromic/elliptic vocabulary has an exact carrier-level form here:
the Möbius coordinate is a modulus factor times a unit complex phase.  The
mirror reverses the modulus and the critical line is exactly the unit-modulus
case.  No scattering or boundary-condition hypothesis is part of this packet. -/

theorem loxodromic_elliptic_packet {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp ((eta s : ℂ) + (theta s : ℂ) * Complex.I) = crossRatio01 s ∧
      ‖crossRatio01 s‖ = Real.exp (eta s) ∧
      ‖crossRatio01 (1 - (starRingEnd ℂ) s)‖ = Real.exp (-eta s) := by
  refine ⟨exp_eta_theta hs, ?_, ?_⟩
  · rw [bipolarLog_real_imag s |>.1]
    exact (Real.exp_log (norm_pos_iff.mpr (crossRatio01_ne_zero hs))).symm
  · rw [show 1 - (starRingEnd ℂ) s = mirror s by rfl]
    rw [crossRatio01_mirror, norm_inv]
    have hnorm : ‖(starRingEnd ℂ) (crossRatio01 s)‖ = ‖crossRatio01 s‖ := by
      exact Complex.norm_conj _
    rw [hnorm, bipolarLog_real_imag s |>.1, Real.exp_neg]
    rw [Real.exp_log (norm_pos_iff.mpr (crossRatio01_ne_zero hs))]

theorem critical_line_is_elliptic (y : ℝ) :
    ‖crossRatio01 (criticalLine y)‖ = 1 ∧
      eta (criticalLine y) = 0 :=
  ⟨norm_crossRatio01_criticalLine y, eta_criticalLine y⟩

/-! The real differential readout is the exact carrier-level translation of
the dissipative/rotational physical vocabulary: one covector produces a
normal gradient response and its quarter-turn, with no extra dynamics assumed. -/

theorem real_gradient_circular_packet (y : ℝ) :
    gradientResponse ((1 / 2 : ℝ), y) = (-(criticalRadiusSq y)⁻¹, 0) ∧
      circularResponse ((1 / 2 : ℝ), y) = (0, (criticalRadiusSq y)⁻¹) ∧
      InfoGeometry.Canonical.ApolloniusGradientCircularBridge.pairing
        (gradientResponse ((1 / 2 : ℝ), y))
        (circularResponse ((1 / 2 : ℝ), y)) = 0 ∧
      InfoGeometry.Canonical.ApolloniusGradientCircularBridge.pairing
        (gradientResponse ((1 / 2 : ℝ), y))
        (gradientResponse ((1 / 2 : ℝ), y)) =
        InfoGeometry.Canonical.ApolloniusGradientCircularBridge.pairing
          (circularResponse ((1 / 2 : ℝ), y))
          (circularResponse ((1 / 2 : ℝ), y)) := by
  exact ⟨gradientResponse_criticalLine y, circularResponse_criticalLine y,
    gradientResponse_pairing_circularResponse _,
    gradientResponse_energy_eq_circularResponse_energy _⟩

/-! The dynamical readout is the exact finite-dimensional flow already owned
by the rapidity module: the radial coordinate contracts exponentially while
the angular coordinate advances linearly. -/

theorem rapidity_flow_packet (γ ω s t u θ : ℝ) :
    (flowMap γ ω t (u, θ)).1 = Real.exp (-γ * t) * u ∧
      (flowMap γ ω t (u, θ)).2 = θ + ω * t ∧
      flowMap γ ω (s + t) (u, θ) =
        flowMap γ ω s (flowMap γ ω t (u, θ)) := by
  exact ⟨flowMap_rapidity γ ω t u θ, rfl, flowMap_add γ ω s t (u, θ)⟩

theorem rapidity_flow_initial_ode (γ ω u θ : ℝ) :
    HasDerivAt (fun t : ℝ => flowMap γ ω t (u, θ))
      (-γ * u, ω) 0 := by
  simpa [totalFlow] using
    (hasDerivAt_flowMap_zero γ ω u θ)

theorem rapidity_flow_dissipation_packet
    {γ ω t u θ : ℝ} (hγt : 0 ≤ γ * t) :
    apolloniusRadialNegativeLog
        (flowMap γ ω t (u, θ)).1
        (flowMap γ ω t (u, θ)).2 =
      Real.exp (-γ * t) * apolloniusRadialNegativeLog u θ ∧
      |apolloniusRadialNegativeLog
          (flowMap γ ω t (u, θ)).1
          (flowMap γ ω t (u, θ)).2| ≤
        |apolloniusRadialNegativeLog u θ| := by
  exact ⟨flowMap_apollonius_readout_scale γ ω t u θ,
    flowMap_apollonius_readout_abs_nonincreasing hγt⟩

theorem rapidity_flow_dissipation_tendsto_zero
    {γ u θ : ℝ} (hγ : 0 < γ) :
    Filter.Tendsto
      (fun t : ℝ => apolloniusRadialNegativeLog
        (flowMap γ 0 t (u, θ)).1
        (flowMap γ 0 t (u, θ)).2)
      Filter.atTop (nhds 0) :=
  flowMap_apollonius_readout_tendsto_zero hγ

theorem rapidity_flow_split_boost_packet (γ t u : ℝ) :
    (flowMap γ 0 t (u, 0)).1 =
      InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.rightPart
        (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.mul
          (InfoGeometry.Krein.SplitBoost.boostElement (γ * t))
          (InfoGeometry.Arithmetic.HestenesKreinPrimeThermodynamics.SplitComplex.reconstruct
            0 u)) :=
  flowMap_rapidity_eq_splitBoost_rightPart γ t u

end InfoGeometry.Canonical.BipolarPristineMathematicalChain
