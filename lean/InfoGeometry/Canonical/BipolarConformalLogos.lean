/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import InfoGeometry.Coordinate.ApolloniusLogCoordinates
import InfoGeometry.Canonical.ApolloniusGradientCircularBridge
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.BipolarPauliRootWeights
import InfoGeometry.Canonical.BipolarDeckPathClass
import InfoGeometry.Canonical.FinitePerfectMatching
import InfoGeometry.Analysis.BipolarPeriodDescent
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain
import InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
import InfoGeometry.Analysis.BipolarSimplePoleResidues
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import InfoGeometry.Analysis.BipolarMetricEndLengths
import InfoGeometry.Analysis.BipolarPlanarHodgePair
import InfoGeometry.Analysis.BipolarCriticalPhase
import InfoGeometry.Analysis.BipolarBoundaryTrace
import InfoGeometry.Canonical.BipolarCartanLorentzBridge
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import InfoGeometry.Analysis.BipolarWindingExactSequence
import InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
import InfoGeometry.Canonical.PerfectPairBosonVortexBridge
import InfoGeometry.Canonical.BipolarVerifiedCorePacket
import InfoGeometry.Canonical.BipolarSpinHolonomy
import InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import InfoGeometry.Probability.DetectorPenroseEikonalRay
import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge


/-!
# Bipolar conformal logos

This capstone records the exact mathematical spine recovered from a physically
phrased note.  The hierarchy is deliberately strict:

1. Möbius coordinate `q(s)=s/(1-s)`;
2. principal logarithmic readout `W=log q` where a branch is chosen;
3. branch-independent meromorphic differential `dq/q`;
4. determinant-one diagonal `2 × 2` realization.

No electrostatic, Maxwell, superconducting, Lorentz, or global Hodge assertion
is part of this owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarConformalLogos

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarPauliRootWeights
open InfoGeometry.Canonical.FinitePerfectMatching
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Probability.DetectorPenroseEikonalRay
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Analysis.BipolarSimplePoleResidues
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarMetricEndLengths
open InfoGeometry.Analysis.BipolarPlanarHodgePair
open InfoGeometry.Analysis.BipolarCriticalPhase
open InfoGeometry.Analysis.BipolarBoundaryTrace
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Analysis.BipolarLocalConformalCoordinate
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarWindingExactSequence
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.PerfectPairBosonVortexBridge
open InfoGeometry.Canonical.BipolarVerifiedCorePacket
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge


/-- Exact multiplicative/additive/differential packet on the punctured domain. -/
theorem bipolar_logos_packet {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
    dlog01 s = 1 / (s * (1 - s)) ∧
    crossRatio01 s * dlog01 s = 1 / (1 - s) ^ 2 ∧
    Matrix.det (torusLift s) = 1 := by
  exact ⟨exp_bipolarLog hs, dlog01_eq_one_div_mul hs,
    crossRatio01_mul_dlog01 hs, torusLift_det hs⟩

/-- Exact source/sink exchange packet.  The coordinate is inverted, the
coefficient of the logarithmic form is symmetric, and the pulled-back one-form
is odd because the involution has derivative `-1`. -/
theorem exchange_packet {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ ∧
    eta (1 - s) = -eta s ∧
    dlog01 (1 - s) = dlog01 s ∧
    (-1 : ℂ) * dlog01 (1 - s) = -dlog01 s := by
  exact ⟨crossRatio01_one_sub hs, eta_one_sub hs, dlog01_one_sub s,
    pullback_one_sub_dlog01 s⟩

/-- Exact reflection packet. -/
theorem conjugation_packet (s : ℂ) :
    crossRatio01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (crossRatio01 s) ∧
    dlog01 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (dlog01 s) := by
  exact ⟨crossRatio01_conj s, dlog01_conj s⟩

/-- The midpoint vertical line is exactly the zero radial-logarithm locus for
the canonical Cayley coordinate, and its multiplicative image has unit norm. -/
theorem critical_line_packet (y : ℝ) :
    eta (criticalLine y) = 0 ∧
    ‖crossRatio01 (criticalLine y)‖ = 1 := by
  exact ⟨eta_criticalLine y, norm_crossRatio01_criticalLine y⟩

/-- Exact real compactification packet. -/
theorem logistic_packet (t : ℝ) :
    0 < logistic t ∧ logistic t < 1 ∧
    crossRatio01 (logistic t : ℂ) = (Real.exp t : ℂ) ∧
    eta (logistic t : ℂ) = t := by
  exact ⟨logistic_pos t, logistic_lt_one t, crossRatio01_logistic t, eta_logistic t⟩

/-- The two-pole residue balance is `(+1)+(-1)=0`. -/
theorem residue_balance_packet :
    residuePair = ((1 : ℂ), (-1 : ℂ)) ∧ residuePair.1 + residuePair.2 = 0 := by
  exact ⟨rfl, residuePair_sum_zero⟩

/-- The logarithmic Cartan coordinate acts on the two native Pauli root
directions with opposite weights. -/
theorem pauli_root_weight_packet (s : ℂ) :
    commutator (cartan s)
        InfoGeometry.Physics.ChiralCausalCone.σPlus =
      bipolarLog s • InfoGeometry.Physics.ChiralCausalCone.σPlus ∧
      commutator (cartan s)
          InfoGeometry.Physics.ChiralCausalCone.σMinus =
        -bipolarLog s • InfoGeometry.Physics.ChiralCausalCone.σMinus :=
  cartan_root_weight_packet s


theorem genuine_residue_limit_packet :
    HasSimplePoleCoefficientAt dlog01 0 1 ∧
      HasSimplePoleCoefficientAt dlog01 1 (-1) := dlog01_simplePoleCoefficient_pair

theorem apollonius_reflection_metric_packet
    {s : ℂ} (hs : s ∈ punctured01) (c : ℝ) :
    (eta s = c ↔ ‖s‖ = Real.exp c * ‖1 - s‖) ∧
      eta (mirror s) = -eta s ∧ (mirror s = s ↔ s.re = 1 / 2) ∧
      infinityChartDensity 0 = 1 := by
  exact ⟨eta_eq_iff_apollonius hs c, eta_mirror s, mirror_fixed_iff s,
    infinityChartDensity_zero⟩

theorem local_conformal_coordinate_packet
    {s : ℂ} (hs : s ∈ punctured01) (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (dlog01 s) s ∧ dlog01 s ≠ 0 ∧ 0 < metricDensity s :=
  local_conformal_packet hs hslit

theorem winding_period_packet :
    circulationPeriod originWinding = (2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod oneWinding = -(2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod (diagonalWinding 1) = 0 := bipolar_period_packet

theorem native_period_covering_packet (W₁ W₂ : ℂ) :
    residueWindingHom.ker = diagonalWindingSubgroup ∧
      Function.Surjective residueWindingHom ∧
      circulationPeriodHom.range = twoPiIPeriodSubgroup ∧
      IsAddQuotientCoveringMap
        (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
        twoPiIPeriodSubgroup ∧
      (nativeLogClass W₁ = nativeLogClass W₂ ↔ PeriodEquivalent W₁ W₂) := by
  exact ⟨residueWindingHom_ker, residueWindingHom_surjective,
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    exp_isAddQuotientCoveringMap, nativeLogClass_eq_iff W₁ W₂⟩

theorem cartan_soldering_packet (s : ℂ) (X : HermitianMat2) :
    halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧ (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact ⟨halfLogLift_eq_compactK_mul_boostA s, halfLogLift_isSL2C s,
    bipolarSolderingAction_det s X⟩

theorem critical_line_compact_packet (y : ℝ) :
    halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) ∧
      isSU2 (halfLogLift (criticalLine y)) := by
  exact ⟨halfLogLift_criticalLine_eq_compactK y, halfLogLift_criticalLine_isSU2 y⟩

theorem schwarzian_projective_connection_packet
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      bipolarProjectiveConnection c s = -(c / 12) * bipolarSchwarzian s ∧
      bipolarProjectiveConnection c s = -(c / 24) * dlog01 s ^ 2 ∧
      deriv (bipolarProjectiveConnection c) s = bipolarProjectiveConnectionDeriv c s := by
  exact ⟨crossRatioSchwarzian_eq_zero hs, bipolarSchwarzian_eq_half_dlog01_sq hs,
    deriv_bipolarSchwarzian_readout hs, bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs, deriv_bipolarProjectiveConnection c hs⟩

set_option maxHeartbeats 800000 in
theorem pristine_chain_packet
    {s : ℂ} (hs : s ∈ punctured01) (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (X : HermitianMat2) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      HasDerivAt bipolarLog (dlog01 s) s ∧ dlog01 s = 1 / (s * (1 - s)) ∧
      eta (mirror s) = -eta s ∧ (mirror s = s ↔ s.re = 1 / 2) ∧
      halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧ (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact ⟨exp_bipolarLog hs, hasDerivAt_bipolarLog hs hslit,
    dlog01_eq_one_div_mul hs, eta_mirror s, mirror_fixed_iff s,
    halfLogLift_eq_compactK_mul_boostA s, halfLogLift_isSL2C s,
    bipolarSolderingAction_det s X⟩

set_option maxHeartbeats 800000 in
theorem paired_condensate_vortex_packet
    {m : ℕ} (M : PerfectMatching m) (mode : PairMode M) (N : ℕ) (n : ℤ) :
    Fintype.card (PairMode M) = m ∧
      totalPairOccupation M (purePairCondensate M mode N) = N ∧
      pairPhase (pairVortexAngle n) = constituentPhase (pairVortexAngle n) ^ 2 ∧
      pairPhase (pairVortexAngle n) = 1 ∧ residuePair.1 + residuePair.2 = 0 :=
  perfect_pair_boson_vortex_packet M mode N n

theorem operator_holonomy_geodesic_GENERIC_packet (p : FlatCoordinatePoint) :
    constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      spinHolonomy originWinding = -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨canonicalConstantConnectionCurvature_zero, spinHolonomy_origin,
    negativeEtaLine_isFlatAffineGeodesic p, thetaLine_isFlatAffineGeodesic p,
    bipolarGENERIC_energy_rate, bipolarGENERIC_entropy_rate⟩

theorem operator_blueprint_master_packet
    {s : ℂ} (hs : s ∈ punctured01) (p : FlatCoordinatePoint) (t : ℝ) (ψ : BipolarCartanFlatHolonomyBridge.Spinor2) :
    (logarithmicOpDerivation s).toLinearMap InfoGeometry.Physics.ChiralCausalCone.σPlus =
      bipolarLog s • InfoGeometry.Physics.ChiralCausalCone.σPlus ∧
      finiteAdjointFlow s InfoGeometry.Physics.ChiralCausalCone.σMinus = (crossRatio01 s)⁻¹ • InfoGeometry.Physics.ChiralCausalCone.σMinus ∧
      constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      BipolarCartanFlatHolonomyBridge.spinorAction (spinHolonomy originWinding) ψ = -ψ ∧
      HasDerivAt (negativeEtaLine p) (-etaBasis) t ∧
      deriv (fun u : ℝ => deriv (negativeEtaLine p) u) t = 0 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact pristine_operator_blueprint_master hs p t ψ

end InfoGeometry.Canonical.BipolarConformalLogos
