import InfoGeometry.Analysis.BipolarCrossRatioLog
import InfoGeometry.Analysis.BipolarLogDifferential
import InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
import InfoGeometry.Analysis.BipolarLocalConformalCoordinate
import InfoGeometry.Analysis.BipolarWindingPeriodLattice
import InfoGeometry.Canonical.BipolarLogSL2
import InfoGeometry.Canonical.BipolarCartanLorentzBridge
import InfoGeometry.Canonical.BipolarPristineMathematicalChain
import InfoGeometry.Canonical.PerfectPairBosonVortexBridge
import InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain

/-!
# Bipolar conformal logos

This capstone records the exact mathematical spine recovered from physically
phrased notes. The hierarchy is deliberately strict:

1. Möbius coordinate `q(s)=s/(1-s)`;
2. principal logarithmic readout `W=log q` where a branch is chosen;
3. branch-independent meromorphic differential `dq/q`;
4. Apollonius level sets and the reflection `s ↦ 1-conj(s)`;
5. noncritical local conformal coordinates and pullback metric density;
6. inversion-chart correction at the omitted infinity point;
7. two-generator winding lattice and residue-difference period;
8. determinant-one diagonal `2 × 2` realization and native `SL₂(ℂ)` soldering;
9. optional perfect-pair occupation and doubled `U(1)` vortex interpretation;
10. two-sheet Cartan connection, central spin holonomy, flat coordinate
    geodesics, and an explicit finite GENERIC realization.

The capstone deliberately does not infer a conductor, Maxwell field, microscopic
superconductivity, global Hodge decomposition, continuum gauge bundle, or a de
Rham classification not already installed in the repository.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarConformalLogos

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarApolloniusReflectionMetric
open InfoGeometry.Analysis.BipolarLocalConformalCoordinate
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.BipolarPristineMathematicalChain
open InfoGeometry.Canonical.MatrixStageLorentzKANSoldering
open InfoGeometry.Canonical.FinitePerfectMatching
open InfoGeometry.Canonical.PerfectPairBosonVortexBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel

/-- Exact multiplicative/additive/differential packet on the punctured domain. -/
theorem bipolar_logos_packet {s : ℂ} (hs : s ∈ punctured01) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
    dlog01 s = 1 / (s * (1 - s)) ∧
    Matrix.det (torusLift s) = 1 := by
  exact ⟨exp_bipolarLog hs, dlog01_eq_one_div_mul hs, torusLift_det hs⟩

/-- Exact source/sink exchange packet at the level of functions and one-forms. -/
theorem exchange_packet {s : ℂ} (hs : s ∈ punctured01) :
    crossRatio01 (1 - s) = (crossRatio01 s)⁻¹ ∧
    dlog01 (1 - s) = dlog01 s ∧
    (-1 : ℂ) * dlog01 (1 - s) = -dlog01 s := by
  exact ⟨crossRatio01_one_sub hs, dlog01_one_sub s, pullback_one_sub_dlog01 s⟩

/-- Exact complex-conjugation packet. -/
theorem conjugation_packet (s : ℂ) :
    crossRatio01 (Complex.conj s) = Complex.conj (crossRatio01 s) ∧
    dlog01 (Complex.conj s) = Complex.conj (dlog01 s) := by
  exact ⟨crossRatio01_conj s, dlog01_conj s⟩

/-- The midpoint vertical line is the zero radial-logarithm locus and maps to
unit modulus. -/
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

/-- Corrected method-of-images/metric packet: reflection is exact, Apollonius
levels are exact, and infinity is a removable point for the metric coefficient. -/
theorem apollonius_reflection_metric_packet
    {s : ℂ} (hs : s ∈ punctured01) (c : ℝ) :
    (eta s = c ↔ ‖s‖ = Real.exp c * ‖1 - s‖) ∧
      eta (mirror s) = -eta s ∧
      (mirror s = s ↔ s.re = 1 / 2) ∧
      infinityChartDensity 0 = 1 := by
  exact ⟨eta_eq_iff_apollonius hs c, eta_mirror s,
    mirror_fixed_iff s, infinityChartDensity_zero⟩

/-- Exact local-conformal replacement for the informal curvature statement. -/
theorem local_conformal_coordinate_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (dlog01 s) s ∧
      dlog01 s ≠ 0 ∧
      0 < metricDensity s := by
  exact local_conformal_packet hs hslit

/-- Corrected two-puncture period packet. The two elementary windings remain
distinct although the bipolar residue-difference form annihilates the diagonal. -/
theorem winding_period_packet :
    circulationPeriod originWinding = (2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod oneWinding = -(2 * Real.pi * Complex.I : ℂ) ∧
      circulationPeriod (diagonalWinding 1) = 0 := by
  exact bipolar_period_packet

/-- Native `SL₂(ℂ)` soldering packet for the bipolar Cartan element. -/
theorem cartan_soldering_packet (s : ℂ) (X : HermitianMat2) :
    halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧
      (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact ⟨halfLogLift_eq_compactK_mul_boostA s,
    halfLogLift_isSL2C s,
    bipolarSolderingAction_det s X⟩

/-- On the critical line the bipolar Cartan element is exactly compact and
therefore belongs to the repository's `SU(2)` predicate. -/
theorem critical_line_compact_packet (y : ℝ) :
    halfLogLift (criticalLine y) = compactK (theta (criticalLine y) / 2) ∧
      isSU2 (halfLogLift (criticalLine y)) := by
  exact ⟨halfLogLift_criticalLine_eq_compactK y,
    halfLogLift_criticalLine_isSU2 y⟩

/-- Direct readback of the physics-free architectural master theorem. -/
theorem pristine_chain_packet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (X : HermitianMat2) :
    Complex.exp (bipolarLog s) = crossRatio01 s ∧
      HasDerivAt bipolarLog (dlog01 s) s ∧
      dlog01 s = 1 / (s * (1 - s)) ∧
      eta (mirror s) = -eta s ∧
      (mirror s = s ↔ s.re = 1 / 2) ∧
      halfLogLift s = compactK (theta s / 2) * boostA (eta s / 2) ∧
      isSL2C (halfLogLift s) ∧
      (bipolarSolderingAction s X).mat.det = X.mat.det := by
  exact pristine_master_chain hs hslit X

/-- The theorem-safe replacement for the informal superconducting layer:
perfect pairing gives composite modes, occupation-number states provide the
bosonic combinatorial carrier, the composite phase doubles the constituent
angle, and integer pair-vortex winding closes. -/
theorem paired_condensate_vortex_packet
    {m : ℕ} (M : PerfectMatching m)
    (mode : PairMode M) (N : ℕ) (n : ℤ) :
    Fintype.card (PairMode M) = m ∧
      totalPairOccupation M (purePairCondensate M mode N) = N ∧
      pairPhase (pairVortexAngle n) = constituentPhase (pairVortexAngle n) ^ 2 ∧
      pairPhase (pairVortexAngle n) = 1 ∧
      residuePair.1 + residuePair.2 = 0 := by
  exact perfect_pair_boson_vortex_packet M mode N n

/-- Downstream operator/holonomy/geodesic/GENERIC packet. Local commutator
curvature vanishes, the elementary half-Cartan holonomy is the nontrivial
central sign, flat coordinate lines are affine geodesics, and the concrete
GENERIC model conserves energy while producing entropy. -/
theorem operator_holonomy_geodesic_GENERIC_packet
    (p : FlatCoordinatePoint) :
    wedge (operatorConnection Kboost Kcirc)
        (operatorConnection Kboost Kcirc) = 0 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨canonicalConnection_selfWedge_zero,
    spinHolonomy_origin,
    negativeEtaLine_isFlatAffineGeodesic p,
    thetaLine_isFlatAffineGeodesic p,
    bipolarGENERIC_energy_rate,
    bipolarGENERIC_entropy_rate⟩

end InfoGeometry.Canonical.BipolarConformalLogos
