import InfoGeometry.Analysis.BipolarSignedLogConventionBridge
import InfoGeometry.Analysis.BipolarWindingExactSequence
import InfoGeometry.Analysis.BipolarElementaryContourPeriods
import InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
import InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge
import InfoGeometry.Canonical.BipolarWittProjectiveWardBridge
import Mathlib.Tactic

/-!
# Pristine period, Schwarzian, and Virasoro chain

This capstone records the exact mathematics recovered from the informal
period/Schwarzian/CFT stream:

* `s/(s-1)` is the constant sign shift of the repository coordinate
  `q=s/(1-s)` and has the same logarithmic differential, although their
  principal logarithms are not generally equivalent modulo `2πi`;
* the explicit winding carrier is `ℤ × ℤ`; the residue-difference homomorphism
  is onto `ℤ`, has diagonal kernel, and its complex period image is `2πiℤ`;
* Mathlib's native complex exponential is the additive quotient covering by
  that `2πiℤ` subgroup;
* the full exponential characters descend through the period quotient, while
  the half-Cartan lift can retain a central spinorial sign;
* the Möbius Schwarzian vanishes;
* a local logarithm branch has a certified third derivative jet whose
  Schwarzian is the global meromorphic coefficient `1/(2s²(s-1)²)`;
* multiplying by `-(c/12)` gives a normalized projective connection satisfying
  the chosen Virasoro coadjoint scaling law;
* the repository's genuine Virasoro cocycle vanishes on the projective Witt
  modes indexed by `{-1,0,1}`;
* `-c/24` is the equal leading double-pole coefficient, not a one-form residue,
  and the exact global partial fraction also contains simple-pole terms.

No global classification of all loops in the twice-punctured plane, CFT state,
vacuum selection, Hilbert-space Virasoro representation, or physical
stress-energy interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarSchwarzianWardPristineChain

open VirasoroProject
open VirasoroProject.WittAlgebra
open InfoGeometry.Algebra.WittProjectiveClosureHonest
open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Analysis.BipolarSignedLogConventionBridge
open InfoGeometry.Analysis.BipolarWindingExactSequence
open InfoGeometry.Analysis.BipolarNativeExpCoveringBridge
open InfoGeometry.Conformal.ComplexSchwarzianJet
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge
open InfoGeometry.Canonical.BipolarWittProjectiveWardBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Physics.ChiralCausalCone

/-- Exact sign-convention and logarithmic-differential reconciliation. -/
theorem pristine_signed_crossRatio_core
    {s : ℂ} (hs : s ∈ punctured01) :
    signedCrossRatio01 s = s / (s - 1) ∧
      HasDerivAt signedCrossRatio01 (-1 / (s - 1) ^ 2) s ∧
      (-1 / (s - 1) ^ 2) / signedCrossRatio01 s = dlog01 s := by
  exact ⟨signedCrossRatio01_eq_div hs,
    hasDerivAt_signedCrossRatio01 hs,
    signedCrossRatio01_logarithmicDerivative hs⟩

/-- Branch-safe principal-log comparison for the two sign conventions. -/
theorem pristine_signed_log_convention_core
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : signedCrossRatio01 s ∈ Complex.slitPlane) :
    signedCrossRatio01 s = s / (s - 1) ∧
      Complex.exp (signedBipolarLog s) = signedCrossRatio01 s ∧
      HasDerivAt signedBipolarLog (dlog01 s) s ∧
      ¬PeriodEquivalent (signedBipolarLog s) (bipolarLog s) := by
  exact bipolar_signed_log_convention_packet hs hslit

/-- Genuine local Cauchy-pole contour calculation using the native circle map. -/
theorem pristine_elementary_cauchy_period
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circlePolePullback c r t) =
      (2 * (Real.pi : ℂ) * Complex.I : ℂ) := by
  exact intervalIntegral_circlePolePullback hr

/-- Native Mathlib circle-integral form of the same elementary Cauchy period. -/
theorem pristine_native_cauchy_circle_period
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    (∮ z in C(c, r), (z - c)⁻¹) =
      (2 * (Real.pi : ℂ) * Complex.I : ℂ) := by
  exact circleIntegral_sub_inv_center hr

/-- Exact algebraic image, kernel, and exponential-fiber statement for the
explicit winding carrier. -/
theorem pristine_period_descent_core
    (w : WindingPair) (W₁ W₂ : ℂ) :
    IsTwoPiIPeriod (circulationPeriod w) ∧
      (circulationPeriod w = 0 ↔ w.1 = w.2) ∧
      (PeriodEquivalent W₁ W₂ ↔ Complex.exp W₁ = Complex.exp W₂) := by
  exact bipolar_period_descent_packet w W₁ W₂

/-- Genuine additive-homomorphism form of the winding exact sequence. -/
theorem pristine_winding_exact_sequence_core :
    residueWindingHom.ker = diagonalWindingSubgroup ∧
      Function.Surjective residueWindingHom ∧
      circulationPeriodHom =
        integerPeriodEmbedding.comp residueWindingHom ∧
      circulationPeriodHom.ker = diagonalWindingSubgroup ∧
      circulationPeriodHom.range =
        AddSubgroup.zmultiples (2 * Real.pi * Complex.I : ℂ) := by
  exact bipolar_winding_exact_sequence_packet

/-- The period image is the deck subgroup in Mathlib's native exponential
covering, and its fibers are exactly period-equivalence classes. -/
theorem pristine_native_exponential_covering_core
    (W₁ W₂ : ℂ) :
    IsAddQuotientCoveringMap
        (fun z : ℂ =>
          (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
        twoPiIPeriodSubgroup ∧
      circulationPeriodHom.range = twoPiIPeriodSubgroup ∧
      (nativeLogClass W₁ = nativeLogClass W₂ ↔
        PeriodEquivalent W₁ W₂) ∧
      ((⟨Complex.exp W₁, Complex.exp_ne_zero W₁⟩ :
          {z : ℂ // z ≠ 0}) =
        ⟨Complex.exp W₂, Complex.exp_ne_zero W₂⟩ ↔
          PeriodEquivalent W₁ W₂) := by
  exact ⟨exp_isAddQuotientCoveringMap,
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    nativeLogClass_eq_iff W₁ W₂,
    exp_fiber_iff_PeriodEquivalent W₁ W₂⟩

/-- The rational coordinate is a map from the punctured plane to nonzero
complex numbers.  It is not mislabeled as a character on the domain. -/
theorem pristine_crossRatio_nonzero_map_core
    (s : PuncturedPlaneCarrier) :
    (bipolarCrossRatioMap s : ℂ) = crossRatio01 s.1 ∧
      bipolarCrossRatioMap s =
        ⟨Complex.exp (bipolarLog s.1),
          Complex.exp_ne_zero (bipolarLog s.1)⟩ := by
  exact ⟨rfl, bipolarCrossRatioMap_eq_exp_principal s⟩

/-- Local principal-log third jet with branch-independent higher coefficients. -/
theorem pristine_local_logarithmic_thirdJet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (logarithmicJet₁ s) s ∧
      HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s ∧
      HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s := by
  exact local_bipolarLog_thirdJet hs hslit

/-- Möbius vanishing, logarithmic quadratic pole, genuine derivative,
square-of-one-form law, and composition factorization. -/
theorem pristine_schwarzian_core
    {s : ℂ} (hs : s ∈ punctured01) :
    crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = 1 / (2 * s ^ 2 * (s - 1) ^ 2) ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      bipolarSchwarzian s =
        schwarzianJet
            (1 / crossRatio01 s)
            (-1 / crossRatio01 s ^ 2)
            (2 / crossRatio01 s ^ 3) *
          crossRatioJet₁ s ^ 2 +
        crossRatioSchwarzian s := by
  exact ⟨crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_rational hs,
    deriv_bipolarSchwarzian_readout hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    bipolarSchwarzian_composition hs⟩

/-- Normalized projective connection, genuine derivatives, square-of-form law,
and exact Ward scaling compatibility. -/
theorem pristine_projective_ward_core
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (v v' v''' : ℂ) :
    bipolarProjectiveConnection c s =
        -(c / 12) * bipolarSchwarzian s ∧
      bipolarProjectiveConnection c s =
        -(c / 24) * dlog01 s ^ 2 ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      deriv (bipolarProjectiveConnection c) s =
        bipolarProjectiveConnectionDeriv c s ∧
      -(c / 12) * schwarzianCoadjointVariation
          (bipolarSchwarzian s) (bipolarSchwarzianDeriv s)
          v v' v''' =
        projectiveConnectionVariation c
          (bipolarProjectiveConnection c s)
          (bipolarProjectiveConnectionDeriv c s)
          v v' v''' := by
  exact ⟨bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    deriv_bipolarSchwarzian_readout hs,
    deriv_bipolarProjectiveConnection c hs,
    bipolar_ward_schwarzian_compatibility c hs v v' v'''⟩

/-- The global projective vector-field evaluation carrier has a genuine
derivative tower ending in zero. -/
theorem pristine_projective_vector_field_core
    (c : ℂ) (v : ProjectiveVectorField) (s : ℂ) :
    HasDerivAt v.value (v.first s) s ∧
      HasDerivAt v.first (v.second s) s ∧
      HasDerivAt v.second (v.third s) s ∧
      (c / 12) * v.third s = 0 := by
  exact ⟨v.hasDerivAt_value s,
    v.hasDerivAt_first s,
    v.hasDerivAt_second s,
    (by simp [ProjectiveVectorField.third])⟩

/-- The analytic zero-third-derivative statement is welded to the repository's
genuine projective Witt modes and Virasoro cocycle. -/
theorem pristine_witt_projective_anomaly_core
    (c : ℂ) (v : ProjectiveVectorField) (s : ℂ)
    (m n : ℤ) (hm : m ∈ ProjectiveClosure)
    (hn : n ∈ ProjectiveClosure) :
    (c / 12) * v.third s = 0 ∧
      anomalyFactor m = 0 ∧
      virasoroCocycle ℂ (lgen ℂ m) (lgen ℂ n) = 0 ∧
      ⁅lgen ℂ m, lgen ℂ n⁆ =
        (m - n : ℂ) • lgen ℂ (m + n) := by
  exact bipolar_projective_anomaly_packet c v s m n hm hn

/-- Equal double-pole coefficients at the two punctures.  These are not
residues of a one-form. -/
theorem pristine_double_pole_core
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    s ^ 2 * bipolarProjectiveConnection c s = regularizedAtZero c s ∧
      (s - 1) ^ 2 * bipolarProjectiveConnection c s = regularizedAtOne c s ∧
      regularizedAtZero c 0 = doublePoleCoefficient c ∧
      regularizedAtOne c 1 = doublePoleCoefficient c ∧
      doublePoleCoefficient c = -c / 24 := by
  exact ⟨zero_doublePole_factorization c hs,
    one_doublePole_factorization c hs,
    regularizedAtZero_zero c,
    regularizedAtOne_one c,
    rfl⟩

/-- Exact global partial fraction, including the simple-pole terms suppressed by
an account that records only leading quadratic coefficients. -/
theorem pristine_projective_partial_fraction_core
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01) :
    bipolarProjectiveConnection c s =
      doublePoleCoefficient c / s ^ 2 +
      doublePoleCoefficient c / (s - 1) ^ 2 +
      (2 * doublePoleCoefficient c) / s -
      (2 * doublePoleCoefficient c) / (s - 1) := by
  exact bipolarProjectiveConnection_partialFractions c hs

/-- Exponential branch descent of the adjoint root actions together with the
central half-Cartan distinction. -/
theorem pristine_adjoint_period_descent_core
    {s : ℂ} (hs : s ∈ punctured01)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    descendedExp (bipolarLogClass s) = crossRatio01 s ∧
      finiteAdjointFlow s σPlus =
        descendedExp (bipolarLogClass s) • σPlus ∧
      finiteAdjointFlow s σMinus =
        (descendedExp (bipolarLogClass s))⁻¹ • σMinus ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact bipolar_period_adjoint_descent_packet hs X

/-- Master theorem for the exact local-to-global chain. -/
theorem pristine_period_schwarzian_ward_master
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (v : ProjectiveVectorField) :
    HasDerivAt bipolarLog (logarithmicJet₁ s) s ∧
      circulationPeriodHom.range = twoPiIPeriodSubgroup ∧
      crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      deriv bipolarSchwarzian s = bipolarSchwarzianDeriv s ∧
      bipolarProjectiveConnection c s =
        -(c / 12) * bipolarSchwarzian s ∧
      bipolarProjectiveConnection c s =
        -(c / 24) * dlog01 s ^ 2 ∧
      deriv (bipolarProjectiveConnection c) s =
        bipolarProjectiveConnectionDeriv c s ∧
      (c / 12) * v.third s = 0 ∧
      regularizedAtZero c 0 = doublePoleCoefficient c ∧
      regularizedAtOne c 1 = doublePoleCoefficient c := by
  exact ⟨(local_bipolarLog_thirdJet hs hslit).1,
    circulationPeriodHom_range_eq_twoPiIPeriodSubgroup,
    crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    deriv_bipolarSchwarzian_readout hs,
    bipolarProjectiveConnection_eq_schwarzian c hs,
    bipolarProjectiveConnection_eq_dlog01_sq c hs,
    deriv_bipolarProjectiveConnection c hs,
    (by simp [ProjectiveVectorField.third]),
    regularizedAtZero_zero c,
    regularizedAtOne_one c⟩

end InfoGeometry.Canonical.BipolarSchwarzianWardPristineChain
