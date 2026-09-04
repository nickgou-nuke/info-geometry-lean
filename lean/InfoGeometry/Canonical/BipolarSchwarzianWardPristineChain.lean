import InfoGeometry.Analysis.BipolarPeriodDescent
import InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
import InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
import InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge
import Mathlib.Tactic

/-!
# Pristine period, Schwarzian, and Virasoro chain

This capstone records the exact mathematics recovered from the informal
period/Schwarzian/CFT stream:

* `s/(s-1)` is the constant sign shift of the repository coordinate
  `q=s/(1-s)` and has the same logarithmic differential;
* the explicit winding carrier is `ℤ × ℤ`, its period image is `2πiℤ`, and its
  kernel is the diagonal subgroup;
* the exponential descends through the period quotient, while the half-Cartan
  lift can retain a central spinorial sign;
* the Möbius Schwarzian vanishes;
* a local logarithm branch has a certified third derivative jet whose
  Schwarzian is the global meromorphic coefficient `1/(2s²(s-1)²)`;
* multiplying by `-(c/12)` gives a normalized projective connection satisfying
  the chosen Virasoro coadjoint scaling law;
* quadratic projective vector fields have genuinely vanishing third derivative;
* `-c/24` is the equal double-pole coefficient at the two punctures.

No global loop-classification theorem, CFT state, vacuum selection, Hilbert-space
Virasoro representation, or physical stress-energy interpretation is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarSchwarzianWardPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Analysis.BipolarPeriodDescent
open InfoGeometry.Conformal.ComplexSchwarzianJet
open InfoGeometry.Conformal.BipolarSchwarzianProjectiveConnection
open InfoGeometry.Conformal.BipolarVirasoroProjectiveConnection
open InfoGeometry.Canonical.BipolarPeriodAdjointDescentBridge
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
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

/-- Genuine local Cauchy-pole contour calculation. -/
theorem pristine_elementary_cauchy_period
    {c : ℂ} {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), circlePolePullback c r t) =
      (2 * (Real.pi : ℂ) * Complex.I : ℂ) := by
  exact intervalIntegral_circlePolePullback hr

/-- Exact algebraic image, kernel, and exponential-fiber statement for the
explicit winding carrier. -/
theorem pristine_period_descent_core
    (w : WindingPair) (W₁ W₂ : ℂ) :
    IsTwoPiIPeriod (circulationPeriod w) ∧
      (circulationPeriod w = 0 ↔ w.1 = w.2) ∧
      (PeriodEquivalent W₁ W₂ ↔ Complex.exp W₁ = Complex.exp W₂) := by
  exact bipolar_period_descent_packet w W₁ W₂

/-- Local principal-log third jet with branch-independent higher coefficients. -/
theorem pristine_local_logarithmic_thirdJet
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) :
    HasDerivAt bipolarLog (logarithmicJet₁ s) s ∧
      HasDerivAt logarithmicJet₁ (logarithmicJet₂ s) s ∧
      HasDerivAt logarithmicJet₂ (logarithmicJet₃ s) s := by
  exact local_bipolarLog_thirdJet hs hslit

/-- Möbius vanishing, logarithmic quadratic pole, square-of-one-form law, and
composition factorization. -/
theorem pristine_schwarzian_core
    {s : ℂ} (hs : s ∈ punctured01) :
    crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = 1 / (2 * s ^ 2 * (s - 1) ^ 2) ∧
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
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    bipolarSchwarzian_composition hs⟩

/-- Normalized projective connection, genuine derivative, and exact Ward
scaling compatibility. -/
theorem pristine_projective_ward_core
    (c : ℂ) {s : ℂ} (hs : s ∈ punctured01)
    (v v' v''' : ℂ) :
    bipolarProjectiveConnection c s =
        -(c / 12) * bipolarSchwarzian s ∧
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
    deriv_bipolarProjectiveConnection c hs,
    bipolar_ward_schwarzian_compatibility c hs v v' v'''⟩

/-- The global projective vector-field carrier has a genuine derivative tower
ending in zero, so its central Virasoro term vanishes. -/
theorem pristine_projective_vector_field_core
    (c : ℂ) (v : ProjectiveVectorField) (s : ℂ) :
    HasDerivAt v.value (v.first s) s ∧
      HasDerivAt v.first (v.second s) s ∧
      HasDerivAt v.second (v.third s) s ∧
      (c / 12) * v.third s = 0 := by
  exact ⟨v.hasDerivAt_value s,
    v.hasDerivAt_first s,
    v.hasDerivAt_second s,
    projectiveVectorField_centralTerm_zero c v s⟩

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
      crossRatioSchwarzian s = 0 ∧
      bipolarSchwarzian s = (1 / 2 : ℂ) * dlog01 s ^ 2 ∧
      bipolarProjectiveConnection c s =
        -(c / 12) * bipolarSchwarzian s ∧
      deriv (bipolarProjectiveConnection c) s =
        bipolarProjectiveConnectionDeriv c s ∧
      (c / 12) * v.third s = 0 ∧
      regularizedAtZero c 0 = doublePoleCoefficient c ∧
      regularizedAtOne c 1 = doublePoleCoefficient c := by
  exact ⟨(local_bipolarLog_thirdJet hs hslit).1,
    crossRatioSchwarzian_eq_zero hs,
    bipolarSchwarzian_eq_half_dlog01_sq hs,
    bipolarProjectiveConnection_eq_schwarzian c hs,
    deriv_bipolarProjectiveConnection c hs,
    projectiveVectorField_centralTerm_zero c v s,
    regularizedAtZero_zero c,
    regularizedAtOne_one c⟩

end InfoGeometry.Canonical.BipolarSchwarzianWardPristineChain
