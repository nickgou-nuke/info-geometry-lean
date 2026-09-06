import InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
import InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge
import InfoGeometry.Thermo.BipolarPoissonAlgebra
import InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import Mathlib

/-!
# Variable connection and Poisson frontier

This capstone records the next verified boundary of the bipolar construction:

* the nonconstant logarithmic Cartan one-form is locally flat;
* its displayed pure-gauge primitive is the actual derivative of the half-log
  lift on a compatible logarithm chart;
* the reversible `(theta,a)` plane defines a Poisson algebra for every supplied
  pair of commuting derivations;
* the eta Casimir forces a skew operator on the two-coordinate carrier to
  vanish, explaining the three-coordinate completion;
* the concrete GENERIC model then has nonzero reversible and dissipative lanes,
  conserved energy, and nonnegative entropy production.

No topological gap is filled by an axiom or by a physical identification.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarVariableConnectionPoissonPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Canonical.BipolarVariableCartanMaurerCartan
open InfoGeometry.Canonical.BipolarHalfLogLiftAnalyticPureGauge
open InfoGeometry.Canonical.BipolarLogSL2
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Thermo.BipolarPoissonAlgebra
open InfoGeometry.Thermo.BipolarTwoDimensionalSkewObstruction
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
open InfoGeometry.Thermo.GenericMetriplecticFlow

/-- Point-dependent connection and local Maurer--Cartan packet. -/
theorem pristine_variable_connection_core
    {s : ℂ} (hs : s ∈ punctured01) (u v : ℂ) :
    omegaCoeff s = dlog01 s ∧
      HasDerivAt omegaCoeff (omegaCoeffDeriv s) s ∧
      variableExteriorDerivativeAt s u v = 0 ∧
      variableCartanCurvatureAt s u v = 0 := by
  exact ⟨omegaCoeff_eq_dlog01 hs,
    hasDerivAt_omegaCoeff hs,
    variableExteriorDerivativeAt_eq_zero s u v,
    variableCartanMaurerCartan s u v⟩

/-- The local pure-gauge identity is tied to the analytic derivative of the
actual half-log lift, entry by entry. -/
theorem pristine_local_pure_gauge_core
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane)
    (v : ℂ) (i j : Fin 2) :
    HasDerivAt (fun t : ℂ => halfLogLift (s + t * v) i j)
        (halfLogLiftAnalyticDifferential s v i j) 0 ∧
      halfLogLiftInv s * halfLogLiftAnalyticDifferential s v =
        variableCartanConnection s v := by
  exact bipolar_half_log_pure_gauge_packet hs hslit v i j

/-- Observable-level Poisson laws from a commuting pair of genuine
Leibniz derivations. -/
theorem pristine_poisson_core
    {A : Type*} [CommRing A] [Algebra ℝ A]
    (D : CommutingDerivationPair A) (F G H : A) :
    poissonBracket D F G = -poissonBracket D G F ∧
      poissonBracket D F (G * H) =
        poissonBracket D F G * H + G * poissonBracket D F H ∧
      poissonBracket D (poissonBracket D F G) H +
        poissonBracket D (poissonBracket D G H) F +
        poissonBracket D (poissonBracket D H F) G = 0 := by
  exact bipolar_poisson_algebra_packet D F G H

/-- The exact two-dimensional obstruction behind the auxiliary-coordinate
completion. -/
theorem pristine_dimension_obstruction_core
    (L : Covector State2 →ₗ[ℝ] State2)
    (hskew : ∀ α β : Covector State2,
      α (L β) = -β (L α))
    (heta : L etaCovector2 = 0) :
    etaCovector2 ≠ 0 ∧ L thetaCovector2 = 0 ∧ L = 0 := by
  exact bipolar_two_dimensional_obstruction_packet L hskew heta

/-- The three-coordinate completion realizes the desired nontrivial GENERIC
laws after the obstruction has been removed. -/
theorem pristine_three_coordinate_GENERIC_core :
    bipolarGENERIC.L bipolarGENERIC.dS = 0 ∧
      bipolarGENERIC.M bipolarGENERIC.dH = 0 ∧
      bipolarGENERIC.L bipolarGENERIC.dH = -auxiliaryBasis3 ∧
      bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact bipolar_GENERIC_packet

/-- Combined nearest-frontier theorem. -/
theorem pristine_variable_poisson_master
    {s : ℂ} (hs : s ∈ punctured01)
    (u v : ℂ) :
    variableCartanCurvatureAt s u v = 0 ∧
      halfLogLiftInv s * halfLogLiftAnalyticDifferential s u =
        variableCartanConnection s u ∧
      cotangentPoissonPairing thetaCovector auxiliaryCovector = 1 ∧
      cotangentPoissonPairing etaCovector thetaCovector = 0 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨variableCartanMaurerCartan s u v,
    halfLogLift_local_pure_gauge hs u,
    cotangentPoissonPairing_theta_auxiliary,
    cotangentPoissonPairing_eta_left thetaCovector,
    bipolarGENERIC_energy_rate,
    bipolarGENERIC_entropy_rate⟩

end InfoGeometry.Canonical.BipolarVariableConnectionPoissonPristineChain
