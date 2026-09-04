import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import InfoGeometry.Canonical.BipolarVariableCartanConnection
import InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
import InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra
import InfoGeometry.Thermo.BipolarPolynomialMetriplecticModel
import Mathlib.Tactic

/-!
# Pristine operator, holonomy, geodesic, BKM, and GENERIC chain

This capstone records the theorem-safe content of the operator-connection
blueprint after five corrections:

1. the logarithmic Cartan generator defines a genuine native `OpDerivation`
   with weights `±W`, integrated by finite characters `q^{±1}`;
2. the nonconstant logarithmic Cartan one-form has a genuine coefficient and
   frame derivative, vanishing exterior derivative and self-wedge, and a local
   pure-gauge factorization;
3. local flatness is compatible with nontrivial central half-Cartan holonomy;
4. coordinate lines are native differentiable affine geodesics in the flat
   `(η,θ)` carrier, without asserting a global geodesic theorem in the original
   punctured plane;
5. BKM response, alternating curvature, observable Poisson/metriplectic
   brackets, and GENERIC evolution are separate structures. The concrete
   polynomial model proves the commuting-partial and Jacobi laws without
   inserting them as hypotheses, and `η = 0` does not imply `dη = 0`.

No physical gauge bundle, BKM constitutive identification, smooth-function
Poisson manifold, or continuum holographic reconstruction is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarLogDifferential
open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarVariableCartanConnection
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout
open InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
open InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra
open InfoGeometry.Thermo.BipolarPolynomialMetriplecticModel
open SouriauOnsagerBKM

/-- Infinitesimal and finite two-sheet Cartan character law, expressed through
the repository-native operator derivation. -/
theorem pristine_logarithmic_character_core
    {s : ℂ} (hs : s ∈ punctured01) :
    logarithmicOpDerivation s σPlus = bipolarLog s • σPlus ∧
      logarithmicOpDerivation s σMinus = (-bipolarLog s) • σMinus ∧
      finiteAdjointFlow s σPlus = crossRatio01 s • σPlus ∧
      finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  exact ⟨logarithmicOpDerivation_sigmaPlus s,
    logarithmicOpDerivation_sigmaMinus s,
    finiteAdjointFlow_sigmaPlus_eq_crossRatio hs,
    finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv hs⟩

/-- The logarithmic operator derivative is genuinely Leibniz. -/
theorem pristine_logarithmic_derivation_core
    (s : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    logarithmicOpDerivation s (X * Y) =
      logarithmicOpDerivation s X * Y +
        X * logarithmicOpDerivation s Y := by
  exact logarithmicOpDerivation_leibniz s X Y

/-- Genuine nonconstant Maurer--Cartan packet. The coefficient and frame
 derivatives are proved, both curvature terms vanish, and `G⁻¹dG=A` holds on a
 compatible principal-log chart. -/
theorem pristine_variable_cartan_connection_core
    {s : ℂ} (hs : s ∈ punctured01)
    (hslit : crossRatio01 s ∈ Complex.slitPlane) (u v : ℂ) :
    HasDerivAt dlog01 (dlog01Deriv s) s ∧
      variableExteriorDerivative s u v = 0 ∧
      wedge (variableCartanConnection s) (variableCartanConnection s) u v = 0 ∧
      variableCartanCurvature s u v = 0 ∧
      HasDerivAt
        (fun t : ℂ => halfLogLift (s + t * v))
        (halfLogLiftDifferential s v) 0 ∧
      halfLogLiftInv s * halfLogLiftDifferential s v =
        variableCartanConnection s v := by
  exact bipolar_variable_cartan_packet hs hslit u v

/-- Constant-coefficient flatness and nontrivial global half-Cartan monodromy
coexist. -/
theorem pristine_flat_holonomy_core :
    constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      spinHolonomy originWinding =
        -(1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy originWinding ≠
        (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      spinHolonomy (originWinding + oneWinding) = 1 := by
  exact flat_connection_nontrivial_holonomy_packet

/-- The two canonical coordinate families are affine geodesics in the flat
logarithmic coordinate carrier. -/
theorem pristine_flat_coordinate_geodesic_core
    (p : FlatCoordinatePoint) :
    IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      (∀ t, negativeEtaLine p t 1 = p 1) ∧
      (∀ t, thetaLine p t 0 = p 0) := by
  exact bipolar_flat_coordinate_geodesic_packet p

/-- Native derivative and zero-acceleration form of the flat-coordinate theorem. -/
theorem pristine_flat_coordinate_derivative_core
    (p : FlatCoordinatePoint) (t : ℝ) :
    HasDerivAt (negativeEtaLine p) (-etaBasis) t ∧
      HasDerivAt (thetaLine p) thetaBasis t ∧
      deriv (fun u : ℝ => deriv (negativeEtaLine p) u) t = 0 ∧
      deriv (fun u : ℝ => deriv (thetaLine p) u) t = 0 := by
  exact bipolar_flat_coordinate_derivative_packet p t

/-- Native separation of the symmetric BKM response and alternating curvature
readout on the same bipolar tangent carrier. -/
theorem pristine_BKM_curvature_readout_core {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Q Kη Kθ Lη Lθ : FiniteOperatorAlgebra n) (u v : Tangent2) :
    bkmOperator1Form D hD
        (finiteOperatorConnection Kη Kθ)
        (finiteOperatorConnection Lη Lθ) u =
      bkmOperator1Form D hD
        (finiteOperatorConnection Lη Lθ)
        (finiteOperatorConnection Kη Kθ) u ∧
    0 ≤ bkmOperator1Form D hD
      (finiteOperatorConnection Kη Kθ)
      (finiteOperatorConnection Kη Kθ) u ∧
    bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) u v =
      -bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) v u := by
  exact bipolar_BKM_curvature_separation_packet
    D hD Q Kη Kθ Lη Lθ u v

/-- Abstract native-derivation observable packet. Positivity is stated through
an ordered real ring readout, not on an arbitrary unordered algebra. -/
theorem pristine_observable_metriplectic_core
    {A : Type*} [CommRing A] [Algebra ℝ A]
    (D : DerivationFrame A) (ev : A →+* ℝ)
    (H S F G K : A)
    (hS : IsPoissonCasimir D S)
    (hH : IsMetricKernel D H) :
    poissonBracket D (poissonBracket D F G) K +
        poissonBracket D (poissonBracket D G K) F +
        poissonBracket D (poissonBracket D K F) G = 0 ∧
      metriplecticBracket D H (H + S) = 0 ∧
      metriplecticBracket D S (H + S) = (D.Deta S) ^ 2 ∧
      0 ≤ ev (metriplecticBracket D S (H + S)) := by
  exact bipolar_observable_metriplectic_packet
    D ev H S F G K hS hH

/-- Concrete theorem packet on the native polynomial observable algebra
`ℝ[η,θ,a]`; here commutation of partial derivations and Jacobi are proved, not
supplied as external hypotheses. -/
theorem pristine_polynomial_metriplectic_core
    (F G H : ObservablePoly) (x : Fin 3 → ℝ) :
    poissonBracket polynomialFrame (poissonBracket polynomialFrame F G) H +
        poissonBracket polynomialFrame (poissonBracket polynomialFrame G H) F +
        poissonBracket polynomialFrame (poissonBracket polynomialFrame H F) G = 0 ∧
      poissonBracket polynomialFrame thetaObservable auxiliaryObservable = 1 ∧
      metriplecticBracket polynomialFrame polynomialHamiltonian
        (polynomialHamiltonian + polynomialEntropy) = 0 ∧
      metriplecticBracket polynomialFrame polynomialEntropy
        (polynomialHamiltonian + polynomialEntropy) = 1 ∧
      0 ≤ evalAt x
        (metriplecticBracket polynomialFrame polynomialEntropy
          (polynomialHamiltonian + polynomialEntropy)) := by
  exact bipolar_polynomial_metriplectic_packet F G H x

/-- Explicit nontrivial finite GENERIC realization of the longitudinal/transverse
coordinate assignment. -/
theorem pristine_GENERIC_core :
    bipolarGENERIC.L bipolarGENERIC.dS = 0 ∧
      bipolarGENERIC.M bipolarGENERIC.dH = 0 ∧
      bipolarGENERIC.L bipolarGENERIC.dH = -auxiliaryBasis3 ∧
      bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact bipolar_GENERIC_packet

/-- Corrected critical-level statement: the coordinate value vanishes, but the
entropy covector and dissipative component do not. -/
theorem pristine_critical_level_correction (θ a : ℝ) :
    etaCovector (criticalCoordinateState θ a) = 0 ∧
      bipolarGENERIC.dS etaBasis3 = -1 ∧
      bipolarGENERIC.M bipolarGENERIC.dS = -etaBasis3 ∧
      bipolarGENERIC.M bipolarGENERIC.dS ≠ 0 := by
  exact ⟨etaCovector_criticalCoordinateState θ a,
    entropyCovector_etaBasis3,
    (critical_coordinate_dissipative_lane_survives θ a).2.1,
    (critical_coordinate_dissipative_lane_survives θ a).2.2⟩

/-- The central elementary holonomy is nontrivial on spinors but trivial in the
adjoint matrix representation. -/
theorem pristine_double_cover_readout
    (ψ : Spinor2) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    spinorAction (spinHolonomy originWinding) ψ = -ψ ∧
      spinorAction (spinHolonomy originWinding)
        (spinorAction (spinHolonomy originWinding) ψ) = ψ ∧
      spinHolonomy originWinding * X * spinHolonomy originWinding = X := by
  exact ⟨originHolonomy_spinor_sign ψ,
    originHolonomy_spinor_two_turns ψ,
    originHolonomy_adjoint_trivial X⟩

/-- Master theorem for the corrected operator blueprint. -/
theorem pristine_operator_blueprint_master
    {s : ℂ} (hs : s ∈ punctured01)
    (p : FlatCoordinatePoint) (t : ℝ) (ψ : Spinor2) :
    logarithmicOpDerivation s σPlus = bipolarLog s • σPlus ∧
      finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus ∧
      constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      spinorAction (spinHolonomy originWinding) ψ = -ψ ∧
      HasDerivAt (negativeEtaLine p) (-etaBasis) t ∧
      deriv (fun u : ℝ => deriv (negativeEtaLine p) u) t = 0 ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨logarithmicOpDerivation_sigmaPlus s,
    finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv hs,
    canonicalConstantConnectionCurvature_zero,
    originHolonomy_spinor_sign ψ,
    hasDerivAt_negativeEtaLine p t,
    (canonical_coordinate_lines_zero_acceleration p t).1,
    bipolarGENERIC_energy_rate,
    bipolarGENERIC_entropy_rate⟩

end InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain
