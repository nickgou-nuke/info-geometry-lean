import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
import InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import Mathlib.Tactic

/-!
# Pristine operator, holonomy, geodesic, BKM, and GENERIC chain

This capstone records the theorem-safe content of the operator-connection
blueprint after four corrections:

1. the logarithmic Cartan generator defines a genuine native `OpDerivation`
   with weights `±W`, integrated by finite characters `q^{±1}`;
2. zero constant-coefficient curvature is compatible with nontrivial central
   half-Cartan holonomy;
3. coordinate lines are native differentiable affine geodesics in the flat
   `(η,θ)` carrier, without asserting a global geodesic theorem in the original
   punctured plane;
4. BKM symmetric response, alternating curvature, and GENERIC evolution are
   separate structures with separate hypotheses; `η = 0` does not imply
   `dη = 0`.

No physical gauge bundle, BKM constitutive identification, or continuum
holographic reconstruction is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarLogarithmicDerivationBridge
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout
open InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
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

/-- Explicit nontrivial GENERIC realization of the longitudinal/transverse
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
