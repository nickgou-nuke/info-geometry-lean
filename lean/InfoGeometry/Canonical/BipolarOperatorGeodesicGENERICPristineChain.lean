import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
import InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel
import Mathlib.Tactic

/-!
# Pristine operator, holonomy, geodesic, and GENERIC chain

This capstone records the theorem-safe content of the operator-connection
blueprint after four corrections:

1. the logarithmic Cartan generator acts infinitesimally with weights `±W` and
   finitely with characters `q^{±1}`;
2. zero local commutator curvature is compatible with nontrivial central
   half-Cartan holonomy;
3. coordinate lines are affine geodesics in the flat `(η,θ)` carrier, without
   asserting a global geodesic theorem in the original punctured plane;
4. a nontrivial GENERIC realization requires explicit skew, positive, and
   Casimir data, and `η = 0` does not imply `dη = 0`.

No physical gauge bundle, BKM constitutive identification, or continuum
holographic reconstruction is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Physics.ChiralCausalCone
open InfoGeometry.Thermo.BipolarGENERICThreeCoordinateModel

/-- Infinitesimal and finite two-sheet Cartan character law. -/
theorem pristine_logarithmic_character_core
    {s : ℂ} (hs : s ∈ punctured01) :
    (logarithmicCartanGenerator s * σPlus -
        σPlus * logarithmicCartanGenerator s = bipolarLog s • σPlus) ∧
      (logarithmicCartanGenerator s * σMinus -
        σMinus * logarithmicCartanGenerator s = (-bipolarLog s) • σMinus) ∧
      finiteAdjointFlow s σPlus = crossRatio01 s • σPlus ∧
      finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus := by
  exact logarithmic_cartan_adjoint_flow_packet hs

/-- Local flatness and nontrivial global half-Cartan monodromy coexist. -/
theorem pristine_flat_holonomy_core :
    wedge (operatorConnection Kboost Kcirc)
        (operatorConnection Kboost Kcirc) = 0 ∧
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
    (p : FlatCoordinatePoint) (ψ : Spinor2) :
    finiteAdjointFlow s σPlus = crossRatio01 s • σPlus ∧
      finiteAdjointFlow s σMinus = (crossRatio01 s)⁻¹ • σMinus ∧
      wedge (operatorConnection Kboost Kcirc)
        (operatorConnection Kboost Kcirc) = 0 ∧
      spinorAction (spinHolonomy originWinding) ψ = -ψ ∧
      IsFlatAffineGeodesic (negativeEtaLine p) ∧
      IsFlatAffineGeodesic (thetaLine p) ∧
      bipolarGENERIC.dH bipolarGENERIC.flow = 0 ∧
      bipolarGENERIC.dS bipolarGENERIC.flow = 1 := by
  exact ⟨finiteAdjointFlow_sigmaPlus_eq_crossRatio hs,
    finiteAdjointFlow_sigmaMinus_eq_crossRatio_inv hs,
    canonicalConnection_selfWedge_zero,
    originHolonomy_spinor_sign ψ,
    negativeEtaLine_isFlatAffineGeodesic p,
    thetaLine_isFlatAffineGeodesic p,
    bipolarGENERIC_energy_rate,
    bipolarGENERIC_entropy_rate⟩

end InfoGeometry.Canonical.BipolarOperatorGeodesicGENERICPristineChain
