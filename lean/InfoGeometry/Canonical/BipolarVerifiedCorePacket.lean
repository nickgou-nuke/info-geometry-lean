import InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
import InfoGeometry.Canonical.BipolarDeckMonodromy
import Mathlib.Tactic

/-!
# Verified bipolar core packet

This capstone records only the layers present in the repository: affine
logarithmic-coordinate geometry, the constant Cartan connection, finite
spinorial holonomy, and the two-sheet deck involution.  Scattering, GENERIC
dynamics, and a smooth contour monodromy are deliberately not inferred here.
-/

namespace InfoGeometry.Canonical.BipolarVerifiedCorePacket

open InfoGeometry.Analysis.BipolarFlatCoordinateGeodesics
open InfoGeometry.Canonical.BipolarCartanFlatHolonomyBridge
open InfoGeometry.Canonical.BipolarDeckMonodromy
open InfoGeometry.Canonical.BipolarTwoSheetCore
open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.Canonical.BipolarSpinHolonomy
open InfoGeometry.Analysis.BipolarWindingPeriodLattice
open InfoGeometry.Topology.Weyl

theorem verified_bipolar_core_packet
    (p v : InfoGeometry.Analysis.BipolarPlanarHodgePair.PlaneCovector)
    (x : TwoSheet ℂ)
    (ψ : Spinor2) :
    IsFlatAffineGeodesic (affineCoordinateLine p v) ∧
      constantConnectionCurvature (operatorConnection Kboost Kcirc) = 0 ∧
      spinorAction (spinHolonomy originWinding)
        (spinorAction (spinHolonomy originWinding) ψ) = ψ ∧
      deck (deck x) = x := by
  exact ⟨affineCoordinateLine_isFlatAffineGeodesic p v,
    canonicalConstantConnectionCurvature_zero,
    originHolonomy_spinor_two_turns ψ,
    deck_involutive x⟩

end InfoGeometry.Canonical.BipolarVerifiedCorePacket
