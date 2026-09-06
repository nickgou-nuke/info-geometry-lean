import InfoGeometry.Canonical.Cl55WittMultigrading
import InfoGeometry.Canonical.Cl55WittFullLieClosure
import InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy
import InfoGeometry.Canonical.Cl55WittChiralityRefinement
import InfoGeometry.Streaming.Cl55FiveGradeBoundaryReadout

/-!
# Certified Cl(5,5) multigraded boundary chain

This file is intentionally a bridge between existing owners.  It records the
finite chain without introducing a second Fock or Clifford carrier.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55WittMultigradedPristineChain

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittCAR
open InfoGeometry.Canonical.Cl55WittLieRouting
open InfoGeometry.Canonical.Cl55WittMultigrading
open InfoGeometry.Canonical.Cl55WittFullLieClosure
open InfoGeometry.Canonical.Cl55WittOrthogonalHierarchy
open InfoGeometry.Canonical.Cl55WittChiralityRefinement
open InfoGeometry.Streaming.Cl55FiveGradeBoundaryReadout
open InfoGeometry.Streaming.FiniteTwoBoundaryWeakFunctional
theorem cl55_multigraded_pristine_chain
    {μ : WittWeight} {X : MatStage 5}
    (hX : X ∈ weightSpace μ) :
    wittFiveGradeLieSubalgebra = wittGeneratorLieSpan ∧
    quadraticCoreLieSubalgebra ≤ wittFiveGradeLieSubalgebra ∧
    (Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittZero +
      Module.finrank ℝ wittPosTwo = 45) ∧
    (Module.finrank ℝ wittNegTwo + Module.finrank ℝ wittNegOne +
      Module.finrank ℝ wittZero + Module.finrank ℝ wittPosOne +
      Module.finrank ℝ wittPosTwo = 55) := by
  refine ⟨wittFiveGradeLieSubalgebra_eq_generatorLieSpan,
    ?_, quadratic_core_dimension_fingerprint.1,
    full_extension_dimension_fingerprint.1⟩
  intro Y hY
  exact quadraticCoreSpan_le_full hY

theorem cl55_multigraded_bracket_chain
    {μ ν : WittWeight} {X Y : MatStage 5}
    (hX : X ∈ weightSpace μ) (hY : Y ∈ weightSpace ν) :
    bracket X Y ∈ weightSpace (μ + ν) ∧
    complexSpinAction (bracket X Y) =
      complexSpinAction X * complexSpinAction Y -
        complexSpinAction Y * complexSpinAction X := by
  exact ⟨weightSpace_bracket_mem hX hY,
    complexSpinAction_bracket X Y⟩

theorem cl55_multigraded_boundary_chain
    (p : Cl55BoundaryPair) {μ ν : WittWeight}
    {X Y : MatStage 5}
    (hX : X ∈ weightSpace μ) (hY : Y ∈ weightSpace ν) :
    bracket X Y ∈ weightSpace (μ + ν) ∧
    cl55BoundaryReadout p (bracket X Y) =
      weakValue p
        (complexSpinAction X * complexSpinAction Y -
          complexSpinAction Y * complexSpinAction X) := by
  exact ⟨weightSpace_bracket_mem hX hY,
    cl55BoundaryReadout_bracket p X Y⟩

def HasClassicalOrthogonalIdentification : Prop :=
  Nonempty (quadraticCoreLieSubalgebra ≃ₗ⁅ℝ⁆ SplitD5Model) ∧
  Nonempty (wittFiveGradeLieSubalgebra ≃ₗ⁅ℝ⁆ SplitB5Model)

end InfoGeometry.Canonical.Cl55WittMultigradedPristineChain
