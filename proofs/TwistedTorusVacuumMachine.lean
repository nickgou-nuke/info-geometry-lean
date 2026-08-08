import proofs.TorusKleinO55Bridge
import proofs.SupergradedCuntzBdG
import proofs.ChiralConeAlgebraFinality

/-!
# Twisted torus vacuum machine

This module records the finite algebraic synthesis for the slogan:

```text
Torus = Fourier/raw doubled-lattice data.
Klein bottle = crosscap/glide selection logic.
O(5,5) = split doubled-charge carrier.
Pin(5,5) = carrier plus orientation-reversing crosscap/reflection action.
```

It proves only finite algebraic facts already present in the spine:
Klein generator relations, orientation signs, doubled rank-five carrier dimension,
`O(5,5)` generator counts, and the `15 + 1 = 16` active/base selection count.
The Standard-Model, confinement, Raman/nonlinear-spectroscopy, and full 2D-CFT
claims are not asserted in this module.
-/

noncomputable section

namespace TwistedTorusVacuumMachine

/-- Two finite layers in the twisted-torus machine metaphor. -/
inductive MachineLayer where
  | rawFourierTorusData
  | kleinCrosscapSelectionLogic
  deriving DecidableEq, Repr

/-- Raw data is orientable; selection logic is orientation reversing. -/
def layerOrientationSign : MachineLayer → ℤ
  | .rawFourierTorusData => 1
  | .kleinCrosscapSelectionLogic => -1

@[simp] theorem raw_torus_layer_orientation :
    layerOrientationSign MachineLayer.rawFourierTorusData = 1 := rfl

@[simp] theorem klein_selection_layer_orientation :
    layerOrientationSign MachineLayer.kleinCrosscapSelectionLogic = -1 := rfl

/-- Finite classification for active/frozen mode classes. -/
inductive ModeSelection where
  | activeConstructive
  | frozenInactive
  deriving DecidableEq, Repr

/-- Active modes are kept as trainable/effective degrees; frozen modes encode
selection-rule data. -/
def modeIsActive : ModeSelection → Bool
  | .activeConstructive => true
  | .frozenInactive => false

@[simp] theorem active_constructive_is_active :
    modeIsActive ModeSelection.activeConstructive = true := rfl

@[simp] theorem frozen_inactive_not_active :
    modeIsActive ModeSelection.frozenInactive = false := rfl

/-- Finite machine-code counts: doubled rank-five carrier, full and active
`O(5,5)` generator counts, and the wallpaper-selected active/base count. -/
theorem twisted_torus_machine_counts :
    O55CartanPhononReduction.o55CartanRank = 5 ∧
    TorusKleinO55Bridge.doubledCartanCarrierDimension = 10 ∧
    TorusKleinO55Bridge.doubledCartanCarrierDimension =
      FrozenPin55ManifoldFlow.o55CarrierDimension ∧
    O55GradedGeneratorBasis.fullGradedGeneratorCount = 45 ∧
    O55GradedGeneratorBasis.activeGradedGeneratorCount = 15 ∧
    ProjectiveWallpaperGaugePSA.nonEquivalentPSACount
      ProjectiveWallpaperGaugePSA.WallpaperGroup.p6m =
        O55GradedGeneratorBasis.activeGradedGeneratorCount + 1 := by
  constructor
  · exact O55CartanPhononReduction.o55_cartan_rank_eq
  constructor
  · exact TorusKleinO55Bridge.doubled_cartan_carrier_dimension_eq
  constructor
  · rw [TorusKleinO55Bridge.doubled_cartan_carrier_dimension_eq,
      FrozenPin55ManifoldFlow.o55_carrier_dimension_eq]
  constructor
  · exact O55GradedGeneratorBasis.full_graded_generator_count_eq
  constructor
  · exact O55GradedGeneratorBasis.active_graded_generator_count_eq
  · exact WallpaperO55FrozenSelectionBridge.p6m_psa_count_matches_active_o55_plus_base

/-- The Klein generator is the explicit twisted-torus relation: it conjugates the
translation to its inverse and squares to a translation in the orientable double
cover. -/
theorem twisted_torus_generator_relations :
    (∀ z : ℂ, G (T z) = T_inv (G z)) ∧
    (∀ z : ℂ, G (G z) = z + 2) := by
  constructor
  · exact klein_bottle_relation
  · exact glide_reflection_sq

end TwistedTorusVacuumMachine

end noncomputable section
