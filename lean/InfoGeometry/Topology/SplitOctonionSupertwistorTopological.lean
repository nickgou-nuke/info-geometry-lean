import InfoGeometry.Canonical.SplitOctonionSupertwistorBridge

/-!
# Topology of the finite split-octonion supertwistor carrier

The canonical owner supplies the finite `Finsupp` carrier and its level-zero
action.  This file records only coordinate-level topology: every basis
readout is continuous and each prescribed coordinate value is a closed
condition.  It does not identify this carrier with projective or super
twistor geometry.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-- Coordinate readout on the finite split-octonion supertwistor carrier. -/
def supertwistorCoordinate (b : SplitOctonionBasis)
    (Z : SupertwistorSpace ℝ) : ℝ := Z b

theorem continuous_supertwistorCoordinate (b : SplitOctonionBasis) :
    Continuous (supertwistorCoordinate b) := by
  unfold supertwistorCoordinate
  fun_prop

/-- A coordinate level set in the finite supertwistor chart. -/
def supertwistorCoordinateLevelSet (b : SplitOctonionBasis) (a : ℝ) :
    Set (SupertwistorSpace ℝ) :=
  {Z | supertwistorCoordinate b Z = a}

theorem isClosed_supertwistorCoordinateLevelSet
    (b : SplitOctonionBasis) (a : ℝ) :
    IsClosed (supertwistorCoordinateLevelSet b a) := by
  change IsClosed ((supertwistorCoordinate b) ⁻¹' ({a} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_supertwistorCoordinate b)

end InfoGeometry.Topology
