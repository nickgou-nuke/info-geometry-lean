import InfoGeometry.Canonical.ChiralCliffordSplitQuaternionBridge

/-!
# Topology of the finite chiral split-quaternion matrix readout

The canonical owner supplies the concrete `2 × 2` matrix identities.  This
file adds only their finite-dimensional topological envelope: commutator
readouts vary continuously, and imposing a fixed commutator value is a closed
condition.  No split-octonion identification is asserted here.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-- The commutator readout on the real `2 × 2` matrix chart. -/
def chiralCommutatorResidual (A B : Mat₂) : Mat₂ :=
  A * B - B * A

theorem continuous_chiralCommutatorResidual :
    Continuous (fun p : Mat₂ × Mat₂ =>
      chiralCommutatorResidual p.1 p.2) := by
  unfold chiralCommutatorResidual
  fun_prop

/-- The level set of a prescribed commutator value. -/
def chiralCommutatorLevelSet (C : Mat₂) : Set (Mat₂ × Mat₂) :=
  {p | chiralCommutatorResidual p.1 p.2 = C}

theorem isClosed_chiralCommutatorLevelSet (C : Mat₂) :
    IsClosed (chiralCommutatorLevelSet C) := by
  change IsClosed ((fun p : Mat₂ × Mat₂ =>
    chiralCommutatorResidual p.1 p.2) ⁻¹' ({C} : Set Mat₂))
  exact isClosed_singleton.preimage continuous_chiralCommutatorResidual

end InfoGeometry.Topology
