import InfoGeometry.Canonical.SplitPauliMatrixRelations

/-!
# Topology of the finite chiral split-quaternion matrix readout

The canonical owner supplies the concrete `2 × 2` matrix identities.  This
file adds only their finite-dimensional topological envelope: commutator
readouts vary continuously, and imposing a fixed commutator value is a closed
condition.  No split-octonion identification is asserted here.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Canonical

/-- The finite integer matrix chart used by the split-Pauli owner. -/
abbrev SplitPauliMat₂ := Matrix (Fin 2) (Fin 2) ℤ

/-- The commutator readout on the finite integer `2 × 2` matrix chart. -/
def chiralCommutatorResidual (A B : SplitPauliMat₂) : SplitPauliMat₂ :=
  A * B - B * A

theorem continuous_chiralCommutatorResidual :
    Continuous (fun p : SplitPauliMat₂ × SplitPauliMat₂ =>
      chiralCommutatorResidual p.1 p.2) := by
  unfold chiralCommutatorResidual
  fun_prop

/-- The level set of a prescribed commutator value. -/
def chiralCommutatorLevelSet (C : SplitPauliMat₂) :
    Set (SplitPauliMat₂ × SplitPauliMat₂) :=
  {p | chiralCommutatorResidual p.1 p.2 = C}

theorem isClosed_chiralCommutatorLevelSet (C : SplitPauliMat₂) :
    IsClosed (chiralCommutatorLevelSet C) := by
  change IsClosed ((fun p : SplitPauliMat₂ × SplitPauliMat₂ =>
    chiralCommutatorResidual p.1 p.2) ⁻¹' ({C} : Set SplitPauliMat₂))
  exact isClosed_singleton.preimage continuous_chiralCommutatorResidual

end InfoGeometry.Topology
