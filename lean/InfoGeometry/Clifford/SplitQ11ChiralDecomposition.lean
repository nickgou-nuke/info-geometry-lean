import Mathlib
import InfoGeometry.Clifford.SplitQ11Projectors
import InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
import InfoGeometry.OperatorAlgebra.SymmetryInvariants
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Clifford.SplitQ11ChiralDecomposition

Proof-only chiral decomposition for the split `Cl(1,1)` projectors.

This module does not add any new analytic content. It packages the existing
`epsMinusProjector` / `epsPlusProjector` pair as a complementary projector
decomposition and proves the exact left/right splitting laws for an arbitrary
split `Cl(1,1)` element.

No socket.
No certificate.
No CFT claim.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitQ11ChiralDecomposition

open InfoGeometry.Clifford.SplitQ11Projectors
open InfoGeometry.OperatorAlgebra.ChiralLightconeStinespring
open InfoGeometry.OperatorAlgebra.SymmetryInvariants

/-- The split `Cl(1,1)` projectors as a complementary projector pair. -/
@[rep_depth krein]
def splitQ11ComplementaryProjectors :
    ComplementaryProjectors Alg where
  p := epsMinusProjector
  q := epsPlusProjector
  p_idempotent := epsMinusProjector_is_idempotent
  q_idempotent := epsPlusProjector_is_idempotent
  sum_eq_one := epsMinusProjector_add_epsPlusProjector
  pq_zero := epsMinusProjector_mul_epsPlusProjector
  qp_zero := epsPlusProjector_mul_epsMinusProjector

/-- The split `Cl(1,1)` projectors as a chiral projector pair. -/
@[rep_depth krein]
def splitQ11ChiralProjectorPair : ChiralProjectorPair Alg where
  PL := epsPlusProjector
  PR := epsMinusProjector
  PL_idem := epsPlusProjector_is_idempotent
  PR_idem := epsMinusProjector_is_idempotent
  complementary := by
    simpa [add_comm] using epsMinusProjector_add_epsPlusProjector
  disjoint_left := epsPlusProjector_mul_epsMinusProjector
  disjoint_right := epsMinusProjector_mul_epsPlusProjector

/-- The left split component of a `Cl(1,1)` element. -/
@[rep_depth krein]
def leftSplitComponent (x : Alg) : Alg :=
  splitQ11ComplementaryProjectors.pComponent x

/-- The right split component of a `Cl(1,1)` element. -/
@[rep_depth krein]
def rightSplitComponent (x : Alg) : Alg :=
  splitQ11ComplementaryProjectors.qComponent x

/-- Every split `Cl(1,1)` element decomposes into left and right components. -/
@[bridge_target_tag, rep_depth krein]
theorem splitQ11_left_right_decomposition (x : Alg) :
    leftSplitComponent x + rightSplitComponent x = x := by
  simpa [leftSplitComponent, rightSplitComponent] using
    ComplementaryProjectors.left_decomposition splitQ11ComplementaryProjectors x

/-- The same decomposition viewed through the chiral projector pair. -/
@[bridge_target_tag, rep_depth krein]
theorem splitQ11_chiral_pair_decomposition (x : Alg) :
    splitQ11ChiralProjectorPair.PL * x + splitQ11ChiralProjectorPair.PR * x = x := by
  simpa [splitQ11ChiralProjectorPair] using
    ComplementaryProjectors.left_decomposition
      splitQ11ComplementaryProjectors x

/-- The left split component is supported on the negative projector. -/
@[bridge_target_tag, rep_depth krein]
theorem leftSplitComponent_supported (x : Alg) :
    IsSupportedOn splitQ11ComplementaryProjectors.p (leftSplitComponent x) := by
  simpa [leftSplitComponent] using
    ComplementaryProjectors.pComponent_supported splitQ11ComplementaryProjectors x

/-- The right split component is supported on the positive projector. -/
@[bridge_target_tag, rep_depth krein]
theorem rightSplitComponent_supported (x : Alg) :
    IsSupportedOn splitQ11ComplementaryProjectors.q (rightSplitComponent x) := by
  simpa [rightSplitComponent] using
    ComplementaryProjectors.qComponent_supported splitQ11ComplementaryProjectors x

/-- The split projector pair is complementary in the operator-algebra sense. -/
@[bridge_target_tag, rep_depth krein]
theorem splitQ11ComplementaryProjectors_owner :
    splitQ11ComplementaryProjectors.p + splitQ11ComplementaryProjectors.q = 1 ∧
      splitQ11ComplementaryProjectors.p * splitQ11ComplementaryProjectors.q = 0 ∧
      splitQ11ComplementaryProjectors.q * splitQ11ComplementaryProjectors.p = 0 := by
  constructor
  · exact splitQ11ComplementaryProjectors.sum_eq_one
  · constructor
    · exact splitQ11ComplementaryProjectors.pq_zero
    · exact splitQ11ComplementaryProjectors.qp_zero

/-- Owner target for the split `Cl(1,1)` chiral decomposition. -/
@[owner_target_tag]
def SplitQ11ChiralDecompositionOwnerTarget : Prop :=
  ∀ x : Alg,
    leftSplitComponent x + rightSplitComponent x = x ∧
      IsSupportedOn splitQ11ComplementaryProjectors.p (leftSplitComponent x) ∧
      IsSupportedOn splitQ11ComplementaryProjectors.q (rightSplitComponent x)

/-- The split `Cl(1,1)` chiral decomposition owner target is proved. -/
theorem splitQ11ChiralDecompositionOwnerTarget :
    SplitQ11ChiralDecompositionOwnerTarget := by
  intro x
  exact ⟨splitQ11_left_right_decomposition x,
    leftSplitComponent_supported x,
    rightSplitComponent_supported x⟩

end InfoGeometry.Clifford.SplitQ11ChiralDecomposition
