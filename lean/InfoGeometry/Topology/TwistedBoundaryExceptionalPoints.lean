import Mathlib.Tactic

/-!
# Non-orientable Exceptional Points in Twisted Boundary Systems

Formalizes the exceptional classification of EP pairs in a Brillouin Klein bottle
from arXiv:2504.11983v1.

Depending on the vorticities, braids, and Berry phases, EP pairs in a two-band
Hamiltonian can merge into Dirac points (DP), Vortex points (VP), or remain defective.
-/

namespace InfoGeometry.Topology.TwistedBoundary

/--
Classification of Exceptional Point pairs.
Type I: Counter-rotating EPs (opposite vorticities)
Type II: Co-rotating EPs (same vorticities)
-/
inductive EPPairType
| TypeI  -- Counter-rotating
| TypeII -- Co-rotating
deriving DecidableEq

/-- The outcome of two EPs merging at the origin. -/
inductive MergingOutcome
| DP        -- Dirac Point (non-defective)
| VP        -- Vortex Point (non-defective)
| Defective -- Remains an exceptional point (defective)
deriving DecidableEq

/--
We formalize Table I from the paper mapping the 4 Hamiltonian cases 
to their topological invariants.
-/
structure EPCaseClassification where
  pair_type : EPPairType
  vorticities_opposite : Bool
  braid_trivial : Bool
  berry_phase_pi : Bool
  merging : MergingOutcome

/-- Case 1: H(z) = [0, z; z*, 0]. Type I, DP merging. -/
def case1 : EPCaseClassification :=
  { pair_type := EPPairType.TypeI,
    vorticities_opposite := true,
    braid_trivial := true,
    berry_phase_pi := true,
    merging := MergingOutcome.DP }

/-- Case 2: H(z) = [0, 1; |z|^2, 0]. Type I, Defective merging. -/
def case2 : EPCaseClassification :=
  { pair_type := EPPairType.TypeI,
    vorticities_opposite := true,
    braid_trivial := true,
    berry_phase_pi := false,
    merging := MergingOutcome.Defective }

/-- Case 3: H(z) = [0, z; z, 0]. Type II, VP merging. -/
def case3 : EPCaseClassification :=
  { pair_type := EPPairType.TypeII,
    vorticities_opposite := false,
    braid_trivial := false,
    berry_phase_pi := false,
    merging := MergingOutcome.VP }

/-- Case 4: H(z) = [0, 1; z^2, 0]. Type II, Defective merging. -/
def case4 : EPCaseClassification :=
  { pair_type := EPPairType.TypeII,
    vorticities_opposite := false,
    braid_trivial := false,
    berry_phase_pi := true,
    merging := MergingOutcome.Defective }

/--
Theorem: A co-rotating pair of EPs (Type II), as defined in Case 3, cannot merge into a Dirac Point,
as it lacks the necessary opposite vorticities required to annihilate.
-/
theorem typeII_case3_cannot_be_dp : case3.merging ≠ MergingOutcome.DP := by decide

/--
Theorem: A co-rotating pair of EPs (Type II), as defined in Case 4, cannot merge into a Dirac Point.
-/
theorem typeII_case4_cannot_be_dp : case4.merging ≠ MergingOutcome.DP := by decide

end InfoGeometry.Topology.TwistedBoundary
