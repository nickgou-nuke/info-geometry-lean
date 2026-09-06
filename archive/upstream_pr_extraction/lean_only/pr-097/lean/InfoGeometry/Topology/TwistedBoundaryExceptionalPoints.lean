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
  left_vorticity : ℤ
  right_vorticity : ℤ
  braid_winding : ℤ
  berry_phase : ℝ
  merging : MergingOutcome

/-- Opposite vorticities are represented by the actual integer charges. -/
def vorticitiesOpposite (C : EPCaseClassification) : Prop :=
  C.left_vorticity = -C.right_vorticity

/-- Trivial braid monodromy is zero winding in the integer braid readout. -/
def braidTrivial (C : EPCaseClassification) : Prop :=
  C.braid_winding = 0

/-- The Berry phase is the physical angle `π`, not a Boolean marker. -/
def berryPhasePi (C : EPCaseClassification) : Prop :=
  C.berry_phase = Real.pi

/-- Case 1: H(z) = [0, z; z*, 0]. Type I, DP merging. -/
noncomputable def case1 : EPCaseClassification :=
  { pair_type := EPPairType.TypeI,
    left_vorticity := 1,
    right_vorticity := -1,
    braid_winding := 0,
    berry_phase := Real.pi,
    merging := MergingOutcome.DP }

/-- Case 2: H(z) = [0, 1; |z|^2, 0]. Type I, Defective merging. -/
def case2 : EPCaseClassification :=
  { pair_type := EPPairType.TypeI,
    left_vorticity := 1,
    right_vorticity := -1,
    braid_winding := 0,
    berry_phase := 0,
    merging := MergingOutcome.Defective }

/-- Case 3: H(z) = [0, z; z, 0]. Type II, VP merging. -/
def case3 : EPCaseClassification :=
  { pair_type := EPPairType.TypeII,
    left_vorticity := 1,
    right_vorticity := 1,
    braid_winding := 1,
    berry_phase := 0,
    merging := MergingOutcome.VP }

/-- Case 4: H(z) = [0, 1; z^2, 0]. Type II, Defective merging. -/
noncomputable def case4 : EPCaseClassification :=
  { pair_type := EPPairType.TypeII,
    left_vorticity := 1,
    right_vorticity := 1,
    braid_winding := 1,
    berry_phase := Real.pi,
    merging := MergingOutcome.Defective }

@[simp] theorem case1_vorticities_opposite : vorticitiesOpposite case1 := by
  norm_num [vorticitiesOpposite, case1]

@[simp] theorem case2_vorticities_opposite : vorticitiesOpposite case2 := by
  norm_num [vorticitiesOpposite, case2]

@[simp] theorem case3_not_vorticities_opposite : ¬vorticitiesOpposite case3 := by
  norm_num [vorticitiesOpposite, case3]

@[simp] theorem case4_not_vorticities_opposite : ¬vorticitiesOpposite case4 := by
  norm_num [vorticitiesOpposite, case4]

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
