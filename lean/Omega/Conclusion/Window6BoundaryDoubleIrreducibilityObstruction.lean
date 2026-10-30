import Omega.Conclusion.Window6BoundaryCliffordIdealExactSplit
import Omega.GU.Window6Center2RankExcludesSimpleGroups

namespace Omega.Conclusion

structure Window6BoundaryDoubleIrreducibilityData where
  simpleEnvelope : Omega.GU.CompactConnectedSimpleLieType

def conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data :
    Window6BoundaryTripleSpinorRigidityData :=
  conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_boundary_data

def conclusion_window6_boundary_double_irreducibility_obstruction_split_data :
    conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_data :=
  ()

def conclusion_window6_boundary_double_irreducibility_obstruction_center_data
    (D : Window6BoundaryDoubleIrreducibilityData) :
    Omega.GU.Window6Center2RankExcludesSimpleGroupsData :=
  { envelope := D.simpleEnvelope
    boundaryCentralRank := 3
    boundaryCentralRank_eq_three := rfl }

def Window6BoundaryDoubleIrreducibilityData.noConnectedSimpleEnvelope
    (D : Window6BoundaryDoubleIrreducibilityData) : Prop :=
  Omega.GU.Window6Center2RankExcludesSimpleGroupsData.no_compact_connected_simple_envelope
    (conclusion_window6_boundary_double_irreducibility_obstruction_center_data D)

/-- Encoded rank exclusion associated with the paper label
`thm:conclusion-window6-boundary-double-irreducibility-obstruction`. It combines fixed
boundary-spinor rigidity and split-rank bookkeeping with exclusion of the supplied simple Lie
type at boundary central rank three. It does not assert that an arbitrary compact irreducible
model exists or fails to exist: the boundary datum and rank-three premise are fixed inputs. -/
theorem encoded_window6_boundary_rank_exclusion
    (D : Window6BoundaryDoubleIrreducibilityData) :
    Window6BoundaryTripleSpinorRigidityStatement
        conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data ∧
      conclusion_window6_boundary_double_irreducibility_obstruction_split_data.conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting_k0_ranks ∧
      D.noConnectedSimpleEnvelope := by
  have hBoundary :
      Window6BoundaryTripleSpinorRigidityStatement
        conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data :=
    paper_conclusion_window6_boundary_triple_spinor_rigidity
      conclusion_window6_boundary_double_irreducibility_obstruction_boundary_data
  have hSplit :=
    paper_conclusion_window6_boundary_clifford_ideal_exact_12_plus_200_splitting
      conclusion_window6_boundary_double_irreducibility_obstruction_split_data
  have hSimple : D.noConnectedSimpleEnvelope := by
    simpa [Window6BoundaryDoubleIrreducibilityData.noConnectedSimpleEnvelope,
      conclusion_window6_boundary_double_irreducibility_obstruction_center_data] using
      Omega.GU.paper_window6_center_2rank_excludes_simple_groups
        (conclusion_window6_boundary_double_irreducibility_obstruction_center_data D)
  exact ⟨hBoundary, hSplit.2.2.2, hSimple⟩

end Omega.Conclusion
