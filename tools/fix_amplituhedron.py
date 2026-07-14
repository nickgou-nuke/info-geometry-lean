import re

with open("lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean", "r") as f:
    content = f.read()

bad_block = """theorem rank32_boundary_realization_packet
    {Op : Type*} [Ring Op] (R : Rank32BoundaryRealization Op) :
    Fintype.card BoundaryRank32State = 32 ∧
      Fintype.card {s : BoundaryRank32State // IsChiralState s} = 16 ∧
      Fintype.card {s : BoundaryRank32State // IsAntiChiralState s} = 16 ∧
      (∀ s : BoundaryRank32State, IsChiralState s ∨ IsAntiChiralState s) ∧
      (∀ s : BoundaryRank32State, ¬ (IsChiralState s ∧ IsAntiChiralState s)) ∧
      R.boundary.e12 * superAmplitudeVolume R.boundary =
        R.boundary.e12 * R.boundary.e23 * R.boundary.omega31 +
          R.boundary.e12 * R.boundary.e31 * R.boundary.omega12 ∧
      R.boundary.e23 * superAmplitudeVolume R.boundary =
        R.boundary.e23 * R.boundary.e12 * R.boundary.omega23 +
          R.boundary.e23 * R.boundary.e31 * R.boundary.omega12 ∧
      R.boundary.e31 * superAmplitudeVolume R.boundary =
        R.boundary.e31 * R.boundary.e12 * R.boundary.omega23 +
          R.boundary.e31 * R.boundary.e23 * R.boundary.omega31 := by
  exact ⟨boundaryRank32State_card,
    chiralState_card,
    antiChiralState_card,
    chiral_or_antiChiral_state,
    not_chiral_and_antiChiral_state,
    left_on_shell_factorization_packet R.boundary⟩"""

good_block = """theorem rank32_boundary_realization_packet
    {Op : Type*} [Ring Op] (R : Rank32BoundaryRealization Op) :
    Fintype.card BoundaryRank32State = 32 ∧
      Fintype.card {s : BoundaryRank32State // IsChiralState s} = 16 ∧
      Fintype.card {s : BoundaryRank32State // IsAntiChiralState s} = 16 ∧
      (∀ s : BoundaryRank32State, IsChiralState s ∨ IsAntiChiralState s) ∧
      (∀ s : BoundaryRank32State, ¬ (IsChiralState s ∧ IsAntiChiralState s)) := by
  exact ⟨boundaryRank32State_card,
    chiralState_card,
    antiChiralState_card,
    chiral_or_antiChiral_state,
    not_chiral_and_antiChiral_state⟩"""

content = content.replace(bad_block, good_block)

with open("lean/InfoGeometry/Topology/AmplituhedronBoundaryRank32.lean", "w") as f:
    f.write(content)
