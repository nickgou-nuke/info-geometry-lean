import InfoGeometry.Quantum.WittenIndexSupertracePairing

namespace InfoGeometry.Canonical.WittenIndexSupertracePairingCapstone

open InfoGeometry.Quantum.WittenIndexSupertracePairing

/-- Canonical supertrace pairing packet assembled from the finite owner laws. -/
theorem capstone_witten_index_supertrace_synthesis (w : ℝ) :
    (supertraceTerm 1 w = 0) ∧
    (supertraceTerm (-1) w = 2 * w) ∧
    (supertraceTerm 0 w = w) ∧
    (gradedPartitionDifference w w = 0) := by
  exact ⟨supertrace_vacuum_cancellation w,
    supertrace_prime_doubling w,
    supertrace_square_fermion_extinction w,
    graded_partition_cancellation_at_vacuum w⟩

end InfoGeometry.Canonical.WittenIndexSupertracePairingCapstone
