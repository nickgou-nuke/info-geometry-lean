import InfoGeometry.Quantum.WittenIndexSupertracePairing

namespace InfoGeometry.Canonical.WittenIndexSupertracePairingCapstone

open InfoGeometry.Quantum.WittenIndexSupertracePairing

theorem capstone_witten_index_supertrace_synthesis (w : ℝ) :
    (supertraceTerm 1 w = 0) ∧
    (supertraceTerm (-1) w = 2 * w) ∧
    (supertraceTerm 0 w = w) ∧
    (gradedPartitionDifference w w = 0) :=
  grand_witten_index_supertrace_synthesis w

end InfoGeometry.Canonical.WittenIndexSupertracePairingCapstone
