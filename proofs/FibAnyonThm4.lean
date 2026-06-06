import InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-!
# Fibonacci Yang-Baxter Proof Archive Bridge

The checked matrix-level proof is owned by
`InfoGeometry.Canonical.YangBaxterProof`. This proof-archive copy re-exports the
same theorem rather than carrying an unfinished independent scalar derivation.
-/

namespace InfoGeometry.Fibonacci.FibAnyonThm4

abbrev F := InfoGeometry.Canonical.YangBaxterProof.F
abbrev R := InfoGeometry.Canonical.YangBaxterProof.R
abbrev B := InfoGeometry.Canonical.YangBaxterProof.B

theorem braid_relation : R * B * R = B * R * B := by
  exact InfoGeometry.Canonical.YangBaxterProof.braid_relation

end InfoGeometry.Fibonacci.FibAnyonThm4
