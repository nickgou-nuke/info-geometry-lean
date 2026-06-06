import InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-!
# Fibonacci Yang-Baxter Bridge

The matrix-level Yang-Baxter proof is owned by
`InfoGeometry.Canonical.YangBaxterProof`.  This Fibonacci archive module keeps
the old theorem surface as a bridge and avoids maintaining a divergent scalar
proof with a different root-of-unity convention.
-/

namespace InfoGeometry.Fibonacci.FibAnyonThm4

abbrev F := InfoGeometry.Canonical.YangBaxterProof.F
abbrev R := InfoGeometry.Canonical.YangBaxterProof.R
abbrev B := InfoGeometry.Canonical.YangBaxterProof.B

theorem braid_relation : R * B * R = B * R * B := by
  exact InfoGeometry.Canonical.YangBaxterProof.braid_relation

end InfoGeometry.Fibonacci.FibAnyonThm4
