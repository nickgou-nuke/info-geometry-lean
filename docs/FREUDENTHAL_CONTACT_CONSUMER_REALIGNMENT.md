# Freudenthal contact consumer realignment

## Ground-truth contract

The legacy `fiveGradedBracket` on `FiveGradedCarrier D` fails Jacobi:
`legacy_extreme_charge_jacobi_readout` computes a nonzero extreme/charge
Jacobiator, and `legacy_fiveGradedBracket_not_jacobi` states the global failure.
The earlier symplectic rank-two mixed-triple counterexample concerns a different
three-graded symmetry requirement; it is not a reason to discard the charge
carrier or its symplectic endomorphisms.

The existing constructive replacement is `symplecticContactBracket D`, defined
in `Exceptional/FreudenthalSymplecticContactRepresentation.lean`. Its faithful
linear representation on `ℝ × (FreudenthalCharge J × ℝ)` preserves the bracket
as the associative commutator. The existing `symplecticContactLieRing` and
`symplecticContactLieAlgebra` instances transport the native Mathlib Lie laws
through that injective representation. This supplies global Jacobi without
an assumed table of homogeneous Jacobi cells.

The consumer `Physics/NuclearPristineChainAudit.lean` still exported
`pristine_chain_boundary_packet`, conditional on
`FiveGradedHomogeneousJacobiData D` for the legacy bracket. Its first conjunct
was legacy global Jacobi; the remaining conjuncts simply repackaged independent
finite nuclear operator facts. Source search found no theorem consumers of this
packet; `AllExhaustive.lean` imports the audit module.

Repair: retain the audit module, replace the aggregate packet with actual axiom
inspection of the constructive contact Lie algebra and the existing atomic
nuclear results, and compile native Jacobi examples on the actual five-graded
carrier, including the extreme/charge triple that failed for the legacy bracket.
No new carrier, bracket, proof-data structure, or contradiction theorem is needed.

The generic contact module and finite nuclear operator module remain distinct.
No grade-preserving intertwiner between them, exceptional Lie classification,
or physical identification is asserted.

Followup source tracing found the obsolete record had an arbitrary `bracket`
field while its `cell_jacobi` field hardcoded `fiveJacobiator` of the legacy
bracket. After migrating the consumer, its only use was
`global_fiveGraded_jacobi_of_data`. Both the record and that wrapper are removed.
The lane projections, reconstruction, bilinear maps, and explicit conditional
`global_fiveGraded_jacobi_of_homogeneous` reduction are preserved. The latter is
a valid multilinearity implication, not a proposed realizable legacy completion.
The two owner module descriptions now point to the constructive contact bracket.

Navigation: recursive repo Lean symbol/import search, actual owner definitions,
and `/tmp/freudenthal-consumer-discovery.json` (navigation-only OpenGauss output).

## Verification

The sequential locked build completed successfully (8969 jobs) for:

- `InfoGeometry.Physics.NuclearPristineChainAudit`
- `InfoGeometry.Exceptional.FreudenthalGlobalJacobiFrontier`
- `InfoGeometry.Exceptional.FreudenthalSymplecticContactAudit`

The nuclear audit's nine axiom reports and the existing contact audit report
only standard foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).
Both native Jacobi regression examples compile. No touched-source warnings
occurred; `/tmp/freudenthal-realignment-build.log` contains 70 dependency/package
warning lines. Strict OpenGauss screening of all three touched Lean files passed
with zero traps. Recursive `lean/` reference search found no uses of the three
removed declarations, and `git diff --check` passed.

Independent semantic auditor Poincare returned PASS on the final four-file diff.
Independent QA-A Popper returned ACCEPTED_WITH_LIMITED_SCOPE after rerunning
all three targets successfully (8969 jobs), strict screens, diff/no-hole checks,
and the recursive removed-declaration reference search. QA evidence is in
`/tmp/freudenthal-realignment-qa.log`. This is constructive reuse
and consumer correction, not a new exceptional Lie classification or completion
of the repository-wide counterexample objective.
