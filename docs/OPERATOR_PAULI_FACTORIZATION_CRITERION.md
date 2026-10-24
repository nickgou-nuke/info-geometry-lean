# Exact ordered Pauli factorization

The existing `Bridge/OperatorPauliFactorizationDefect.lean` computes the
noncommutative matrix defect and proves a sufficient pairwise-commuting case.
The new criterion uses that same carrier, multiplication, and ordered channel.

For any ring, the product `operatorSigma t z u v * operatorBarSigma t z u v`
equals `diagonalBlock (orderedQuadratic t z u v)` exactly when

`Commute t z ∧ Commute u v ∧ Commute u (t+z) ∧ Commute v (t-z)`.

The first theorem characterizes vanishing of the existing defect; the second
transports it through the owner's exact defect formula. No division by two,
centrality of the channel, or reverse-order factorization is asserted.
Bounded maintained owner/dependent searches found the defect formula and
sufficient conditions but no equivalent iff in those results.

The native integral-matrix audit verifies a positive family with `z=1-t`
and `v=0`, an explicit noncommuting `t,u` pair, and failure when an
off-diagonal commutator survives. The positive family's channel simplifies
algebraically to `2*t-1`; the audit does not separately certify nonvanishing.

Independent semantic AA and strict screening passed (zero traps).
Parent owner build: session 80879, `/tmp/pauli-criterion-build.log`,
3,094 jobs, exit 0. Parent audit: session 56200,
`/tmp/pauli-criterion-audit.log`, 3,095 jobs, exit 0. Three examples passed,
and three axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Zero source warnings, two existing package notices.
Independent kernel QA accepted this scope: session 17128,
`/tmp/pauli-criterion-qa.log`, 3,095 jobs, exit 0; the shared lock was released.
