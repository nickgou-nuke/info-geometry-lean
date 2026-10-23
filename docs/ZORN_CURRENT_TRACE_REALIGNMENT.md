# Zorn operator currents and the existing trace split

## Ground-truth contract

The central-scalar obstruction is owned by
`Canonical/ApolloniusScalarOperatorSurprisalNoGo`: scalar identity operators
have zero Zorn-derivation current, and the eight-dimensional carrier cannot
have a nonzero scalar commutator. The actual carrier here remains
`EndCZ = Module.End ℝ CZ`, not a coordinate substitute.

`Quantum/OperatorSurprisalTraceSplit` already defines the generic scalar and
trace-free parts and proves their decomposition and trace identities. Reuse
these definitions directly. `CanonicalZornSurprisalCurrent.surprisalCurrent`
is the existing Chevalley--Eilenberg differential of an operator zero-form;
its value at D is `D.1 * K - K * D.1`.

The missing bridge proves that removing the scalar trace part preserves this
whole current, every current value has trace zero, and two operators have
the same current exactly when their difference commutes with every canonical
Zorn derivation. In particular the full zero-current kernel is the joint
centralizer, not asserted to be only scalars. This does not construct a
nonzero current, prove faithfulness modulo scalars, or evade the finite-CCR
obstruction. No duplicate trace projection is introduced.

## Verification

The shared-lock build of this audit target together with
`InfoGeometry.Canonical.CyclicZornTrialityActionAudit` passed (9,385 jobs).
All four current lemmas report only `propext`, `Classical.choice`, and
`Quot.sound`. No warnings originate in the new modules. Independent semantic
review passed. Independent QA reran both targets successfully (9,385 jobs),
confirmed all eleven combined axiom reports, and found zero traps in strict
screening of the four new Lean files. Scoped diff checks passed. The rerun
reported 852 warning lines: zero from these sources, 849 from dependencies,
and three package/other warnings. Acceptance is limited to the contract above.
