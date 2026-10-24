# Canonical quotient shift and its invariant uniform functional

Contract: instantiate the existing `InfoGeometry.NCG.CuntzSystem` on
`ComplexStarCuntzAlg Bool` with the actual generators `Sℂ` and their proved
Cuntz relations. Reuse its `canonicalShift`; do not introduce a second shift.

Prove, for every quotient element x and canonical branch b,
`φ (Sℂ b * x * Tℂ b) = (1 / 2) * φ x` using
`uniform_generator_twisted_S` and `complexified_ortho`.
Summing the two branches proves `φ (canonicalShift x) = φ x`.
Here φ is the normalized uniform `quotientProductFunctional` already proved
positive on all star-squares.

Owners: `NCG/CuntzColimitKMSTiltGNS.lean` (CuntzSystem and canonicalShift),
`Algebra/CuntzComplexificationAlgEquiv.lean` (relations),
`Physics/ComplexStarCuntzRedesign.lean` (star), and
`OperatorAlgebra/CuntzComplexStarGeneratorCyclicity.lean` (cyclicity).

The older `Canonical/CuntzCanonicalEndomorphismBridge.KMSStateFunctional`
assumes scaling for every CuntzTwoAlgebra. Fixed canonical-generator scaling
does not discharge that universal field. No maximum entropy, convergence,
ground-state, or completed GNS conclusion is inferred from invariance here.

Status: parent audit and independent QA passed (9423 jobs each, exit zero).
Logs: `/tmp/cuntz-shift-state-audit.log` and `/tmp/cuntz-shift-state-qa.log`.
All four audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. There are zero own-source warnings; dependencies emit 732 source
warnings and two package notices. Strict screening found zero traps.
Independent semantic review passed for the fixed canonical-family scope.
