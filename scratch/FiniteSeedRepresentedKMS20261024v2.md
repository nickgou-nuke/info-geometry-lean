# Finite-seed represented KMS candidate v2 repair contract

Source: FiniteSeedRepresentedKMS20261024v2.lean.
The mathematical contract of FiniteSeedRepresentedKMS20261024.md is unchanged:
actual finite-seed represented State, actual mapped Gibbs density unit,
and the twisted product identity for all elements of the native closure.
No desired identity or invariance hypothesis is added.

Repairs grounded in /tmp/qa-a-finite-seed-represented-kms-pc2hsre0/compile.log:

- After cstarConcreteMap_toMatrixStage, the goal contains concreteMap, whereas
  the transition lemma is stated with rawMap. Use explicit exact application
  of stageInjection_transition; their map definitions are definitionally equal.
- The readback timeout is located at the underscore-filled change expression
  (line 153), before the final stage-state application. Remove that expression
  and the generic rewrites. Compose congrArg of the fully specified continuous
  vacuum functional with explicit represented stage readback and finite-seed
  state readback equalities instead.
- Supply every parameter to the generic dense-extension theorem and both
  algebraic readback rewrites in the final concrete proof, avoiding fresh
  inference of the large dependent family from an apply/rewrite pattern.

No statement, import, density convention, or heartbeat budget changed.
Original candidate preserved. No compilation/tests or live-owner edits.
Kernel validation and final axiom audit remain with the parent's QA lane.
