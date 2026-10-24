# Represented nontraciality: generic predicate boundary

Uncompiled independent sandbox alternative to v6; preserves all existing files.
Parent/James should select one implementation, not promote parallel duplicates.

## Diagnosis supported by source/log

`/tmp/qa-a-gns-nontracial-readback-v6-ad3app26/compile.log` reports whnf timeout
at 100:9, the explicit `representedSpectralStarOrderedRing` argument in the
concrete theorem's State type. This occurs before its proof. The generic
transport theorem was reported passing by parent. No profiler was run; exact
instance-diamond causation is a hypothesis, not established by that location.

The concrete State annotation and explicit State.functional repeat a dependent
closure/order instance tower specialized to the entire seed state family.
Explicit arguments do not remove the definitional-equality checks between the
Cstar ring projections used by that type and the supplied StarOrderedRing.

## Exact reuse

`OperatorAlgebra.NoncommutativeRenyi.IsTracial` is already exactly
`forall a b, tau (a*b) = tau (b*a)` on a native positive linear map.
A regular `def representedVacuumIsTracial` applies this predicate to the actual
`FilteredGNSVacuumState.representedVacuumState(...).functional` in generic scope.
It introduces no carrier, state, positivity axiom, assumed conclusion or witness
structure. It is definitionally the original cyclicity assertion.

The generic transport theorem retains its original proof after unfolding this
predicate in generic scope. The concrete theorem only concludes the negation
of its application to `finiteSeedCompatibleStageStates H hH beta`; it does not
re-elaborate an explicit concrete State type, order instance or projection.
The finite matrix witness proof and generic transport application remain intact.

## Performance boundary

Use ordinary `def`, not eager `abbrev`. No opacity hack, linter suppression,
new heartbeat increase or owner edit is proposed. The existing v6 budgets
are retained for like-for-like QA comparison. Semireducibility should avoid
unnecessary concrete normalization while still permitting ordinary unfolding.
This is a source-grounded proposed elaboration fix, not a measured guarantee.
The existing dependent-family instance aliases remain, since generic application
still needs those native instances. If this still times out, the next useful
QA diagnostic is the precise new location; do not infer mathematical failure.

The NoncommutativeRenyi import itself imports Mathlib. Its dependency is broad,
but provides the existing predicate without copying its mathematical definition.
No new completion or analyticity claim is made. No compiler/build/test run.
