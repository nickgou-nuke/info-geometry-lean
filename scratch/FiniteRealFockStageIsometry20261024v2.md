# Finite real Fock stage isometry v2

Source-only successor-proof repair; exact contract and six declarations from
FiniteRealFockStageIsometry20261024.md are preserved.
Diagnostic: /tmp/qa-a-fock-stage-isometry-lhhe3dlb/compile.log.

Replace the no-progress generic simp by an explicitly instantiated
fockStageMap_succ rewrite at m,n,h. Change the resulting inner product to the
actual fockTailMap applications; conclude by fockTailMap_inner.trans ih.
This follows the native fockStageMap_involute successor proof pattern in
ClNNFockDirectLimitRepresentation.lean:98-111.

No change to transitions, index shift, metric, carrier, statements, assumptions,
or budgets. V1 remains frozen. No builds/tests/live-owner edits.
Independent AA and serialized QA remain required. This is still only the
all-index metric prerequisite, not a completed Fock construction.
