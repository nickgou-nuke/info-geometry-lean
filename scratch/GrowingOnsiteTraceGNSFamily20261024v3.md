# Growing onsite trace-GNS family v3: native state alignment

Candidate: `GrowingOnsiteTraceGNSFamily20261024v3.lean`.
Same statements and mathematical contract as the frozen v2; source-only repair.

Diagnostic: `/tmp/qa-a-onsite-trace-family-v2-1uy_fy_q/compile.log`
reports only the final transport simplification mismatch between
`(cstarMatrixTraceStateFamily.state n).functional` and
`(cstarMatrixTraceState n).functional`.

Native source: `Canonical/CantorBernoulliCStarMatrixTraceState.lean`,
`cstarMatrixTraceStateFamily`, explicitly sets `state := cstarMatrixTraceState`.
The repair uses `change ... at he` to express the generic transport equality
with the actual `onsiteStageOperator` maps BEFORE evaluating it at x.
This explicitly aligns the family projection and direct state by definitional
equality, preserving the same native filteredGNSMapCLM. The final simplification
then keeps onsiteStageOperator folded on both sides, rather than exposing the
state projection mismatch again.

No theorem statement, carrier, state, operator, bound, hypothesis, or budget is
changed. All fields of the actual compatible family and the completed operator
outputs remain present. No new assumptions or declarations are introduced.
V1/v2 and FreshTail v2 are untouched. No build/test/live-owner edit was run;
independent AA and serialized QA remain required.
