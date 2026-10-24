# FreshTail v3: explicit native GNS completion coercions

Candidate: `GrowingOnsiteTraceGNSFreshTail20261024v3.lean`.
Source-only repair of frozen v2 from
`/tmp/qa-a-onsite-fresh-tail-v2-8jph1bus/compile.log`.

Mathlib `Analysis/CStarAlgebra/GelfandNaimarkSegal.lean` defines PreGNS,
its seminormed additive group/inner product instances, and GNS as the uniform
completion of that same PreGNS. The native GNSStage is definitionally the GNS
of the compatible family's state, whose trace instance is cstarMatrixTraceState.

The faithfulness proof is factored into a private generic lemma for a positive
functional on a CStarAlgebra, where native PreGNS instances synthesize from the
explicit generic algebra/order context. Its faithfulness premise is discharged
at the concrete application by cstarMatrixTraceState_faithful; no new premise
is added to any public result. Norms and completion coercions are explicitly
typed as f.PreGNS and f.GNS. No custom norm, instance, or Hilbert carrier is made.

All concrete representative occurrences now explicitly coerce into the direct
trace functional's .GNS before use by stage operators or stage inclusions.
The first public result's carrier annotation is now this definitionally equal
.GNS rather than E n, so coercion insertion sees the completion directly.

Actual faithful-state detection, fresh nonzero action at every stage, geometric
summability, and completed operator norm at most two remain unchanged in scope.
All imports are existing native owners; GrowingOnsiteTraceGNSFamily is now
accepted. Frozen v2 is preserved. No budget increases, builds, tests, or live
owner edits. Requires independent AA and serialized QA, including later proof
lines not reached by the maxErrors-limited v2 run.
