# Mode coherence v2: explicitly instantiated successor transport

NEW helper source only; frozen v1 and all native owners unchanged.
Exact QA log: /tmp/qa-a-realfockmodecoherence20261024-svsw9t7r/compile.log.

Injectivity's generic successor rewrites left m<=n proof metavariables. Supply
m,n,h,i and m,n,h,j explicitly to fockModeShift_succ. Fin.succ injectivity
then applies to the original induction hypothesis without new assumptions.

Composition's simp made no progress. Explicitly rewrite the outer shift using
n,k,h and the inner shifted index; rewrite the right side using m,k,hmn.trans h
and i; conclude by congrArg Fin.succ ih. The two composite inequality proofs
have the same proposition, so ordinary proof irrelevance handles their syntax.

All definitions, theorem statements, finite CAR proofs and common-stage
comparison results are unchanged. No new mode carrier, action, assumptions,
budget or transparency settings. No builds or live edits. Source-only v2
awaits independent AA/QA; the completed multi-mode consumer remains frozen and
imports the intended native RealFockModeCoherence, not an alternate helper.
See RealFockCompletedMultiModeCAR20261024.md for the full unchanged scope.
