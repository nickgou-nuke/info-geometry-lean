# FreshTail v4 targeted coercion repair

Candidate: GrowingOnsiteTraceGNSFreshTail20261024v4.lean.
Same mathematical contract and statements as frozen v3. Source-only, no builds.
Diagnostic: /tmp/qa-a-onsite-fresh-tail-v3-nnjnyxea/compile.log.

1. cstar_fresh_commutator_ne_zero: apply congrArg with the explicitly typed
   native Matrix/CStarMatrix inverse equivalence to the alleged zero equality.
   Explicitly change the pulled-back equality to the raw matrix commutator.
   This avoids simp's residual toRingEquiv coercion mismatch.
2. onsiteCompletedOperator_fresh_ne_zero: bind the actual completed trace
   representative as x : E (n+1), obtain the native stage readback at x, and
   explicitly align its type to the local native E/S expressions via change.
   Compose equalities using trans instead of rw through a semireducible
   state-family completion coercion. The existing stage isometry's injectivity
   then contradicts the established stage nonzero action.

Generic faithful_toGNS_ne_zero and its specialization are unchanged (they
compiled in v3). All geometric weights, summability, every-stage fresh action,
and completed norm <=2 results are retained. No added assumptions, carriers,
instances, or budgets. No live owners or frozen v3 files edited.
Independent AA and serialized QA are still required. The rotor contract is a
separate artifact and is not an import or dependency of this candidate.
