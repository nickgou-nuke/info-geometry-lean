# Finite-first consumer v5: explicit action and generator transport

NEW consumer only; import the unchanged helper-v4, which got through helper
compilation before the consumer failure. No builds/live edits, budget increases,
transparency changes or new assumptions. Existing files preserved.

Exact first failure: /tmp/qa-a-finite-first-v4-kmlmdf1v/consumer_compile.log48:8
isDefEq1M in matrixStageAut_eq_finitePath's first calc step. This is BEFORE the
concrete Gibbs family specialization. The generic CStar expUnitary equality
was being matched to matrixRealTimeAut with a coerced matrixGenerator. No
proved instance inconsistency follows from this timeout.

V5 replaces that expected-type-heavy calc with small equalities:
1. Whole matrixRealTimeAut equals Unitary.conjStarAlgAut of the actual
   expUnitary(t • matrixGenerator), by the native definitions.
2. DFunLike.congr_fun transports1 to the actual observable f x, following the
   already accepted whole-action/pointwise alignment repair.
3. Obtain generic expUnitary_conjugation_eq_complexPath without an expected
   matrixRealTimeAut target.
4. Explicitly prove the actual matrixGenerator's value equals f H, by rfl;
   transport it through the complex path with congrArg.
5. Compose the equalities with the unchanged finitePath_map result.

Thus generic analytic specialization is not asked to identify the native
application and generator simultaneously through defeq. No new state/action
or wrapper carrier. This remains a source-only proposal; generator equality or
later concrete pointwise specialization may still expose elaboration costs.

All theorem statements, finite witness construction, accepted actual seed
injectivity, alignment-v2 use and final EVERY beta/nonzero tilt existence claim
remain unchanged. Helper v4 import is unchanged, so no duplicate helper v5.
Same1M/500k baseline. Parent supplies independent AA and serialized QA.
