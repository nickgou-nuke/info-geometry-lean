# Actual represented tilt motion v10 — local reduction boundary

Diagnostic: /tmp/qa-a-motion-v9-bjildmql/compile.log reports whnf timeouts at
229/246 (concrete helper applications) and isDefEq at242 (concrete nonzero
declaration). Generic and matrix-tower abstract-state helpers emit no errors.
The capped final motion proof remains unverified.

Source comparison: native seedStageHom is representedMatrixStageMap applied to
finiteSeedCompatibleStageStates; native seedRealTimeAut is matrixRealTimeAut
applied to that same map/family. The family is a constructed CompatibleStateFamily
whose state field is finiteSeedStageState. No source-level mismatch was found.
The log does not diagnose a specific typeclass diamond; repeated deep reduction
of the constructed family is the hypothesis targeted by this revision.

V10 retains every v9 theorem statement and proof. Before concrete declarations,
locally mark finiteSeedCompatibleStageStates irreducible and the two thin native
wrappers seedStageHom/seedRealTimeAut reducible. This makes definitional alignment
expose the wrapper applications while preventing elaboration from expanding
Gibbs state construction through the dependent representation carrier.
No global attributes, owner edits, new carrier, replacement state, assumed output,
axiom, new hypothesis, timeout increase, or weaker conclusion. Kernel definitions
and their checking are unchanged: local reducibility is an elaboration control,
not opacity that removes a proof obligation. Mathlib uses local irreducible
boundaries (e.g. RingTheory/Kaehler/TensorProduct.lean:32).

The actual native seedRealTimeAut must move the represented switch for some
real t, for every beta and nonzero real h. All v9 generic proofs remain intact.
This is uncompiled; QA must test whether the narrower reduction path suffices.
Limits remain 1M/500k. No builds/tests/live edits. Prior candidates preserved.
