# Actual represented tilt motion v7 — uncompiled repair

Source log: /tmp/qa-a-tiltseedrealtimenontrivial20261024v6-w6ky500k/compile.log.
V6 reported timeouts at concrete seed injectivity application and concrete
map-zero simplification (181/204/196); its generic declarations emitted no errors.
The three-error cap leaves the tail unverified.

V7 preserves the theorem interfaces: seedStageHom injectivity; J(raw commutator)
nonzero; every beta and every nonzero real tilt admits some time moving the
represented switch under the actual native seedRealTimeAut. No new flow/carrier.

Repair: unfold only seedStageHom / seedRealTimeAut at concrete proofs, then
abstract finiteSeedCompatibleStageStates by generalize before applying generic
lemmas. The goal now concerns an arbitrary native compatible state family, so
unification need not traverse its Gibbs positivity/normalization construction.
This proves a stronger intermediate fact, not an assumed faithfulness premise.
A generic mapped-nonzero lemma handles map_zero by explicit equality transitivity,
before specialization, avoiding the concrete simp traversal. Native stage
simplicity and globalStageRepresentation_injective still supply faithfulness.

Remove v4's local closure CStar/Ring abbreviations: concrete statements no longer
multiply closure elements, and the native hom's target instances should be used
without an extra Ring projection route. Retain the accepted native matrix-stage
instance families. Generic closure coe/readback rewrites and abstract CStar flow
proof are unchanged. Limits stay 1M/500k; no linter or gate suppression.

QA must validate dependent generalization and that native instance unification
now terminates. No compile/pass claim, no builds/tests/live edits. V1–v6,
centralizing variants, and Fock basis/research work are preserved.
