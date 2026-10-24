# Actual represented tilt motion v9 — remove failed notation quotation

Exact diagnostic: /tmp/qa-a-tiltseedrealtimenontrivial20261024v8-lhtrbtkh/compile.log.
First error line190: no quot_precheck instance for Lean.Parser.Term.proj in the
parameterized Jstage notation's typed equivalence .toStarAlgHom projection.
Lines194/196 are cascading notation-elaborator/unknown-omega errors; maxErrors=3
stops the run. This log does NOT establish that the new matrix-tower readback
helpers or their concrete specializations pass. Earlier generic declarations
preceding this block emitted no errors in this run.

V9 removes Jstage notation entirely and writes the exact existing
representedMatrixStageMap applied to native CStarMatrix.ofMatrixStarAlgEquiv
explicitly at each occurrence. No new map definition, alternate carrier,
quotPrecheck disable, instance, budget increase, or mathematical change.

Retains v8's two-stage specialization: first arbitrary compatible state on the
native matrix tower, then the actual finiteSeedCompatibleStageStates.
Re-read native FiniteSeedGibbsCStarStates.finiteSeedCompatibleStageStates and
FiniteSeedRepresentedRealTime.seedStageHom / seedRealTimeAut: the constructed
state and actual action remain precisely these native declarations.

All concrete conclusions unchanged: actual seed map faithful; its image of the
raw tilt/switch commutator nonzero; for every beta and nonzero real h, some real
time moves the represented switch under seedRealTimeAut. No new hypotheses.
Uncompiled new sandbox files only; no builds/tests/live edits. V1–v8 and all
other work preserved. Independent QA must now test the previously blocked
matrix-tower abstraction and concrete matching at the same 1M/500k limits.
