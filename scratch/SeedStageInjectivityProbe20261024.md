# Isolated native seed-map specialization diagnosis

Uncompiled probe, not motion v11. No builds/tests/live edits, no transparency
attributes, allowUnsafeReducibility, increased budgets, or weaker motion claim.
Limits retain the existing 1M/500k solely for comparable diagnostic receipts.

V10 exact terminal: /tmp/qa-a-motion-v10-pr6kq2gv/compile.log rejects local
reducible on seedStageHom and seedRealTimeAut, explicitly citing simp/typeclass
indexing invariants; then isDefEq times out at concrete injectivity. Do not use
the suggested unsafe override. V9 already established that the abstract-state
matrix tower helpers elaborate; the seed application did not. No specific
instance inequality has been demonstrated: describing it as a proven diamond
would exceed evidence.

## Trace of actual definitions
CantorBernoulliCStarMatrixTraceState:38 CStarMatrixStage n is the operator-norm
CStarMatrix type-copy of MatrixStage n; :98 cstarMatrixInductiveSystem maps via
cstarConcreteMap. It is not a CStar instance installed on raw matrices.
FiniteSeedGibbsCStarStates:136 finiteSeedCompatibleStageStates constructs the
native CompatibleStateFamily with state=finiteSeedStageState and proved transition.
FilteredGNSHilbertColimit:91 GNSHilbertColimit is a completion abbreviation;
its stages and resulting norms depend on that state family.
FilteredGNSRepresentedCStarClosure:47 representedCStarClosure is a closed
StarSubalgebra of bounded operators on that completed Hilbert carrier;
:55 its CStar structure is inherited; :65 algebraicColimitToRepresentedClosure
is codRestrict; :75 its coe lemma reads back the existing representation.
FiniteSeedRepresentedRealTime:198 representedMatrixStageMap composes that map
with algebraicStarDirectLimitOf and the matrix type-copy equivalence.
:229–235 native private abbrev CStar/order/star-order families are local instances.
:253 seedStageHom is a def with inferred result, specialized to the actual Gibbs
family; :268 seedRealTimeAut is matrixRealTimeAut on this same map/family.
FilteredGNSMatrixFaithfulness.globalStageRepresentation_injective provides
unconditional stage faithfulness from native simplicity/nonzero vacuum.

## Probe split
A: seedStageHom_coe_apply_probe states the concrete operator readback and uses
only named composition/coercion/colimit-of equations. Failure here localizes the
problem before Function.Injective/generic theorem specialization.
B: seedStageHom_injective_probe takes congrArg Subtype.val, rewrites A twice,
and applies the existing stage injectivity plus matrix equivalence injectivity.
No full motion candidate and no generic re-proving of faithfulness.
Neither probe is claimed to compile. Parent may compile A then B serially and
record the FIRST error, to avoid cascading failures being counted as diagnosis.

## Parent-safe owner/API repair proposal, pending review
First preference: add explicit result type to seedStageHom and add a small
seedStageHom_coe_apply theorem in the native owner immediately after its def,
under the SAME native instance families and variable telescope. Prove it using
StarAlgHom.comp_apply, algebraicColimitToRepresentedClosure_coe and
algebraicColimitGNSRepresentation_of. This is an application API, not a new state
or wrapper theorem packet. Avoid importing matrix faithfulness into this owner:
the coe law needs no injectivity, so it does not introduce that dependency edge.
Then downstream injectivity consumes only the coe API. If B still fails, inspect
fully explicit elaborated instance arguments under a separately authorized
minimal diagnostics run; do not assert a typeclass mismatch from timeouts alone.

An optional native seedStageHom_apply equation into algebraicColimitToRepresentedClosure
can supply a still shallower rfl checkpoint if A's stage readback fails. Do not
change def to abbrev or globally retag transparency by default. Such source
changes affect elaboration/indexing of existing consumers and require separate
parent review and narrow regression verification; mathematical defeq alone is
not an engineering acceptance argument. No such edit is made here.
After injectivity is accepted, analogous native application API for
seedRealTimeAut may avoid unfolding its dependent closure. Actual seed state,
map and action must remain unchanged; the target remains all beta/nonzero h,
exists t moving the represented switch. This probe establishes none of that yet.

## Source identities at inspection
FiniteSeedRepresentedRealTime.lean:
de19e22b0619c2d9a743dac42355971c4223c27bffeb41033b7ff1135862232e
FiniteSeedGibbsCStarStates.lean:
c549798097822a7823a50d3451efa82d05271e85f819733e49a2406ffccd58e2
FilteredGNSMatrixFaithfulness.lean:
3c4671269246b2e46b263d5f629eac0e900f823e778e9e807043b79d68f3c48b
Earlier motion versions, signed basis and metric work are preserved.
