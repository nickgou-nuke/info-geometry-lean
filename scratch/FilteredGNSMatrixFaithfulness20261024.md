# Simple-stage GNS faithfulness candidate

Status: source-grounded, uncompiled; no builds or live edits. Parent AA/serial QA required.

## Exact contract
For the existing directed `ContinuousStarInductiveSystem Stage` and any existing
normalized `CompatibleStateFamily Stage sys`, if each stage is a simple ring,
its actual `globalStageRepresentationStarAlgHom` is injective. Consequently the
actual `algebraicColimitGNSRepresentation` and its `rangeAlgHom` are injective.
Specialize to native `CStarMatrixStage` and `cstarMatrixInductiveSystem`, for
ANY compatible normalized states, not only the trace or faithful states.

No new carrier, representation, state, kernel quotient, or faithfulness field.
Simplicity is a structural sufficient hypothesis in the generic lemma; it is
proved for the concrete matrix stages by transport of Mathlib matrix simplicity.

## Source grounding and reuse
- `Canonical/FilteredGNSHilbertNontrivial.lean`:
  `globalGNSHilbertColimitNontrivial` derives nontriviality from normalized stage
  vacua and their isometric embeddings. Thus the bounded-operator ring is nontrivial.
- `Canonical/FilteredGNSGlobalStageRepresentation.lean`:
  `globalStageRepresentationStarAlgHom` is the actual unital representation,
  transported from the completed upper-tail representation by its cofinal unitary.
- Mathlib `RingTheory/SimpleRing/Basic.lean`: `RingHom.injective` for a simple
  source and nontrivial codomain. `SimpleRing/Matrix.lean`: `IsSimpleRing.matrix`.
  `SimpleRing/Congr.lean`: `IsSimpleRing.of_ringEquiv`.
- `Canonical/CantorBernoulliCStarMatrixTraceState.lean`: `CStarMatrixStage n`
  is the native operator-norm type copy of complex matrices of size 2^n;
  `cstarMatrixInductiveSystem` transports the existing concrete tensor embeddings.
  Use public `CStarMatrix.ofMatrixStarAlgEquiv`, not private matrixEquiv.
- `Canonical/FilteredGNSAlgebraicColimitRepresentation.lean`:
  `algebraicColimitGNSRepresentation_of` identifies the descended map on stages.
  Mathlib `DirectLimit.induction₂` puts two elements at a common stage.
- `Canonical/FilteredGNSFaithfulAlgebraicQuotient.lean`: `rangeAlgHom` is the
  range restriction, and `kernel_eq_bot_of_injective` already turns this result
  into kernel triviality. Feed the new concrete injectivity theorem directly to
  `FilteredGNSFaithfulCStarRepresentation.faithfulStarRepresentation` and other
  conditional consumers; no need to copy their completion constructions.
- Broad search of Canonical/OperatorAlgebra and simple-ring uses found an analogous
  direct-limit induction in `ConcreteCompatibleCuntzFaithfulness`, but its
  `stageMap`/boundary coefficient representation is not this arbitrary-state GNS
  map. `Cl55NeutralFockFaithfulness` uses simplicity on a different Clifford carrier.
  No equivalent arbitrary-state filtered GNS injectivity found in these searches.

## Scope and next concrete consumer
Faithfulness is of the representation, not of the state functional. Pure states
can be nonfaithful as functionals while their full-matrix representations are faithful.
No new analytic dynamics or unbounded Dirac assertion follows.

The existing `tailGNSCompatibleOperatorFamily` already constructs a compatible
bounded family from any finite seed, with bound its norm, on growing native GNS
stages. `FilteredCompatibleOperatorSelfAdjoint.completedOperator_selfAdjoint`
handles stagewise selfadjointness; `FilteredGNSTailStarRepresentation` already
preserves star directly. A stage-one Hermitian Pauli seed gives a non-scalar
completed observable using the injectivity proved here (and scalar preservation).
This is a finite-seed observable on a genuinely growing tower, not a family
accumulating new interactions. `DiracHeatSemigroupBridge.flow_intertwines`
transports an assumed intertwiner through an exponential; its tsum proof is not
an independently constructed summable interaction family.

QA should check all five theorem heads, warnings and axioms. Potential elaboration
risk is native CStarMatrix order-instance alignment and DirectLimit representative
reduction; no kernel evidence is asserted by this draft.
