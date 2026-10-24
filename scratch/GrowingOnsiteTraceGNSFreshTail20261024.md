# Fresh-tail nonzero action in the completed trace-GNS family

Candidate: GrowingOnsiteTraceGNSFreshTail20261024.lean, uncompiled source.
Pending import: InfoGeometry.Canonical.GrowingOnsiteTraceGNSFamily.
No live owners changed and no build/test was run.

The first lemma uses cstarMatrixTraceState_faithful, native preGNS_norm_sq,
and the completion's preserved norm to prove that a nonzero finite matrix
has a nonzero native trace-GNS representative. Representation faithfulness is
not substituted for faithfulness of the state.

The actual raw onsite_fresh_tail_action_ne_zero is mapped through the existing
Matrix-to-CStarMatrix equivalence. Native tracialCommutatorGNS_toPreGNS proves
that onsiteStageOperator sends the fresh switch representative to this nonzero
commutator representative. Existing onsiteCompletedOperator_stage and the
injectivity of the native stageToHilbertDirectLimit linear isometry then show
nonzero action in the SAME completed Hilbert colimit whenever w(n) != 0.

A concrete nonterminating sequence is geometricWeight n = (1/2)^(n+1).
The candidate proves positivity at every n, absolute summability, absolute
sum = 1, and the derived uniform stage-operator norm bound 2. It specializes
the same onsiteCompletedOperator to these actual weights and proves nonzero
fresh action at every stage for that one completed operator.

This does not introduce another family/carrier or a fixed-seed substitute.
It does not assert linear independence of fresh images, an unbounded operator,
a coupled interaction model, or a spectral-triple classification. The explicit
completed operator-norm inequality can be added from the existing family-bound
extension machinery separately; this candidate records its concrete stage
bound and completed fresh action.

All proof inputs are the actual accepted finite/GNS owners plus summability;
no completed nonzero output or separation assumption is supplied. Requires
independent AA and serialized kernel QA. Candidate and contract are staged.
