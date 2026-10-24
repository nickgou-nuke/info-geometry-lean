# Completed same-mode CAR and both adjoints: implementation contract

New source RealFockCompletedSameModeCAR20261024.lean only. Import intended native
RealFockCompletedCoordinateAction (pending dependency) plus existing finite
FiniteFockCLMReflexivePair and FiniteRealFockAdjoint. Reuse exact metric instances
and the bounded-action topology/uniformity projections. No replacement carrier.

Prove a common finite representative lemma above any prescribed birth stage
for two algebraic Fock vectors. Use existing transition readbacks to move both
to max m (max n p), without a representative/image assumption on the vectors.

At any stage above birth, derive completed same-mode square-zero/CAR evaluations
from completed stage readbacks and existing finite CLM identities. Extend to
all completion vectors via closed equality and Completion.induction_on. For
adjointness, derive the finite common-stage inner identity from the accepted
finite metric adjoint theorem, then extend simultaneously in both variables
via Completion.induction_on₂. Use Mathlib eq_adjoint_iff and adjoint_adjoint
with the correct orientation to conclude both actual CLM adjoint equalities.

All outputs use fockCompletedCreationCLM/fockCompletedContractionCLM. No assumed
CAR, adjoints, norm bounds, compatibility, or new law-bearing structure. No
builds, live edits, budgets or transparency changes. Source-only pending AA/QA.

## Required next extension: multi-mode

Same-mode closure is NOT full multi-mode CAR. Next prove shift injectivity and
composition for fockModeShift. Lift existing finite FockSpaceCAR cross-mode
identities to actual coordinate CLMs, using the existing zero-form equivalence
readbacks, not another exterior carrier. Then apply the same common-stage and
density method for SAME birth i,j: creations anticommute, contractions anticommute,
D_i*C_j+C_j*D_i=(if i=j then 1 else 0). For different birth stages compare indices
after transport to a common upper stage, and prove independence using shift
composition/injectivity. Do not compare raw indices across birth stages.
No multi-mode implementation or acceptance is claimed by this file.
