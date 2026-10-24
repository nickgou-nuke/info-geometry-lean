# Completed same-mode CAR and both adjoints: implementation contract

New source RealFockCompletedSameModeCAR20261024v2.lean only. Import intended native
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

## v2 bounded layout/type repair

Exact diagnostic /tmp/qa-a-fock-same-mode-car-dnypt14i/compile.log: the multiline
hp expressions ended at isClosed_eq before their arguments, leaving T2Space
metavariables and parser errors. Introduce two small named closed-set helpers
with explicit RealFockCompletion domain (and product domain for the inner law),
typed continuous functions and fully applied isClosed_eq. Each hp branch now
calls the matching helper with the actual completed CLMs on its own indented
line. These helpers prove topological closedness, not assumed CAR/adjoint laws.
All prior theorem statements and finite/density/adjoint arguments preserved.
No budgets, transparency changes, builds or live edits. Frozen v1 unchanged.
