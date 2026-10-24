# Real Fock metric and completion on the existing root colimit

New source only: RealFockHilbertCompletion20261024.lean.
Native import: InfoGeometry.Clifford.RealFockInfinityPairing, promoted byte-identically
from scratch/RealFockInfinityPairing20261024v2.lean after its sandbox all-gates PASS.
Dependency SHA: 9c83a8f82e0fe0e004519a6317700bc4c69a5ddaf7a77f6a6637381f7d0b8d8b.
Parent reports native QA running. This new completion candidate is uncompiled.

## API grounding and exact construction

Existing FockInfinity is the root DirectLimit in
Clifford/ClNNFockDirectLimitRepresentation.lean:137; keep that exact carrier.
FiniteRealFockStageIsometry supplies the actual transition isometries. The
native pairing supplies fockInfinityPairing, symmetry, nonnegative self-pairing,
self=0 iff vector=0, and fockInfinityPairing_same_stage. No definiteness input.

Mathlib/Analysis/InnerProductSpace/Defs.lean:139-157: InnerProductSpace.Core
requires Hermitian symmetry, re nonnegativity, additivity, scalar law and
definiteness. Over real scalars conjugation/re reduce to identity. Discharge
all fields using that actual descended bilinear pairing. Derive named norm and
inner-product structures using Core.toNormedAddCommGroup and ofCore (same
construction used by Canonical/FilteredIsometricHilbertCompletion:41-74).
All newly named instances are activated LOCALLY, so complex owners and consumers
are unchanged. Consumers must re-enable these exact named instances locally.

The algebraic stage injection is the existing root DirectLimit.Module.of,
bundled by LinearMap.isometryOfInner using actual finite pairing readback.
Root DirectLimit.Module.of_f proves transition compatibility.

RealFockCompletion is only an abbreviation for UniformSpace.Completion
FockInfinity with the constructed uniform structure, not a replacement quotient.
Mathlib/Analysis/InnerProductSpace/Completion.lean:89 supplies the completed
InnerProductSpace; completeness is the existing completion instance.
Mathlib/Analysis/Normed/Module/Completion.lean:49 supplies toComplₗᵢ, used directly
for stage embeddings by composition. No duplicate completion embedding proof.
UniformSpace.Completion.denseRange_coe plus DirectLimit.exists_eq_mk proves
density of the UNION of stage ranges (not density of each finite stage).
Expose finite inner readback, norm preservation and transition compatibility.

## Boundaries

This constructs the real metric and completion of the actual algebraic tower.
It does not yet descend individual creation/contraction operators, establish
index-shift intertwining, or prove completed CAR/adjoint identities. Those need
actual compatible operator families and bounds; none are assumed here.
No new carrier hierarchy, budgets, transparency changes, live edits or builds.
