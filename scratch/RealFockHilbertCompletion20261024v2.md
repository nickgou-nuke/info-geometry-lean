# Real Fock metric and completion on the existing root colimit

New source only: RealFockHilbertCompletion20261024v2.lean.
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

## v2 instance construction repair

Exact diagnostic: /tmp/qa-a-fock-hilbert-completion-eho8ds3y/compile.log.
Replace the four class-valued def plus local-attribute constructions with proper
named local instance declarations. This removes the eight class-definition
reducibility warnings without manually changing transparency or suppressing
linters. Preserve the construction bodies and all carrier/theorem statements.

Expose NormedSpace via fockInfinityInnerProductSpace.toNormedSpace. Derive
UniformContinuousConstSMul from Mathlib Analysis/Normed/MulAction.lean:51
lipschitzWith_smul, followed by LipschitzWith.uniformContinuous. This uses the
constructed norm's actual scalar bound, not a scalar-continuity assumption.
The original complex completion owner contains no extra NormedSpace declaration;
InnerProductSpace itself extends NormedSpace. The explicit local projection and
Lipschitz proof here make the prerequisite to toComplₗᵢ concrete.

Keep the stage-completion rfl readback unchanged: its v1 diagnostic follows the
failed definition of fockStageToCompletion. New QA must confirm that repairing
its scalar-continuity prerequisite removes that downstream error.
Replace the unnecessary simpa in the core scalar field with an explicit real
scalar target and the same LinearMap.congr_fun proof.

Native pairing is now parent-reported accepted (25 declarations, build/axioms/
strict pass). No builds/tests/live edits performed for this repair; v1 preserved.
No budgets, assumed definiteness, replacement quotient, or operator claims.
