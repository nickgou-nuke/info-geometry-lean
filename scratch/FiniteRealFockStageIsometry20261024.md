# Native all-index real Fock stage isometries

Exact prerequisite contract, recorded before implementation.
Candidate: FiniteRealFockStageIsometry20261024.lean (new scratch only).

Native carrier is ClNNFockDirectLimitRepresentation.FockStage n, definitionally
Clifford.SpinorSpace (ClNNNeutralChevalleyBridge.Vector n). Activate ONLY the
existing fockNormedAddCommGroup and fockInnerProductSpace as local instances.
No replacement stage, inner product, or assumed isometry.

Imports:
- InfoGeometry.Clifford.FiniteRealFockMetric
- InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation

Exact primary statements for m n : Nat, h : m <= n, x y : FockStage m:
  inner real (fockStageMap m n h x) (fockStageMap m n h y) = inner real x y;
  norm (fockStageMap m n h x) = norm x.
The proof uses Nat.le_induction, native fockStageMap_refl/succ (lines57/65),
and fockTailMap_inner (FiniteRealFockMetric:83). Successor is the actual
zero-head tail inclusion, not a constant coordinate embedding; no index shift
is changed. Coordinate generators shift by Fin.succ at each step as before.

Package fockStageMap itself as fockStageLinearIsometry m n h using
LinearMap.isometryOfInner, following native fockTailLinearIsometry:93.
Application readback is rfl. Derive norm preservation from norm_map and
identity/composition of these bundled maps from fockStageMap_refl and
fockStageMap_apply_trans:113, not new coherence hypotheses. This small bundle
is the actual transition map needed by a real isometric-system consumer.

This is ONLY the first prerequisite toward completion of existing FockInfinity.
No completed Fock space, completed operator, CAR extension, or uniform bound
claim is substituted for that unfinished outcome. No builds/live edits.

## Subsequent reusable scalar-generalization route (outline only)

Existing Canonical.FilteredIsometricInnerProductColimit.IsometricDirectSystem
currently hardcodes complex scalars; its RealDirectLimit restricts to real.
FilteredIsometricInnerProductDirectLimit constructs the complex-valued pairing
and complex scalar action on that real module quotient. HilbertCompletion and
CompatibleOperatorColimit then hardcode complex CLMs. This is not solved by
renaming a type parameter in one file.

Prefer a coordinated scalar-parametric underlying layer for k with RCLike k:
E_i real/complex inner-product spaces, k-linear isometric transitions;
Module.DirectLimit E transitions over k; common-stage k-valued inner pairing;
well-definedness from actual isometry; positivity/definiteness from stage
positivity and equality in the existing module direct limit; native completion
and isometric stage readback. Generalize CompatibleOperatorFamily over k and
its density-based operator/norm arguments, preserving existing complex API
consumers. Use RCLike.re/conj in common proofs, specialize k=real for Fock.
Before editing, account for the current real-restriction carrier and explicit
complex action so existing complex consumers do not silently change carriers.
An equivalent generic carrier requires an explicit native comparison, not an
unproved definitional identification. No such owner edits are authorized here.

For FockInfinity (the existing root DirectLimit), mathlib already provides
Module.DirectLimit.linearEquiv in Algebra/Colimit/Module.lean:242, with
linearEquiv_of and linearEquiv_symm_mk. Transport the constructed metric through
that equivalence onto existing FockInfinity before taking its completion, or
prove the exact isometric comparison to the generic completion. Do not invent
a second algebraic Fock carrier. Operator compatibility and bounds remain
separate derived prerequisites, not fields assumed of the Fock model.

Candidate verification remains independent AA then serialized QA. No compiler,
test, budget change, or source mutation of existing owners in this task.
