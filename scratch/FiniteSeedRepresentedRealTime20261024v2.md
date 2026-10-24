# Finite-seed real-time candidate v2

Source: FiniteSeedRepresentedRealTime20261024v2.lean. Uncompiled; original v1
is preserved. No compiler was started or interrupted and no live owner edited.

Repairs from /tmp/qa-a-finiteseedrepresentedrealtime20261024-ovrk1ja4/compile.log:
- Correct Unitary.coe_star_mul_self namespace.
- Supply the explicit algebra type R to Unitary.conjStarAlgAut.
- Move matrix image self-adjointness, mapped density, native exponential
  unitary, group laws, time continuity, and density/exponential commutation
  to FilteredGNSMatrixRealTime with abstract Stage/sys/omega and a genuine
  matrix star-hom f into the existing represented closure.
- Define representedMatrixStageMap abstractly and prove the generic
  matrixStage_realTime_state_invariant there. Its sole twisted premise is
  discharged by the accepted finite-seed theorem in the concrete consumer.
- Infer concrete definition result types from these generic constructors,
  avoiding repeated concrete closure instance inference in annotated bodies.

Actual content retained: seedGenerator is the represented image of the
Hermitian H; representedDensityUnit is its mapped Gibbs unit; seedUnitary and
seedUnitaryFlow reuse the native bounded-generator implementation; seedRealTimeAut
is native unitary conjugation with positive-time sign. Generic zero/add/orbit
continuity proofs apply to these specializations. Concrete seedUnitary_continuous
is provided, and finiteSeed_realTime_state_invariant still asserts invariance
of the actual constructed represented State for all observables, times, and
vacuum choices. No invariance, faithfulness, or flow witness is newly assumed.

No new carrier or state package. Existing generic algebraic readout helper and
transparent actual-state predicate are retained. Heartbeat budgets unchanged.
No analytic-strip, nontrivial-time, or injectivity claim is introduced.

Requires independent AA and serialized QA; no success claim from source alone.
