# Real pairing on existing FockInfinity: exact pre-implementation contract

New scratch source: RealFockInfinityPairing20261024.lean.
Import native FiniteRealFockStageIsometry. Use existing FockStage, fockStageMap,
fockDirectedSystem, FockInfinity, and fockToInfinity. Activate only the existing
finite real metric locally; no norm or completion instance on FockInfinity yet.

1. Define common-stage real pairing of x:FockStage m, y:FockStage n at max m n.
   Prove equality with the inner product transported to ANY common upper k,
   using accepted fockStageMap_inner and fockStageMap_apply_trans. Derive symmetry
   and left/right transition compatibility; no compatibility input is assumed.
2. Bundle the second-variable finite functional and descend it with the EXISTING
   root DirectLimit.Module.lift. Bundle first-variable stage functionals and
   descend again. Result: FockInfinity ->ₗ[real] FockInfinity ->ₗ[real] real.
   The target/source is exactly the existing root quotient, not Module.DirectLimit
   or a new quotient. Prove readback on fockToInfinity representatives.
3. Derive symmetry, bilinearity (from LinearMap structure), nonnegative
   self-pairing, and self-pairing=0 iff vector=0 from actual finite inner-product
   definiteness. A zero finite representative maps to zero by the native
   injection's map_zero; no injectivity/definiteness premise is added.

Only steps1-3 are claimed. No InnerProductSpace.Core, norm, completed carrier,
completed operator, or analytic norm bound is constructed in this candidate.
This is an intermediate native metric prerequisite, not the full completion.
No builds/tests/live-owner edits, replacement carrier, or budget changes.
Independent AA and serialized QA required after source review.
