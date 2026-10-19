# Gate 0 contract: operator exponential quadratic remainder

## Claim and scope

For a complete real inner product space `H`, use the actual unital normed
operator algebra `H →L[ℝ] H` and Mathlib's `NormedSpace.exp`. Prove, for every
continuous linear operator `A` with `‖A‖ ≤ 1`,

```lean
‖NormedSpace.exp A - (1 : H →L[ℝ] H) - A‖ ≤ ‖A‖ ^ 2
```

Then specialize to `A = ε • K` to obtain the bound
`‖exp (ε • K) - 1 - ε • K‖ ≤ ε ^ 2 * ‖K‖ ^ 2` from
`‖ε • K‖ ≤ 1`. The proof uses the norm-convergent operator-exponential
series on the stated complete real inner-product-space carrier; it is not a
finite-dimensional argument. It does not assert self-concordance, Dikin
ellipsoid containment, KMS boundary behavior, or a continuum/colimit result.

## Existing owner facts

- `lean/InfoGeometry/Canonical/KMSInteriorPoint.lean` imports
  `Mathlib.Tactic` and `InfoGeometry.Algebra.FiniteSpinAlgebra`.
- `ExpOp H` is currently an arbitrary function
  `(H →L[ℝ] H) → (H →L[ℝ] H)`.
- `HasBregmanQuadraticBound expOp K` uses the actual step norm
  `‖ε • K‖ ≤ 1`.
- The unit-generator consumer is named
  `bregman_remainder_bounded_of_quadratic_bound` and requires `|ε| ≤ 1`.
- `HasLocalFlowLipschitz` requires one nonnegative constant `C` working
  pairwise for all step-parameter pairs in the unit interval.
  `flow_uniformly_continuous_of_lipschitz_step` derives uniform continuity on
  that interval from this premise, including the `C = 0` case.
- The only theorem consumer found in repo-owned Lean source is
  `dikin_hessian_compatible_cone_transport` in
  `lean/InfoGeometry/Synthesis/HestenesStokesAlgebraicBoundarySynthesis.lean`;
  it forwards the same conditional bound. This consumer does not construct an
  exponential or prove self-concordant containment.
- Mathlib's `NormedSpace.expSeries_hasSum_exp'`, `norm_mul_le`, and
  `norm_pow_le` are candidate ingredients. No generic Banach-algebra quadratic
  remainder theorem was located during Gate 0 scouting. The factorial-tail
  estimate behind `Complex.exp_bound` is a proof route to inspect, not proof
  authority.

## Carrier and conventions

The carrier is the real continuous-linear endomorphism algebra on a complete
real inner product space. Multiplication is composition/operator
multiplication, the unit is the identity map, and `NormedSpace.exp` is the
norm-convergent algebra exponential. The proof must retain the operator carrier;
no scalar or matrix proxy is permitted.

## Relevant imports and dependents

- Owner: `InfoGeometry.Canonical.KMSInteriorPoint`
- Consumer: `InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesis`
- Audit consumer: `InfoGeometry.Synthesis.HestenesStokesAlgebraicBoundarySynthesisAudit`
- Aggregate imports also include `CoverageClosure` and `AllExhaustive`.

## Smallest delta

The concrete operator-exponential remainder lemma and its scalar-step
specialization are kernel-checked. The corrected Lipschitz predicate is
meaningful but remains a hypothesis: a pairwise Lipschitz witness for
`NormedSpace.exp` on scalar multiples of a fixed operator has not been proved.
Keep generic arbitrary-`ExpOp` conditional results explicitly conditional
unless a concrete instantiation is proved.

## Not established

- Self-concordance of a barrier on this operator space.
- Feasibility or containment of a Dikin ellipsoid.
- Existence/uniqueness of an operator flow or KMS semigroup.
- A theorem about infinite-dimensional physical propagators or causal
  distributions.
- Any colimit or boundary-readout theorem.

## Evidence and status

- Discovery receipt: `scratch/kms_operator_exp_discovery.json` (OpenGauss
  navigation evidence only).
- Repo-wide scoped `rg` search covered `lean/InfoGeometry`, `lean/DAG`,
  `proofs`, and `external_refs` for the owner predicates and consumer names.
- A-A and QA-A passed the repaired conditional interface and remainder
  theorem. Sequential locked builds passed for `KMSInteriorPoint`,
  `KMSOperatorExpRemainder`, its audit, and `InfoGeometry.All`; audited theorem
  axiom footprints were `[propext, Classical.choice, Quot.sound]`. QA-A also
  reported zero strict-screen and semantic-vacuity findings. These results do
  not provide a concrete Lipschitz witness for `NormedSpace.exp`.
