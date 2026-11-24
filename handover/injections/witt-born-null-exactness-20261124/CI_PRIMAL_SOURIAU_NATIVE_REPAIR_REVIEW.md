# Independent Primal/Souriau repair review

Baseline: recovered checkout at
`c97caca572514f128e846212ca30f050414dabac`.
Evidence: exact three owner logs from CI run `45416776463`, diagnostic
execution `c73ae23678dd44f398d46c2a8ef7184f`.

Reviewed worktree owner hashes:

| Owner | SHA256 |
| --- | --- |
| `Algebra/ZornPrimalDual.lean` | `8da3339b0dfcccc3a1f58525ec6ec8e3309b05a6fadd346cfccade2895891a6c` |
| `Canonical/SouriauAffineActionGroupoid.lean` | `b987decf4e7f5031b41c18724b39d3e03bdfcde418ed1c9c08e61c4d9bbd78ba` |
| `Geometry/SouriauCotangentGraphSigns.lean` | `cb0bdc1353577fde2931d905d7f3309b5d0deb1cdafc565ea6e53929a81df9cf` |

## Findings

No source-level blocker was identified in these exact deltas.

**Primal/dual.** The eight reported mixed-product goals retain projections
of the explicit `ZornVectorMatrix.neg`. Restoring its definition in the
existing simplifier list directly reduces those stuck projections to real
scalar negation before `ring`. The earlier native-subtraction rewrite stays
in place. The `norm_encode` proof changes only the CI-reported unnecessary
focused sequencing to ordinary sequential `simp` and `ring`; its scalar
identity and all operator formulas are unchanged.

**Affine action groupoid.** `@[instance_reducible]` is precisely the
attribute recommended by the native class-definition warning. It changes
reducibility of the parameterized action definition, without registering a
global action instance or changing its cocycle-dependent operations. Pinned
Mathlib `Topology/Algebra/Module/ContinuousLinearMap/Basic.lean` explicitly
declares the deprecated `ContinuousLinearMap.add_apply` as an alias of
`_root_.add_apply`; using that target preserves the exact evaluation rule
while removing the reported deprecation warning.

**Cotangent graph signs.** The general scaling theorem remains unchanged:
its coefficient is `1 - 2*c`. At `c = 1`, `norm_num at h` evaluates the
remaining real coefficient and normalizes the unit scalar action. At
`c = -1`, `norm_num [neg_one_smul] at h` additionally identifies the graph
of `(-1) • B` with the graph of `-B`. The retained conclusions are respectively
`-B u v` and `3 * B u v`, matching both the actual general theorem and the
reported unsimplified targets. No skewness hypothesis or sign convention is
weakened or replaced.

## Validation boundary

The reviewer read the worktree diff, affected declaration context, each
native diagnostic log, and the pinned continuous-linear-map alias source.
No imports, theorem statements, dependencies, gates, or linter options change.
All actual diagnostics emitted for these three owners are addressed at their
source locations.

This receipt is source review only. No compiler, test, build, syntax parser,
axiom audit, tracked-source edit, or GitHub mutation was performed by the
reviewer. The parent's unchanged strict suite must establish native
acceptance; diagnostic elaboration is not acceptance.
