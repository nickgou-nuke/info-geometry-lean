# Finite fragmentation absorption and response stability

Additive follow-up to PR #221, pinned initially to head
`756646098b235aa8b8a0111fea552d921634afd5`. No existing owner or dependency pin is
changed. The PR is stacked on `feat/ms-experimental-evidence`, not merged.

## Dependency order

Strict rank support -> power support -> transient nilpotence -> exact absorbing
projection -> finite fundamental inverse -> response perturbation bounds.

The generic rank lemma is over a semiring. The existing FragmentationDAG,
StochasticGrammar, Option-indexed absorbingCompletion, and SignedNetwork's
finiteGreen are reused. The transient power bound is `max rank + 1`, including
the final transition from a terminal original state to `none`. This need not be
the least nilpotence exponent or the least possible absorption horizon.

The completed stochastic matrix is not nilpotent. Its powers stabilize at the
idempotent matrix whose only nonzero column is the absorbing column, filled
with ones. The finite fundamental inverse belongs to the original transient
block, not to `1 - absorbingCompletion`, which is singular.

## Verification boundary

Draft sources pending the scoped pinned-toolchain workflow. No successful
compilation or axiom audit is claimed by this initial document. The checker
compiles the selected complete repository import closure and audits every
declaration owned by the selected new modules, collecting axiom dependencies
transitively. It does not separately enumerate every declaration in the old
dependency modules. A scoped success is not a full root-package CI success.

## Scientific boundary

The finite row potential is algebraic. A hitting-time random variable,
probability-space expectation, optimal transport optimizer, and calibrated
instrument or chemistry simulator are not constructed here. Exact nilpotence
requires exact support: arbitrarily small nonzero forbidden transitions can
destroy finite absorption. Additivity reduces direct editing risk, not all
integration or regression risk.
