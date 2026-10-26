# Drazin / Moore–Penrose / Kitaev intake: exact scope and rejection boundaries

The uploaded note proposes universal Zorn Drazin, Moore–Penrose and two-cell Kitaev claims. The current repository already has native Drazin and Moore–Penrose owners, including `Canonical/DrazinCoreFlow` and `Canonical/MoorePenroseDrazinObstruction`, plus Peirce and Zorn laws in `Algebra/ZornAlternativeLaws`.

## Corrections

### Drazin

The statement `T² = λT` does not imply `T` is its own Drazin inverse. The matrix `diag(2,0)` over integers satisfies `T²=2T` yet `T³≠T`. A Drazin inverse of `diag(2,0)` over the rationals is `diag(1/2,0)`. In particular, `T` is its own Drazin inverse only under additional normalization (e.g. `T³=T` plus compatible index conditions). Over a general ring the coefficient may not even be invertible.

In an alternative but nonassociative Zorn algebra, the conventional Drazin definition is not automatically meaningful: one must specify associativity of the subalgebra and the inverse algebra laws. Power-wise polynomial identities alone are not the three standard Drazin axioms.

### Moore–Penrose

An identity `(P P*)P = μ P` is a **Gram-scaled triple identity**, not the first Penrose equation unless `μ=1` or the generalized inverse is normalized appropriately. The candidate `P*=P` for `P=diag(2,0)` plainly fails `PP*P=P`. Furthermore, coordinate swap is not automatically a proper anti-involution of the Zorn product, and the choice of norm or order matters.

### Kitaev

The finite 4×4 bond and edge-support calculation verifies an exact two-site zero-mode kernel: the bond acts only on interior coordinates 1,2; its left and right edge supports lie in its kernel. This does not imply physical Majorana self-adjointness, CAR anticommutation, a many-site transfer operator, a spectral gap or a topological phase.

## Added modules

- `Canonical/InverseNormalizationAudit.lean`: a nontrivial scaled core that refutes the self-Drazin and unscaled Penrose inverse assertions.
- `Canonical/KitaevTwoCellBoundary.lean`: explicit integer-matrix bulk, edge, and support projectors and annihilation identities.

## Verification and merge policy

This is source committed through GitHub API, not a kernel check. The runtime lacks Lean/Lake, so `by decide` and all other tactic proofs must be confirmed by a pinned-toolchain narrow build, axiom/vacuity audit, and the repository's required integration checks. Do not merge until checks pass. No manifest, pin, or existing Lean owner was changed.
