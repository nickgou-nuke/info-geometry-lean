# Zorn ternary transport and color-isospin projector split: scope

## Intake and owner search

The supplied note cites source revisions `820045719`, `94782074f`, and `868335915`. The inspected default-branch owner files at the time of this change were:

- `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean`: existing alternative associator proof layer, but no public `zornTomitaConj` declaration was visible in the fetched source.
- `lean/InfoGeometry/Physics/Cl55SpinorCartanFock.lean`: existing real 32-dimensional Clifford spinor construction, but no `colorPositiveCompanyProj` or `colorNegativeCompanyProj` declaration was visible in the fetched source.

Those names may exist in another revision/branch or under alternate owner names. No absence assertion about the entire repository is made.

## New theorem contracts

### Algebra/AntiAssociatorTransport

Given an additive homomorphism `J : A →+ A` reversing products and a fully alternating associator, prove:
- `map_assoc_reverse`: the image of `(xy)z - x(yz)` is minus the associator of the reversed images.
- `map_assoc_of_reverse_alternating`: the two minus signs cancel, giving a positive ternary transformation law.

This is a conditional theorem on arbitrary nonassociative multiplication. It does not assume a concrete Tomita involution and does not prove the Zorn-coordinate permutation is multiplicatively anti-homomorphic.

### Physics/ColorIsospinProjectorSplit

Given two color and isospin partitions of unity, define four ordered products and prove:
- `half_sum_eq_one`: `halfPlus + halfMinus = 1`;
- `volume_factorization`: `(colorPos-colorNeg)*(pair-iso) = halfPlus-halfMinus`;
- `halfMinus_four_sector`: four-term distributive expansion.

No numeric rank or idempotence follows from these equalities alone. The claimed 16+16 and 2+6+2+6 ranks require the concrete matrix representation, trace/rank calculations, idempotence and cross-sector commutativity.

## Rejected or deferred promotions

- A zero-hypothesis theorem over *arbitrary* `Ring A` claiming the color occupancy polynomial is an idempotent partition is unjustified without CAR/commuting number-operator hypotheses.
- Algebraic matrix projector counts alone do not provide an identification of physical quark/lepton multiplets or a complete `Spin(5,5)` representation theorem.
- The Zorn frame Nambu determinant coefficient and Jacobiator factor six require source definitions and a specific checked normalization before promotion.

## Verification

GitHub API source-only draft. **Lean/Lake kernel compilation, vacuity, and axiom checks were not run in this environment.** Keep draft and do not merge until source-aligned proof review and the repository's native build gates pass. No manifest or external dependency revisions were changed.
