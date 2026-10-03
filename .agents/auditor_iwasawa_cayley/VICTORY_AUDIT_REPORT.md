# Corrective audit report: Iwasawa and split Cayley–Dickson claims

## Disposition

The earlier `SUCCESS (VALIDATED)` conclusion is withdrawn. It promoted finite
matrix identities and an unvalidated pair-operation definition to geometric,
functorial, and KAN claims that the inspected source does not prove. This is a
corrective source audit, not an independent QMS acceptance of the corrected
modules.

## Source findings

### `GrandUnification/IwasawaDiracDecomposition.lean`

The source defines four concrete real `2 × 2` matrices. `D_N_sq` proves the
displayed strictly upper triangular matrix squares to zero.
`iwasawa_dirac_decomposition` expresses an arbitrary traceless matrix
`!![a,b;c,-a]` in a three-matrix basis. It does not define a differential
operator or forms, establish uniqueness, prove a group-level KAN
factorization, or construct a BRST/Koszul complex.

### `Algebra/SplitCayleyDickson.lean`

The source defines a pair carrier and raw `Add`, `Neg`, `Zero`, `Mul`, and
`Star` operations. It provides no additive-group/ring law instances, no proof
of the Cayley–Dickson identities, no functor, and no identification with
split-complex, split-quaternion, or split-octonion algebras. The earlier report
incorrectly described it as a ring extension and a functor.

### `Canonical/KANIwasawaSplitPeirceDiracBridge.lean`

Its explicit matrix identities are valid in their stated finite matrix scope.
However, `matR = [[0,1],[1,0]]` has determinant `-1`; it is not in
`SO(2)`. It normalizes the positive diagonal subgroup by swapping coordinates,
but it does not centralize a nontrivial diagonal boost. Thus it is a Weyl
normalizer action, not an element of `M = Z_K(A)` in the standard
`SL(2,ℝ)` KAN setting. The source also does not construct a Klein bottle
holonomy representation or a geometric Dirac–Kähler operator.

### `GrandUnification/IwasawaCayleyArchetypeDictionary.lean`

This module contains imports and an empty namespace. It defines no master
dictionary theorem or causal-chain API. Its earlier documentation overstated
the imported files' scope and has been corrected.

## Verification boundary

The matrix and pair-operation claims must be verified with their own narrow
Lean builds. A build cannot promote them to the stronger geometric and
functorial claims listed above. No claim of a repository-wide build or
independent audit is made here.
