# Corrective audit report: Iwasawa and split Cayley–Dickson claims

## Disposition

The earlier `SUCCESS (VALIDATED)` conclusion is withdrawn. It promoted finite
matrix identities and an unvalidated pair-operation definition to geometric,
functorial, and KAN claims that the inspected source does not prove. This is a
corrective source audit, not an independent QMS acceptance of the corrected
modules.

## Source findings

### `GrandUnification/IwasawaDiracDecomposition.lean`

The source defines four concrete real `2 × 2` matrices. `matN_R_sq` proves the
displayed strictly upper triangular matrix squares to zero.
`iwasawa_decomposition` expresses an arbitrary traceless matrix
`!![a,b;c,-a]` in a three-matrix basis. `trace_matI_R`, `trace_matJ_R`, and
`trace_matN_R` prove the generators are traceless; `trace_matOne` proves the
identity matrix has trace `2`; `trace_iwasawa` proves the displayed linear
combination has trace zero. The current owner also proves
`iwasawa_decomposition_unique` for these explicit coordinates. These results
do not prove a group-level KAN factorization or any differential-operator
claim.

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

This module contains imports and an empty namespace. Its earlier documentation
claimed that the imports provided a Klein group representation, an SL(2) KAN
trace theorem, and a causal-chain API. Those claims were unsupported and the
documentation has been corrected. No homomorphism connects the abstract
semidirect-product owner to the finite matrix identity in
`KleinParabolicPeirceTwist`.

### `GrandUnification/KleinParabolicPeirceTwist.lean`

The source proves finite projector identities and
`matKR * matA lam * matKR = matA (lam⁻¹)`. The latter is a matrix identity;
`matA` is defined on all reals, not on the group of nonzero real scalars, and
the file does not define a homomorphism from the presented Klein group. The
matrix `matKR` is a Weyl normalizer representative: it swaps diagonal entries
and is not in the centralizer `M`. In the standard SL(2,ℝ) minimal parabolic,
it is outside `P` as well. The Klein relation identity alone does not give a
faithful representation, and its assignment of the glide to an involution
would in any case have a nontrivial kernel because the presented glide has
infinite order.

### `Canonical/KANDiracKahlerTriadArchitecture.lean`

This separate owner proves conditional ring identities for Peirce projectors,
an element family `1 + x • e_plus`, an assumed involution `R`, and arbitrary
ring elements `D_K`, `D_A`, and `D_N`. The hypotheses are explicit, so these
conditional identities are meaningful. The file does not construct the
algebra elements as differential operators, prove a KAN decomposition, or
derive a Klein bottle representation. Its earlier module comments promoted
these conditional formulas to geometric claims and have been narrowed.

The affine Klein presentation and the finite matrix reflection are separate
models here; these files establish no homomorphism connecting them to the
displayed conditional Peirce algebra.

### `Canonical/KANIwasawaSplitPeirceDiracBridge.lean`

This is the more general finite-matrix owner for the displayed `K`, `A`, and
`N` coordinates. It proves determinant/trace identities, Peirce identities,
and the finite Weyl-normalizer action. It does not prove existence or
uniqueness of a global `KAN` factorization, nor does it define a geometric
Dirac–Kähler operator. Its theorem `kan_trace_supported_on_a` is scoped to the
specific matrices shown in the theorem.

### `GrandUnification/MoebiusTomitaPacket.lean`

The previous source had a compile error in the commutant closure proof: its
Unicode-subscript binders were referenced by different, undefined ASCII names.
The proof now uses consistently bound variables and builds. Its former comments
claimed a Tomita–Takesaki/AQFT and Klein/Möbius phase-separation result, while
the code only supplied algebraic hypotheses. The source now states that scope
explicitly, names the reflection conditions by their actual commutant laws,
and defines a Krein symmetry as an involutive isometry of a supplied bilinear
form. This does not assert nondegeneracy, indefiniteness, completeness, or a
geometric origin.

## Verification boundary

The matrix and pair-operation claims must be verified with their own narrow
Lean builds. A build cannot promote them to the stronger geometric and
functorial claims listed above.

The targeted locked builds passed for
`InfoGeometry.GrandUnification.IwasawaDiracDecomposition`,
`InfoGeometry.GrandUnification.IwasawaCayleyArchetypeDictionary`,
`InfoGeometry.GrandUnification.MoebiusTomitaPacket`, and
`InfoGeometry.Canonical.PristineChainKleinDiracKahlerCapstone`. The broader
`InfoGeometry` umbrella build exited with code 1 on unrelated modules, including
unknown `Y1`/`Y2` identifiers in the former version of
`MoebiusTomitaPacket`, missing imports in `InfoGeometry.Topological.All`, a
rewrite failure in `Canonical/FiniteDimensionalCCRNoGo.lean`, and other proof
or resource failures. The repository-wide baseline is therefore not verified
clean by this run. This is a source audit, not an independent QMS acceptance.
