# Operator volume, observable covariance, and Schwartz uncertainty

## Intake and revision

The 2026-11-17 conversation requested native Mathlib Lean 4 implementation and
publication of a PR following a source audit at
`08c34e03f610b452e03422037949196dc7d92d6d`. The mathematical intake connected
Fourier/Mellin transforms, wavepackets, primal/dual coordinates, Dirac and Hodge
squares, spinor bilinears, split-octonion operators, circular bases, boost/rotation
conversion, Fisher information, Cramer--Rao bounds, and spacetime supersymmetry.

The final implementation instruction was: "implement in native mathlib in lean 4
and publish a PR". The source audit separated existing owner results from the
remaining representation and analytic identifications. This change implements
the concrete operator-volume, observable-Gram, and Schwartz-moment statements
below. It does not infer a covariant spinor PDE or spacetime emergence from a
finite matrix identity.

## Exact contracts

### Positive split-octonion triad

Owner: `InfoGeometry.Lie.SplitOctonionTriadVolume`.

Carrier: the existing full eight-dimensional real `CanonicalZorn` module and
its associative `Module.End` algebra. The chosen generators are the actual
left multiplications by the three existing `ellAxis` elements. The map from
the three-dimensional positive quadratic space is a native quadratic isometry.
`CliffordAlgebra.map` and the existing seven-generator representation construct
the restricted Clifford action.

The target equations are `K_i * K_i = 1`, pairwise anticommutation, and, for the
ordered product `J = K_0 * K_1 * K_2`, `J * J = -1`, `Commute J (K_i)`, and
`(J * K_i) * (J * K_i) = -1`. The existing circular coordinate algebra equivalence
transports these identities. The generic volume-square theorem is reused from
`InfoGeometry.Clifford.ThreeDHurwitz.pseudoscalar_sq`.
The generator-to-bivector identification is explicit:
`(J K_0, J K_1, J K_2) = (K_1 K_2, -K_0 K_2, K_0 K_1)`.

The composition defect of octonion left multiplication is not discarded.
`L_(ell e_i)` is not identified with `L_ell * L_e_i`. Centrality is asserted for
the selected triad, not the entire endomorphism algebra. No faithfulness claim
is made for the full seven-generator Clifford representation.

### Native even Clifford volume and the real Cartan phase

Owner: `InfoGeometry.Canonical.HestenesCartanPhaseTransport`.

The existing native even spacetime Clifford--Pauli algebra equivalence is
composed with the existing interleaved realification, now bundled as a real
algebra homomorphism. Injectivity follows from the two existing faithful maps
and the explicitly involutive coordinate permutation. The intrinsic spacetime
volume maps to the concrete real phase axis; it squares to minus one and
commutes with every element of the even Clifford algebra. Its action on an
arbitrary even element is intertwined with real phase multiplication.

The Cartan compact/noncompact identity is thereby connected to the native
Clifford volume. Complex matrices are an intermediate established coordinate
model; the transported phase operator and its square are real matrices.

The existing `Spacetime.Vec13`, `minkiQ`, and `minkiQ_apply` declarations move
unchanged into `InfoGeometry.Clifford.Spacetime.Basic`; the original spacetime
owner imports them. The even-Clifford owner now imports this exact quadratic
dependency. The Cartan phase owner imports its realification and logarithmic
derivation dependencies directly. These changes preserve the declaration names
and proof bodies and avoid importing unrelated operatorial soldering packages
into the finite Clifford proof.

### Arbitrary finite families of observables

Owner: `InfoGeometry.QuantumGeometry.FiniteObservableGram`.

Carriers: arbitrary finite full complex matrices `Matrix d d Complex`, a native
Euclidean Hilbert space, and arbitrary finite observable index types. There is
no simultaneous diagonalization or pairwise commutativity hypothesis.

Expectation is the actual vector-state pairing. Centering is performed on the
actual matrix action. The columns of `T` are `(A_a - <A_a> I) psi`, and the
uncertainty matrix is their native Gram matrix. Its positivity is unconditional;
normalization and Hermiticity are used exactly when identifying entries with
ordered observable expectations, symmetric covariance, and commutators.

The convention is `K_ab = Im <[A_a,A_b]> / 2`, so `G = C + I K`.
The resulting full matrix is positive semidefinite. The same `G` is proved to
be the right block of the square of the existing doubled operator
`FiniteDiracGramSquare.dirac T`; no abstract desired square is supplied as data.

`FiniteObservableGramCongruence` proves the transformation law for actual
operator combinations: complex rectangular coefficients give `G' = R^* G R`;
real coefficients preserve Hermiticity and give `C' = R^T C R` and
`K' = R^T K R`. The real block `[[C,-K],[K,C]]` is positive semidefinite
because it is the native real Gram matrix of the vectors `v_a` and `I v_a`.
Every two-observable minor satisfies `C_ab^2 + K_ab^2 <= C_aa C_bb`.

`FiniteObservableGramExamples` exercises the imaginary term using the existing
spin raising/lowering matrices. The two Hermitian observables are proved not
to commute. In the first-coordinate normalized state their Gram matrix is
`[[1,I],[-I,1]]`, their covariance is the identity, and their commutator matrix
is `[[0,1],[-1,0]]`. These explicit identities check the sign and factor in the
general convention.

This is positive Hilbert-space algebra. An indefinite Minkowski or Krein form
is not used as a variance. Statistical score identification, estimator
unbiasedness, and attainability of a multiparameter Cramer--Rao bound remain
separate model obligations.

### Actual Schwartz position/frequency uncertainty

Owner: `InfoGeometry.Analysis.SchwartzUncertainty`.

The domain is the real line with Lebesgue measure. The value space is an
arbitrary complex Hilbert space, complete for the Fourier statements. Actual
Schwartz multiplication and differentiation are used; these operators are not
asserted to be bounded on all of `L2`.

The product rule and native Schwartz integration by parts prove the exact real
pairing `<(x-a)f, f'> = -||f||_2^2 / 2`. Cauchy--Schwarz gives the moment bound.
An imaginary constant derivative shift allows an arbitrary frequency center.
The existing native Fourier derivative theorem and Plancherel identity then
give

`||f||_2^2 <= 4*pi * ||(x-a)f||_2 * ||(xi-b) Fourier(f)||_2`.

The Fourier convention is Mathlib's `exp(-2*pi*I*x*xi)`. No normalization or
nonzero-function premise is hidden. For normalized signals, choosing the
actual means gives the usual centered moment interpretation. The module also
exposes the corresponding derivative/momentum norm estimate with `|hbar|`.

## Reused analytic transform result

Pinned Mathlib already contains `mellin_eq_fourier` in
`Mathlib.Analysis.MellinInversion`. It gives the actual logarithmic-coordinate
Mellin/Fourier identity. The repository imports that owner through
`InfoGeometry.Analysis.LaplaceFourierComparison`, which also proves the genuine
Mellin/Laplace change of variables and conditional inversion and uniqueness.
This change deliberately reuses that surface instead of adding another alias.

## Search and acceptance boundary

The source audit covered the exact owners, their imports and consumers, and
alternate-name searches for the target identities. Native Mathlib source was
searched for Clifford map/volume, Gram positivity, matrix adjoints, Schwartz
integration by parts, Fourier derivatives, and Mellin inversion. No freshness
or completeness claim is made for an optional declaration database.

The implementation must pass the maintained source-closure compiler and native
axiom audit, strict placeholder screening, the staged proof gate, and independent
semantic review. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed
by the declaration audit. Exact commands, source hashes, and outcomes belong in
the verification evidence and PR description. A focused source-closure result
does not certify every root Lake target or unrelated historical owner.
In particular, it compiles the extracted spacetime quadratic data and their
even-Clifford consumer, without certifying the historical full `Spacetime`
operatorial soldering import closure.

Remaining integration obligations include a common covariant spinor wavepacket
realization, unbounded-operator domains and self-adjointness, logarithmic `L2`
isometry and dilation-generator transport, geometric curvature identification,
differential current conservation, a statistical spacetime parameter family,
and a full super-Poincare representation. None is encoded as a hidden proof
field or an unproved declaration in the new owners.
