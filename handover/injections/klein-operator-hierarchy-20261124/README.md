# Real Zorn–Klein operator hierarchy

This is the mathematical continuation of draft PR #446. Complete Lean proof
terms have been prepared on the existing real carriers. Native validation
status is recorded separately in `VALIDATION.md`; source review is not a
kernel-check certificate.

## The canonical construction

The vector carrier is the real split-octonion algebra, with
N(a,v,w,b)=ab−v·w. Its point–covector coordinates give a chosen 4+4 Witt
splitting. The Clifford action instead uses a 16-dimensional spinor module,
S=O_s×O_s, with two 8-dimensional summands.

The existing native Clifford lift sends a vector x to

    gamma(x)(s,t) = (x*t, conjugate(x)*s).

The new hierarchy retains this multiplication and its actual noncommutative
endomorphism algebra. It records the real dimensions 8, 16, 64, and 256 and
the obstruction to identifying the full Clifford algebra with End(O_s).
It proves parity through Mathlib's grade involution, rather than replacing
Clifford operations with commuting scalars.

## Added owners

| Owner | Content |
| --- | --- |
| `Algebra/ZornNullIncidence.lean` | Full left-kernel and image dimension 4 for every nonzero null input; internal isotropy; maximality; the zero-input dimension 8; explicit incidence counterexamples. |
| `Canonical/ZornCliffordKleinHierarchy.lean` | Real dimension certificates; existing-carrier readback; native grade involution and spin chirality; exterior-degree-two readback; bivector/vector and bivector/bivector commutator formulas. |
| `Canonical/ZornCliffordSourceVolume.lean` | Fixed source-ordered native Clifford product, its image −chirality, represented square identity, and orientation-sensitive eigenvalues. |
| `Lie/SplitOctonionNullPlaneCovariance.lean` | Explicit canonical/vector kernel equivalence; automorphism transport of kernels and multiplication coefficients; differentiated incidence and fixed-kernel preservation. |

The earlier arbitrary-element 8×8 left matrix and matrix/action bridge in
`Algebra/ZornLeftDeterminant.lean` remain the source for multiplication
matrices. No second Zorn multiplication or Clifford representation is introduced.

For P(x,y)=N(x+y)−N(x)−N(y), define

    beta(x,y) = (gamma(x) gamma(y) − gamma(y) gamma(x))/2,
    A(x,y)z   = P(y,z)x − P(x,z)y.

The two closure statements are

    [beta(x,y), gamma(z)] = gamma(A(x,y)z),
    [beta(x,y), beta(u,v)] = beta(A(x,y)u,v) + beta(u,A(x,y)v).

The second statement retains genuine associative operator multiplication
while preserving the octonionic origins of the generators.

## Geometry supported by the source

For x≠0 and N(x)=0, ker(L_x) is a maximal norm-isotropic real 4-plane.
Its projectivization would be a projective 3-plane; no projective quotient
construction is claimed here. Actual multiplication automorphisms carry it
to ker(L_(phi x)).

For a derivation D, the incidence equation x*y=0 differentiates to
(D x)*y+x*(D y)=0. Only when D x=0 does D preserve that fixed kernel.
In a basis transported by an actual automorphism, the multiplication
structure constants are unchanged. This is an algebraic covariance statement.

The supplied seven-generator order gives an eight-generator volume operator
equal to −C for C(s,t)=(s,−t). Its first summand has eigenvalue −1 and its
second +1. Negating that ordered product matches the chosen chirality.

## Explicit boundaries

The full D4 null quadric, the classical Klein quadric, and the imaginary
split-Cayley hexagon remain different incidence geometries. Triality
permutes the vector and two half-spinor representation types, not those
8-dimensional modules with the 28-dimensional adjoint representation.

An algebra isomorphism Cl(4,4)≃End(S), a full bivector/so(4,4) classification,
an exterior-grade-eight volume identification, homogeneous-space quotients,
smooth gauge connections, and the cotangent symplectic groupoid require
their own constructions. They are not inferred from matching dimensions,
operator parity, a filename, or an algebraic action groupoid.

See `CONTRACT.md` for the causal theorem order and correction ledger,
`INTAKE.md` for the original proposed assertions, and the independent review
reports for the exact reviewed source hashes.
