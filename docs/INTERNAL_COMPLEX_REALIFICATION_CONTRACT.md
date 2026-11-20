# Internal complex structures, Clifford phases, and real thermodynamics

## Intake and mathematical base

The requested extension expresses the existing finite operator and information
geometry in a real Hestenes-style language: an internal square-minus-one
operator, a bivector phase acting on real even spinors, and explicit grading
and Krein conventions. The implementation starts from PR #413, commit
`4d7b8d4b2e22768abe6d9b13990c2da9fe495ffb`.

The supplied article is J. Patera and H. Zassenhaus, *The Pauli matrices in n
dimensions and finest gradings of simple Lie algebras of type A_(n-1)*,
J. Math. Phys. 29, 665–673 (1988),
[DOI 10.1063/1.528006](https://doi.org/10.1063/1.528006).
Its clock–shift grading is related to, but is not itself, Hestenes' real Dirac
formalism. The latter comparison uses David Hestenes,
[*Real Dirac Theory*](https://davidhestenes.net/geocalc/pdf/REAL_DIRAC.pdf),
§2, equations (2.1c)–(2.13), and §3, equation (3.22).

## Contracts to implement

### Internal real matrix phases and homogeneous planes

Reuse `Quantum.Realification.realify`, its faithful multiplication map, the
real block operator `internalJ`, and the proved range/commutant equivalence.
The new phase coefficients are real matrices `a • 1 + b • internalJ`.
Prove their actual multiplication, their action on realified operators, and
the associated real rotor law. The native phase definitions have no external
complex scalar; complex inputs occur only in comparison theorems.

Transport the existing ordered Weyl-word product and bracket identities with
their order-dependent phase coefficients. Identify the image of a complex
homogeneous line as the real plane spanned by `realify W` and
`internalJ * realify W`. Multiplication of these components must follow from
the actual product law. Do not assert a new finite direct-sum or fineness
classification from the existing scalar-multiple predicate alone.

For the real image of complex trace-zero operators, require both
`trace M = 0` and `trace (internalJ * M) = 0`, together with commutation with
`internalJ`. Ordinary real trace zero alone loses the imaginary trace
condition.

### Native even Clifford right action

Use Mathlib's `CliffordAlgebra.even` and the repository's
`Clifford.EvenRegularRepresentation`. For an orthogonal normalized definite
two-plane, construct the even bivector from the actual Clifford generators
and prove its square is minus one. Include a concrete instance in an existing
real Clifford carrier, rather than supplying the desired square law as the
only datum.

Right multiplication by this bivector squares to minus the identity and
commutes with every left regular observable. Connect its real phase plane
to this module action and, where appropriate, the existing `RealKVect`
category. No global centrality assertion about an arbitrary Clifford
bivector is permitted. Clifford parity fixes the bivector; reversal negates
it. A bivector generator and its trigonometric rotor are distinct objects.

### Native analytic and thermodynamic transport

Package the existing faithful realification as a real star-algebra
homomorphism. Prove compatibility with actual matrix exponential, positive
functional-calculus logarithm and square root, and the inverse of a strictly
positive matrix. Use native CFC naturality and proved continuity, not fields
that assume the desired logarithm equation.

The ordinary real trace satisfies `trace (realify A) = 2 * re (trace A)`.
Consequently use the existing normalized state `state rho = realify rho / 2`.
The intended normalized identities are

\[
\log(\Gamma\rho/2)=\Gamma(\log\rho)-\log 2\,I,\qquad
S_{\mathbb R}(\Gamma\rho/2)=S_{\mathbb C}(\rho)+\log2,
\]

\[
D_{\mathbb R}(\Gamma\rho/2\Vert\Gamma\sigma/2)
=D_{\mathbb C}(\rho\Vert\sigma).
\]

Connect partition functions and normalized Gibbs states to these identities.
Preserve noncommuting Hermitian operators. For the actual relative modular
action, prove an intertwining equation on the realification image:

\[
(\Gamma\sigma/2)\,\Gamma X\,(\Gamma\rho/2)^{-1}
=\Gamma(\sigma X\rho^{-1}).
\]

The full doubled real Hilbert–Schmidt carrier has more dimensions than the
realification of the complex Hilbert–Schmidt carrier. An equality between
their full modular matrices is therefore not a valid target.

These analytic theorems live in the real matrix representation. The native
even Clifford phase is connected to its real matrix phase coordinates by an
explicit intertwiner. That map alone does not represent the entire matrix
operator algebra, its positive Hilbert adjoint, and its functional calculus
inside `Cl(5,5)`. No such full Clifford analytic identification is claimed.

### Grading and Krein compatibility

Keep separate the internal phase generator, complex conjugation, Clifford
parity, Pauli degree, and a Krein fundamental symmetry. Positive density
operators and their logarithms use the positive Hilbert adjoint. A Krein
self-adjoint operator is not thereby positive.

For a real fundamental symmetry `eta`, the Krein adjoint is
`eta * transpose T * eta`. A skew-transpose phase generator is Krein-skew
when it commutes with `eta`; the neutral doubled convention that
anticommutes with the phase generator instead makes it Krein-self-adjoint
and anti-isometric. Preserve the existing doubled-space convention.

## Paper convention audit

With the article's `A D A⁻¹ = zeta D`, its unreduced ordered words obey

\[
(A^aD^d)(A^{a'}D^{d'})
=\zeta^{-a'd}A^{a+a'}D^{d+d'}.
\]

Equation (5.13a) has the corresponding commutator coefficient. Substituting
the relabeling in (5.12) into it yields the opposite sign to the printed
(5.13b). The implementation follows the proved ordered product; this is a
bounded correction of that displayed convention, not a new classification.
Its existing Weyl owner uses `Z X = omega • (X Z)`; comparison with those
paper words sets `X = A`, `Z = D`, and `omega = zeta⁻¹`.

For even dimension, the article's determinant-one normalization has
`A^N = D^N = -I`. Reducing word exponents modulo `N` then introduces carry
signs. The ordinary unsigned clock–shift construction is not silently
identified with that normalization. Realification preserves the signed power
relations; any finite indexing or wraparound claim needs its own proof.

## Reuse, acceptance, and scope

The source audit identified the existing owners `Quantum.Realification*`,
`Quantum.RealKCategory`, `Quantum.SylvesterWeylBraidBridge`,
`Weyl.WeylDisplacement`, `Canonical.SylvesterGrading`,
`Clifford.EvenRegularRepresentation`, `Clifford.Clifford55`,
`Canonical.MatrixRelativeModular`, and `Canonical.MatrixGibbsEntropy`.
The implementation extends these owners rather than replacing their
noncommutative carriers with scalar models.

Candidate generation, semantic acceptance, and final verification have
separate agent contexts. Every compiler invocation holds the repository's
shared build lock. Final evidence must include fresh source-closure checking,
zero warnings in selected new owners, and a transitive axiom audit of every
owned declaration. Lean and Mathlib pins remain unchanged.

Acceptance is finite dimensional and theorem by theorem. This work does not
by itself construct a full Dirac spinor representation, prove all fine Lie
grading classifications, or certify infinite-dimensional modular theory.
The previously observed root-package path-dependency blockers must be
rechecked and reported separately from scoped native compilation.
