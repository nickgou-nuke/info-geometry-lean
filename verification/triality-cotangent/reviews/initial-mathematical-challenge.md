# Independent mathematical challenge: triality and cotangent groupoids

Reviewer: `/root/triality_refuter`, 2026-11-24.
Scope: read-only inspection of the user intake, the relevant canonical owners,
and the pinned Mathlib source. No Lean build was run by this reviewer.

## Required corrections

### 1. Arbitrary fixed cotangent loci need not be symplectic

The intake's general fixed-point conclusion is false, even for an actual
smooth Lie group automorphism with its actual differential.

Take the additive Lie group `G = R²`, its abelian Lie algebra, and
`T(x₁,x₂) = (x₁+x₂,x₂)`. Its adjoint action is trivial and its bracket zero,
so every stated intertwining hypothesis is satisfied. The fixed vectors are
`{(a,0)}`. Under the contragredient action, fixed covectors are `{(0,b)}`.
Their natural pairing vanishes identically. Consequently the fixed locus
inside `T*R²` has tangent space spanned by the first position direction and
the second momentum direction, with identically zero restricted canonical
2-form. It is two-dimensional and degenerate.

The natural restriction map `(V*)^T -> (V^T)*` is zero in this example.
Thus the fixed locus is not canonically `T*(G^T)` as a symplectic space.
Abstract equality of the dimensions is not an adequate repair.

A constructive sufficient hypothesis is finite order over `R`, or more
generally an invariant projection `P : V -> V^T` that is the identity on
fixed vectors and satisfies `P T = P`. For finite order `n > 0`, use
`P = (1/n) sum_{j=0}^{n-1} T^j`. Restriction and extension by `P` give the
actual inverse linear maps between invariant covectors and the dual of the
fixed subspace. This also proves nondegeneracy of the restricted cotangent
pairing. For a finite group, native Mathlib's
`Representation.averageMap` and `Representation.isProj_averageMap` in
`Mathlib/RepresentationTheory/Invariants.lean` provide the averaging core.

### 2. Operation covariance is not the groupoid laws

The submitted `hAd_one` and `hAd_mul` are not used by the theorem because its
conclusion only records covariance of named operations. In particular,
`mulArrow` is defined for all arrow pairs, whereas groupoid composition is
defined for pairs with `source x = target y`.

The conventions themselves are consistent. For
`coadj(k)(alpha) = alpha o Ad(k^-1)`, coadjoint action is a left action:
`coadj(kl) = coadj(k) o coadj(l)`. Source is `alpha`, target is
`coadj(k)(alpha)`, and `(k,alpha)*(l,beta) = (kl,beta)` requires
`alpha = coadj(l)(beta)`. A native `Ad : G ->* (V ≃ₗ[R] V)` and
`CategoryTheory.ActionCategory` can encode the action laws and the typed
composition, rather than retaining unused hypotheses.

Fixed-arrow closure is algebraically valid without finite-order assumptions,
but should include the fixed source and target objects explicitly. The intake
docstring advertises those clauses although its final conjunction only states
unit, inverse, and multiplication closure.

### 3. The scalar formula needs a Lie-algebraic and geometric boundary

The formula

`Omega_alpha((X,beta),(Y,gamma)) = gamma(X) - beta(Y) + alpha([X,Y])`

has the correct signs for the canonical form `-d<alpha,theta_L>` in left
trivialization. With a raw `bracket : V -> V -> V`, however, it is not
automatically bilinear or alternating. Native `LieRing`/`LieAlgebra` instances
can supply those laws. Its nondegeneracy follows algebraically from the full
dual pairing: first test vertical vectors, then horizontal vectors.

Preservation of this algebraic form by a bracket-preserving linear
equivalence is valid. It does not construct the tangent/cotangent bundle of
a Lie group, prove smoothness, identify `dTau` with the actual derivative of
`tau`, prove exterior closedness, or prove the multiplicativity equation on
the manifold of composable arrows. Each of those is a separate implication.

## Matrix and existing-owner findings

The submitted 4x4 identities are mathematically consistent: the Hadamard
reflection and first-axis reflection generate an order-three cycle, and
their common fixed plane is `v0 = 0`, `v1+v2+v3 = 0`. The natural coordinate
map `(a,b) -> (0,a,b,-a-b)` gives the advertised basis. The displayed vector
and half-integral weight orbit is correct.

The theorem type omits several facts advertised in its docstring: cycle
nonidentity, square nonidentity, an actual dimension/basis result, and a
faithful representation of `S3`. Presentation relations alone should not be
reported as a constructed group isomorphism or a faithful action.

Existing owner
`lean/InfoGeometry/Lie/KreinCl44SplitG2DerivationPosetSynthesis.lean` already
defines `trialitySwapVS`, `trialitySwapSpin = diag(1,1,1,-1)`,
`trialityCycle3`, `s3FixedCartanSubmodule`, `s3FixedCartanEquiv`,
`cartan_s3_triality_presentation`, and
`finrank_s3FixedCartanSubmodule`. The signed permutation
`P(v)=(-v3,v1,v2,-v0)` transports the old reflection to the requested one,
commutes with the Hadamard matrix, and transports the old fixed plane
`v3=0, v0=v1+v2` to the requested plane. The root and G2 developments later
in that owner are separate, more extensive constructions.

The existing concrete Cartan directions are `cl44Bivector i (i+4)` for
`i=0,1,2,3`, a split boost Cartan. The intake instead names rotations in the
planes `(1,e3)`, `(e1,e2)`, `(ell,ell e3)`, `(ell e1,ell e2)`. Under the usual
split-octonion norm, each of those planes has equal norm signs, so these are
compact rotations. This latter identification is conditional on that exact
definition of `T_V`, which the intake does not provide. Coordinate conjugacy
of two 4x4 actions does not identify these different real Cartan embeddings
or their Killing forms. Safely report Euclidean coordinate orthogonality
unless a concrete Killing normalization is separately proved.

The two parts of the intake also lack an instantiated connection: no actual
`Spin(4,4)` group automorphism, differential, adjoint action, and Cartan
restriction are constructed together. The existing
`CanonicalZornOuterTrialityGroup.cartanTrialityOuterEquiv` is an actual
related-triples group automorphism over complex scalars; it should not be
silently treated as the requested real differential realization.

## Primary references consulted

- A. Alekseev and E. Meinrenken, *On the coadjoint Virasoro action*,
  https://arxiv.org/pdf/2211.06216, Appendix A.2, Example A.5 and equations
  (78), (81). This gives exactly the chosen source/target convention and
  `-d<mu,theta_L>` and defines multiplicativity separately.
- E. Meinrenken, *Symplectic Geometry* (Fall 2024),
  https://www.math.toronto.edu/mein/teaching/LectureNotes/symplectic.pdf,
  sections 3.4 and 8.4; Example 4.16 discusses involutions and their fixed
  loci. These support the geometric interpretation but are not Lean proof
  evidence.

## Recommended acceptance boundary

Accept a proved algebraic coadjoint action groupoid and its automorphism,
fixed-arrow closure, a native bilinear cotangent-form invariance theorem,
finite-order fixed-dual/restricted-form construction, and the actual 4D
matrix/action/plane transport. Do not advertise an arbitrary fixed
symplectic subgroupoid, smooth Weinstein integration, actual derivative
identification, a concrete Killing isometry, or full real Spin/G2
identification unless the corresponding new constructions are present.
