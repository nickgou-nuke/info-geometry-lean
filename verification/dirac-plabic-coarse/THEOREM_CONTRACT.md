# Theorem contract: Dirac incidence, finite edge weights, Schur transport

## Intake and provenance

The intake described White/Black graphs of opposite skew maps, an involution
called CPT, Casimir fixed states, epsilon spinor brackets and Pluecker relations,
and network addition/coarse-graining. It further claimed a complete eight-module
physical unification. The accepted mathematical contract is the real linear and
finite-matrix content below; the broader interpretation requires additional data
and theorems. This reconstruction preserves that contract, not the inaccessible
bytes or certificate of the earlier unpublished snapshot.

## Native carriers and reused owners

| Construction | Existing owner |
| --- | --- |
| Real module times its algebraic dual and neutral form | `Clifford.NeutralPhaseSpaceCore` |
| Neutral orthogonal set and real para-involution | `Canonical.NeutralDualPairSplitting` |
| Native incidence linear map and range submodule | `Twistor.RealTwistorIncidence` |
| Real matrix/dual coordinate identification | Mathlib `dotProductEquiv` |
| Existing real epsilon matrix | `Clifford.Soldering` |
| Ordered minors and Pluecker identity | `Topology.AmplituhedronGeneralTwistorExpansion` |
| Supplied finite graph, signing, edge-sum matrix, block Dirac | `Canonical.FinitePlabicKasteleyn` |
| Positive fine/coarse precision and harmonic extension | `OperatorAlgebra.PositiveCoarseGraining` |
| Native symmetric/antisymmetric matrix decomposition | `OperatorAlgebra.RealMatrixSplit` |

## Exact claims

### 1. Native real incidence

For a real module E and its algebraic dual E*, use the existing carrier E x E*,
neutral form B((u,xi),(v,eta)) = xi(v) + eta(u), and incidence map
W_P(xi) = (P xi,xi). Assume evaluation skewness
xi(P eta) = -eta(P xi) only for the isotropy claims.

- B(W_P xi,W_P eta)=0.
- B(W_P xi,W_(-P) eta)=2 eta(P xi).
- The graph is its own neutral orthogonal complement and is maximally isotropic.
- The real linear mirror J(u,xi)=(-u,xi) is involutive and negates B.
- J exchanges the two graph submodules.
- Without a skewness assumption, J fixes W_P xi iff P xi=0; opposite-graph
  intersection states are exactly (0,xi) with P xi=0.
- Native dual pullback and primal pushforward preserve evaluation skewness and
  transport a specified pullback-kernel covector in one direction.
- With the explicit dot-product dual identification, the native composite
  Q o P o Q.dualMap agrees with rectangular matrix congruence Q P Q^T.

### 2. Real spinors

Reuse epsilon=[[0,1],[-1,0]]. With ordered vectors u,v, the positive-negative
cross pairing is **-2 (u0 v1-u1 v0)**. Reversing the two graph signs while keeping
u,v ordered gives +2 times the same minor. The actual cross pairings satisfy the
three-term Pluecker identity because their common scale occurs quadratically.
Epsilon has zero kernel; its graph has only the zero mirror-fixed state. The
explicit basis-vector example has pairing -2 before mirroring and +2 afterward.

### 3. Supplied finite networks

The graph and its signing are supplied native data. Edge weights are actual
incidence cross pairings, and their consumers are the native edge-sum matrix
and block Dirac operator. Parallel addition of operators adds weights and
edge-sum matrices. The mirror negates weights and the Dirac operator, preserves
the Dirac square, and multiplies an edge-product by (-1)^card(Edge). Even edge
count is an explicit sufficient condition for edge-product invariance.

### 4. Positive Schur transport

Let A and R be positive definite real square matrices, Q rectangular, and P a
fine skew matrix where stated. Reuse the existing definitions

```text
H = A + Q^T R Q
C = R - R Q H^(-1) Q^T R
F = H^(-1) Q^T R.
```

The exact covariance/skew bridge is

```text
R^(-1) + Q (A^(-1) + P) Q^T = C^(-1) + Q P Q^T.
```

Its native self-adjoint and skew-adjoint parts are C^(-1) and Q P Q^T when
P^T=-P. The ordered normality defect of C+Omega is 2(C Omega-Omega C).
The harmonic transport is F^T P F = R Q H^(-1) P H^(-1) Q^T R.
No commuting hypothesis is inserted. Pure harmonic skew congruence needs no
positivity assumption. Three final declarations feed the actual skew-adjoint
part of the full Schur response into the native incidence graph, establishing
orthogonal equality, pulled-back cross pairing, and the kernel-fixed implication.

## Dependency order

Neutral carrier and incidence maps support skew incidence. The coordinate
identification supports the spinor and rectangular matrix bridges. Existing
finite-graph consumers receive actual pairing weights. Existing positive Schur
transport identifies the symmetric part; skew congruence identifies the other
part; only then is the full coarse response fed back into native incidence.

## Explicit boundaries

No theorem here constructs a Courant/Dorfman bracket or proves integrability,
a Drinfeld Lie bialgebra, physical charge/parity/time-reversal operators,
global Casimir entropy functions, a planar embedding, existence of a Kasteleyn
signing, representation-labeled Penrose spin networks or invariant intertwiners,
arbitrary internal-vertex gluing/elimination, or a continuum RG limit. Operator
addition is parallel addition. Rectangular kernel transport is one-way.

The user's eight-module architectural description remains a separate claim;
this package certifies only its actual declarations and imported dependencies
when the recorded compiler/axiom checks pass.
