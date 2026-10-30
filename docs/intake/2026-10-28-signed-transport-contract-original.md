# Signed Peirce transport: intake and proof contract

## Sources and scope

The two current uploads are preserved unmodified:

- Pasted text(20261028-150320).txt: SHA256 c9ea1b3660df958f1492aa1bb7aa48a1a59abb84439546bd958ba1180cfe8c85.
- Pasted text (2)(20261028-150355).txt: SHA256 8cad16c145458a913ffb933dab2ab48a47f590f36daa85ce58657bf6544f3ad9.

The first stream repeats the reciprocal-pair conservation material already
compiled in #260 and adds double weighted commutators. The second explicitly
corrects the missing sandwich term and completes the eight-composition table.
Its isolated line with a repeated backward factor is a prose typo; definitions,
subsequent equations and formal targets consistently use a*x*b +/- b*x*a.

This continuation is based on #260 at da8d0d0aa8ea24c50fc4c9ceb24fd42835d2cbe0.
The parent is not merged. No existing mathematical owner or dependency pin is
modified. The current environment lacks a local Lean executable and cannot
resolve GitHub in the shell; actual verification is delegated to the declared
read-only scoped Actions workflow, not claimed as a local build.

## Owner reuse and search

Read the actual LieJordanEndomorphisms, LieJordanBoundaryComposition,
PeirceBoundaryDynamics, PeirceBoundaryMetric, PeirceBoundaryWitness,
PeirceGradedDifferential, Core.PeirceDecomposition and IdempotentCartan owners.
The existing symmetric crossTransport, sandwichOp, lieOp, jordanOp, corner
projectors and reflection are retained. Seven rows of the octet and the
single weighted commutators are reused rather than reproved under new names.
Code search for skewTransport found no indexed default-branch owner; that is
not an exhaustive repository-wide absence claim. Open-PR source search also
separates the existing DMP, gauge, twistor and trace-localization continuations.
No live code-derived DAG backend is accessible in this environment.

## Native mathematical carriers

General constructions live in Module.End R A for CommRing R and Ring A with
Algebra R A. The coefficient action is central by the algebra interface;
multiplication in A and in its endomorphism ring is not assumed commutative.
Real metric statements use full Matrix n n Real, Frobenius trace and native
Matrix.PosSemidef. All concrete witnesses are dense 4x4 real matrices from the
parent, with its nondiagonal projector. No complex carrier, scalar spectral
surrogate, commuting-generator hypothesis or diagonalization is introduced.

Write C=a*b+b*a, T=a*b-b*a, F(x)=a*x*b+b*x*a and G(x)=a*x*b-b*x*a.

1. SignedBoundaryTransport adds G, the missing reversed mixed-difference row,
   division-free extraction of J_T and G, all eight identities using owners,
   and algebra-homomorphism naturality. If a^2=b^2=0, then
   F^2(x)=(ab)x(ab)+(ba)x(ba), G^2=-F^2, and FG+GF=0.
2. PeirceSignedTransport specializes to a=P*A*(1-P), b=(1-P)*B*P.
   Both maps factor through even input, annihilate odd input and have even
   output. With S=2P-1 and L_S(x)=S*x, prove L_S F=G, L_S G=F,
   F L_S=-G, G L_S=-F, and exact output corner extraction.
   The double commutators are 4*C*C*(a+b) and 4*C*C*(a-b).
3. SignedTransportMetric proves tr G(x)=-tr(T*x), Frobenius self-adjointness
   of F and skew-adjointness of G for b=a^T, Hermitian preservation, Gram
   energy for -G^2, and native ker(G^2)=ker G. A nonzero square-zero a has
   positive input a*a^T whose signed output is -((a^T*a)^T*(a^T*a)),
   which is not positive semidefinite. This disproves a positive-channel
   interpretation of G in this setting.
4. The explicitly displayed indefinite pairing B(x,y)=tr(x^T*S*y) has
   fundamental involution L_S, with L_S^2=Id and B(x,L_S x)>0 for x!=0.
   For the transpose Peirce pair, B(Gx,y)=B(x,Gy). This is a finite real
   indefinite-pairing statement, distinct from the positive Frobenius adjoint;
   it does not assert an infinite-dimensional completion or physical sector.
5. SignedTransportWitness reuses the parent's noncommuting arrows, proves
   signed nonzero and nonsquare-zero behavior, noncommutation of F and G,
   and failure of ambient centrality of C with an independent dense probe.
6. SignedTransportOrder supplies a finite native PartialOrder of sufficient
   prerequisites, keeping cyclic trace, metric, support and nilpotence inputs
   distinct. It is not an extracted full declaration DAG or physical causality.

## Source claims not promoted to theorems

- C is an operator that commutes with the two square-zero generators and
  their quadratic products. It need not commute with every ambient matrix.
- The +/+ reciprocal commutator cycle is not a proof of periodic real-time
  motion. No time evolution or scalar frequency 2C is constructed.
- Opposite operator squares do not specify a nondegenerate spacetime metric,
  spin representation, particle species, mass gap or Schrodinger dynamics.
- With b=a^T the symmetric map is positive (the parent proves this), but
  normalization is additional. The signed map is not a positive channel.
  No matrix-amplification theorem or complete-positivity assertion is made.
- The six formal words in the source table need not be linearly independent
  for actual matrices. They are expansion terms, not an asserted basis.
- simp/abel closing these identities does not establish completeness of a
  Knuth--Bendix decision procedure for all noncommutative ring expressions.

## Verification

Pending the actual scoped run. The unchanged repository source-closure checker
compiles every selected import, and uses public Lean.collectAxioms on all
owned declarations in the five new owners and four explicitly reused owners.
Unsafe/partial declarations and axioms beyond propext, Classical.choice and
Quot.sound are rejected. Source hashes and full logs are uploaded. Existing
repository CI gates are not changed, bypassed or represented as passing.
