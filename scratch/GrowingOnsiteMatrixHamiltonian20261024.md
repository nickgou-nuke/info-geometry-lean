# Growing onsite finite-matrix Hamiltonians

Candidate: GrowingOnsiteMatrixHamiltonian20261024.lean; uncompiled source.

Uses native MatrixStage n, concreteStep n, stageIndexEquiv n, and existing
KleinBottleSewingExact.tilt2/switch2. No new matrix or Hilbert carrier.

The new tailEmbedding is the actual star-algebra map
B -> reindex(stageIndexEquiv n) (I_(2^n) kronecker B).
Its derived tailZ/tailX commute with every embedded old observable; proof uses
native mul_kronecker_mul and reindex algebra-map laws, not an assumed commutant.

For arbitrary real weights w:
H(0)=0, H(n+1)=concreteStep n H(n)+w(n)•tailZ(n).
The candidate derives:
- Hermiticity of all H(n), using native Hermiticity of the existing tilt matrix.
- [H(n+1),concreteStep n A]=concreteStep n [H(n),A].
- [H(n+1),tailX(n)]=w(n)•tailEmbedding n [tilt2,switch2].
- This last commutator is nonzero if w(n) is nonzero. The proof tests the
  actual entry with tensor indices (0,0),(0,1), whose real value is 2*w(n).

Thus nonzero weights yield genuinely new tail action at each such stage.
There is no assertion H(n+1) != H(n) between different carriers, no restriction
to a scalar stage-zero Hamiltonian propagated unchanged, and no arbitrary
nearest-neighbor interaction compatibility claim.

Search covered native matrix tower/tensor owners, tail/onsite/commutator
searches in Canonical and OperatorAlgebra, Cl11BipartiteOrderOneCondition, and
Mathlib Kronecker/reindex APIs. The latter already provide the product proof;
the tail map and this weighted recursion were not found in those sources.
Existing FiniteMatrixGibbsParity supplies tiltHamiltonian_isHermitian.

Scope ends at finite algebra. No summability assumption, uniform norm estimate,
GNS completion, or compatible completed operator family is asserted here.
Those belong to subsequent consumers using the accepted tracial GNS action.

No builds/tests/live-owner edits. Candidate and contract staged; AA/QA required.
