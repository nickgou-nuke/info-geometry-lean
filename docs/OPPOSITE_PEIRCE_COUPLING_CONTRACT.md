# Opposite Peirce coupling: theorem contract

## Intake and scope

The two user uploads dated 2026-10-28 (10:43:06 and 10:44:17) propose
identities for `X = P A (1-P)` and `Y = (1-P) B P`, interspersed with physical
interpretations. The uploads remain unchanged. Their mathematical content is
compiled here on the full matrix algebra, with no commuting, diagonal, or
scalar restriction on the operators.

The algebraic carrier is `Matrix n n R`, for finite `n` and `Ring R`.
`P` is a native `IsIdempotentElem`; `A` and `B` are arbitrary matrices.
Trace cyclicity additionally needs `CommRing R`, but matrix multiplication
remains noncommutative. The positivity branch uses complex matrices, Hermitian
`P`, and the explicit adjoint choice `B = Aᴴ`.

## Owner search and exact operations

- `Core/PeirceDecomposition`: `component10 P A = P*A*(1-P)`,
  `component01 P B = (1-P)*B*P`, `component11`, `component00`,
  opposite-corner product routing and same-corner zero products.
- `Core/PeirceGrading`: `reflection P = 2*P-1`, `reflection_sq`,
  `mem_odd_iff`, `odd_mul_odd`, `even_commutes_reflection`,
  `odd_anticommutes_reflection`.
- `NCG/NonCommutativeFredholmIndex`: existing matrix `commutator`,
  `anticommutator`, `trace_commutator_zero`.
- `Core/PeirceMatrixTracePairing`: cyclic opposite-corner trace pairing
  and its separation theorem; this concerns a pairing, not the new coupled sum.
- `Core/IdempotentCartan` and `Core/FinitePeirceMatrix`: existing parity
  and finite-block assembly; no duplicate grading or block carrier is added.
- `Canonical/OperatorHermitianLieJordanSplit`: a different, normalized
  Jordan product on Dirac matrices; no silent identification with our
  division-free anticommutator.
- Mathlib `Matrix.PosSemidef`, Gram positivity, and
  `trace_mul_conjTranspose_self_eq_zero_iff` supply the ordered branch.

Search included both source names and formulas across Core, NCG, Algebra,
CliffordWeyl, Canonical and their consumers. Context preflight found no
generated declaration DAG/InfoTree index in this checkout. The dependency
order below is source-derived, not a claim of generated graph freshness.

## Proposed theorem surface and dependency order

With `S = reflection P`, `J = XY+YX`, `L = XY-YX`, prove:

1. Corner routing and square-zero owners imply `(X+Y)² = J`.
2. Corner support implies `X+Y` is odd, while `J` and `L` are even.
3. Support and reflection give `L = S*J`; `S²=1` gives `J=S*L`.
4. These identities imply `J=0 ↔ L=0`; corner readouts further give
   `J=0 ↔ XY=0 ∧ YX=0`.
5. Parity gives reflection conjugation by minus on `X+Y` and plus on `J,L`.
6. Corner readouts and cyclic trace give equal traces for the two product
   corners, opposite traces for commutator corners, and `tr J=2 • tr(XY)`.
7. Under the explicit adjoint hypothesis, `Y=Xᴴ`. Mathlib Gram positivity
   gives positive semidefiniteness of `J`, and faithfulness of the Gram trace
   gives `J=0 ↔ X=0`. Thus nonzero `X` forces a nonzero commutator.

The causal order is the reflexive transitive closure of actual proof-use
edges, oriented prerequisite → result. Distinct declarations in these files
are ordered before their consumers, so this relation is acyclic and its
closure is a partial order. This is documentation of proof dependencies;
no physical time order or new Lean poset carrier is asserted.

## Rejected promotions

The input does not establish automatic nonvanishing, strict positivity,
invertibility, a spectral gap, Yang–Mills theory, spin, gravity, photon/electron
identification, a connection, or spontaneous symmetry breaking. Odd parity is
a grading identity. For arbitrary `B`, even positivity is false: the adjoint
choice with the opposite sign yields the negative Gram sum. The identity
`E*(E*E)=(E*E)*E` is associativity, not a Drazin or Dirac equation.
The even part is generally a noncommutative subalgebra, not a Cartan subalgebra.
An equality of two corner traces is not a positivity statement.

## Verification

Pending kernel checking and independent acceptance. Local Lean launch fails
with `error: failed to locate application`; verification uses the repository's
pinned Lean/mathlib versions in an isolated, serial GitHub Actions check.

## Intake fingerprints

- `Pasted text(20261028-104306).txt`: SHA256 `fc76f3c1295af250a9aac658b305d0860fc9726fa581ccdd30c735e808bea659`.
- `Pasted text (2)(20261028-104417).txt`: SHA256 `5a4f6b652586a71d405b6543bb7e24152d2a284705f5a3a7a35481f454dd4e7f`.
