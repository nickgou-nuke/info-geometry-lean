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
- `Krein/FiniteDiracGramSquare`: rectangular `fromBlocks` Dirac/Gram
  identities; the present carrier instead uses arbitrary ambient idempotents
  and independent opposite corners, without choosing a block basis.
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

The following principal proof-use edges generate the partial order; the full
proof terms also depend on the imported support, ring, trace and order lemmas.
Namespaces are abbreviated to the two new modules.

| Prerequisite declaration(s) | Consumer declaration(s) |
| --- | --- |
| Existing same-corner zero-product lemmas | `sum_sq` |
| `sum_mem_odd`, existing odd-parity law | `conjugate_sum` |
| `sum_sq`, `sum_mem_odd`, existing `odd_mul_odd` | `anticommutator_mem_even` |
| `commutator_eq_reflection_mul`, existing `reflection_sq` | `anticommutator_eq_reflection_mul` |
| Both reflection-exchange lemmas | `anticommutator_eq_zero_iff_commutator` |
| `component11_anticommutator`, `component00_anticommutator` | `anticommutator_eq_zero_iff_products` |
| The respective even-membership lemma, existing reflection laws | `conjugate_anticommutator`, `conjugate_commutator` |
| `sum_sq`, native cyclic trace | `trace_sum_sq` |
| `anticommutator_eq_reflection_mul`, native cyclic trace | `trace_reflection_mul_commutator` |
| Respective corner readouts, native cyclic trace | `trace_anticommutator_corners`, `trace_commutator_corners_add` |
| `component01_conjTranspose` | `adjoint_sum_isHermitian`, `adjoint_anticommutator_posSemidef` |
| `sum_sq`, `adjoint_anticommutator_posSemidef` | `adjoint_sum_sq_posSemidef` |
| `adjoint_anticommutator_posSemidef` | `trace_adjoint_anticommutator_nonneg` |
| `anticommutator_eq_zero_iff_products`, `component01_conjTranspose`, native faithful Gram trace | `adjoint_anticommutator_eq_zero_iff` |
| `anticommutator_eq_zero_iff_commutator`, `adjoint_anticommutator_eq_zero_iff` | `adjoint_commutator_ne_zero_iff` |
| `sum_sq`, `adjoint_anticommutator_eq_zero_iff` | `adjoint_sum_sq_eq_zero_iff` |

The base support/reflection identities use noncommutative ring normalization
with the actual idempotence equation; they assume no pairwise commutativity.
In the ordered branch `open scoped ComplexOrder` means
`z ≤ w ↔ z.re ≤ w.re ∧ z.im = w.im`. Thus the trace nonnegativity theorem
also certifies that this trace is real.

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

`[kernel_verified]` All 29 new declarations passed the focused check, with
zero Lean warnings or errors and `semantic_vacuity: 0`.

- Source commit: `59b846e63ea45545e2664eaacd5dd75c1d09fc70`.
- Checked PR merge: `f1ca9c006209d9159e23237460dbc96997027f10`.
- [Successful run 40675941324](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/40675941324),
  job `122774239354`.
- Command: `bash scripts/quality/check-opposite-peirce.sh`. This compiles the
  seven-module import closure serially in an isolated directory using the
  root-pinned mathlib revision; it does not claim a full root Lake build.
- Lean `4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`;
  Lake `5.0.0-src+5045d00`;
  mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Exact-set axiom inspection: 29 declaration reports, each with precisely
  `[propext, Classical.choice, Quot.sound]`. No extra axioms or placeholders.
- Static placeholder scan, semantic-vacuity gate and staged proof-proxy gate
  passed. No scalar/diagonal specialization or commuting assumption was added.

Verified SHA256 fingerprints:

| File | SHA256 |
| --- | --- |
| `OppositePeirceCoupling.lean` | `e7ff68b70a87806d409d7fafb219af4af738e9f809928bc72daea8ffdac682ef` |
| `OppositePeirceTrace.lean` | `ee193baded42a3643b24b483f40bf62cdb26df36e41c0d86b688228efb00de98` |
| `OppositePeirceAudit.lean` | `91368a4303278c8973257040d2c279d7c467be07b40129af354da1a641eeeea6` |

Local Lean launch failed with `error: failed to locate application`, so no
local kernel success is claimed. The first remote run diagnosed a name
collision in four simplifier entries (`commutator` resolved to a group-theory
constant). Fully qualifying the matrix definition repaired those steps;
explicitly importing `RCLike.Basic` supplies complex ordered-star instances.
The statements and hypotheses were unchanged.

Independent semantic audit found the finite algebra and conditional positivity
sound. Separate acceptance review independently retrieved the successful logs,
matched all 29 theorem names and all three hashes, and returned
`ACCEPTED_WITH_LIMITED_SCOPE`. The final verification-record update changes
only this document; the verified proof files, script and workflow are unchanged.

### Repository-wide checks outside this closure

Full repository CI is not green. On the first source head, style run
`40675621774`, job `122773151777`, stopped before Lean lint on the existing
case collision `Physics/PellisFineStructure.lean` versus
`Physics/PellisfineStructure.lean`. Sorry Gate run `40675621682`, job
`122773150953`, failed before compilation because `lake` was missing
(`Errno 2`, exit 127). These are separate from the successful focused kernel
check; this PR does not repair unrelated repository infrastructure.

## Intake fingerprints

- `Pasted text(20261028-104306).txt`: SHA256 `fc76f3c1295af250a9aac658b305d0860fc9726fa581ccdd30c735e808bea659`.
- `Pasted text (2)(20261028-104417).txt`: SHA256 `5a4f6b652586a71d405b6543bb7e24152d2a284705f5a3a7a35481f454dd4e7f`.
