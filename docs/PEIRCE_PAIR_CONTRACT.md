# Opposite Peirce corners: theorem contract

## Intake and source boundary

This extension continues PR #251 from commit
`54896c873c04459e18c702decc20b135d9dcf4d5`. The original attachments remain
unchanged. Their SHA256 digests bind this contract to the complete intake:

| Attachment | SHA256 |
| --- | --- |
| `Pasted text(20261028-104318).txt` | `fc76f3c1295af250a9aac658b305d0860fc9726fa581ccdd30c735e808bea659` |
| `Pasted text (2)(20261028-104338).txt` | `5a4f6b652586a71d405b6543bb7e24152d2a284705f5a3a7a35481f454dd4e7f` |

The proposed source uses the full algebra `Matrix n n ℂ`, where `n` is any
finite decidable type. Multiplication remains ordered. No diagonal carrier,
commuting-input hypothesis, scalar replacement, or physical interpretation is
introduced. The checked finite statements are the deliverable.

## Native owners and conventions

- `Core.PeirceDecomposition.component10 p A = p * A * (1 - p)` and
  `component01 p B = (1 - p) * B * p` own the two directed corners.
- `Core.PeirceDecomposition` owns their complete routing table, including
  same-corner zero multiplication and opposite-corner products.
- `Core.IdempotentCartan.reflection p = 2 • p - 1` owns the reflection, its
  square identity, and the ring equivalence `reflectionConj`.
- `OperatorAlgebra.PeirceChiralGeometry` owns corner trace vanishing, adjoint
  exchange, and the same-input odd-square and Gram identities.
- Mathlib owns `IsIdempotentElem`, `IsStarProjection`, `IsSelfAdjoint`,
  `Commute`, the associative Lie bracket, matrix adjoint, trace, `PosSemidef`,
  and `PosDef`. The convention is `⁅U,V⁆ = U * V - V * U`.

Below, `U`, `V`, `S`, `E`, `Q`, and `L` are notation in this contract, not
new Lean wrappers: `U = component10 p A`, `V = component01 p B`,
`S = reflection p`, `E = U + V`, `Q = U*V + V*U`, and `L = ⁅U,V⁆`.

## Mathematical atoms and hypotheses

With only `IsIdempotentElem p`:

1. The directed corners are square-zero (reuse the existing owner).
2. `E*E = Q`; `S*E*S = -E`; the sum has zero same-sector compressions.
3. `Q` and `L` commute with `p` and with `S`; reflection conjugation fixes
   each. The ambient even algebra is generally noncommutative.
4. `S*Q = L` and `S*L = Q`. Consequently `Q = 0 ↔ L = 0`, and
   `Q ≠ 0 ↔ ¬ Commute U V`.
5. `component11 p Q = U*V`, `component00 p Q = V*U`,
   `component11 p L = U*V`, `component00 p L = -(V*U)`.
6. Cyclic trace yields equal traces of the two compressions of `Q`, opposite
   traces of the compressions of `L`, and
   `trace Q = trace (S*L) = 2 * trace (U*V)`.
7. `trace (S*Q) = 0`. The factor two is relative to `trace (U*V)`,
   not relative to `trace Q`.

With the additional adjoint pairing `IsStarProjection p` and `B = star A`:

8. `V = star U`, so `E` and `Q` are self-adjoint, and
   `Q = U * star U + star U * U` lies in Mathlib's positive-semidefinite cone.
9. Both compressions are positive-semidefinite Gram matrices.
10. `Q = 0 ↔ U = 0`, and likewise `trace Q = 0 ↔ U = 0`.
    The faithful conclusion concerns the directed corner, not arbitrary
    commutation of `p` and a non-Hermitian input `A`.
11. The exact vector kernel is `Q *ᵥ v = 0 ↔ U *ᵥ v = 0 ∧ star U *ᵥ v = 0`.
    Positive definiteness is equivalent to injectivity of `U + star U` as
    a vector operator. This states precisely the stronger condition required.

## Nonvacuity and rejected strengthening

Reuse the existing nondiagonal noncommuting `OperatorExtensionExamples.P`
and `.Q`. Their mixed square is nonzero and nonscalar, with a nonzero kernel.
The opposite-corner Lie bracket is also nonzero by the new twist theorem.
Choosing the reverse input with a minus sign gives a negative nonzero mixed
square and refutes unconditional positivity while retaining noncommutation.

No automatic nonzero conclusion follows for arbitrary inputs. Semidefinite
positivity does not assert positive definiteness or a uniform lower bound.
No Yang--Mills mass gap, spin representation, spacetime topology, spontaneous
symmetry breaking, or gravitational statement follows from these finite
identities. The identity `E*(E*E) = (E*E)*E` is ordinary associativity and
does not warrant a new theorem claiming Dirac or Drazin content.

## Dependency and acceptance contract

The conceptual order is corner routing and reflection involution; then pair
square, parity, twist and compression laws; then trace readouts; then
adjoint Gram positivity and faithful vanishing; then concrete instances.
The deliverable poset must be computed from constants in the actual checked
declaration types and values. Inverse algebraic equalities must not be turned
into directed dependency cycles.

Acceptance requires a fresh complete selected import-closure compilation,
an audit of every owned declaration, only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms, the staged proof-proxy and semantic gates,
and independent semantic and verification review. Existing imported sources
and dependency pins are preserved. A final verification record will bind
the exact source, tool versions, diagnostics, and checked dependency graph.

## Checked theorem surface

The three additions contain **49 named theorems** and no new source-level
`def`, `abbrev`, carrier, bracket, reflection, or Peirce-operation definition.
The example file's local `Mat` notation generates three safe, axiom-free
syntax definitions; these are included in the complete declaration audit.

| Module under `InfoGeometry.OperatorAlgebra` | Named theorems | Main results |
| --- | ---: | --- |
| `PeircePairGeometry` | 28 | Independent-corner square; reflection parity and twist; exact noncommutation criterion; compression, kernel splitting, and trace identities |
| `PeircePairPositivity` | 14 | Adjoint Gram identity; positivity of both compressions and their sum; faithful vanishing; exact vector kernel; positive definiteness iff injectivity |
| `PeircePairExamples` | 7 | Noncommuting directed constituents; nonscalar bracket; nonzero joint-kernel vector; noncommuting negative-square counterexample to unconditional positivity |

The zero same-sector compression assertion in atom 2 is a consequence of
`oddPart_pair` and the existing Peirce projection/routing laws, rather than a
separately named new export. Square-zero, individual trace-zero, reflection
involution, and adjoint exchange likewise retain their existing owners.

## Source-bound local verification

The complete local snapshot contains **39 repository modules**, including all
**14 audited operator owners**. All **36 inherited source files** are unchanged
from `54896c873c04459e18c702decc20b135d9dcf4d5`: 11 old owners and 25 other
repository dependencies. Mathlib and all eight transitive package revisions
remain pinned. The compiler is Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`.

The local complete audit passed for **343 declarations**: **314 theorem-kind**
and **29 definitions**, including generated declarations. The additions account
for 66 audited declarations: 63 theorem-kind declarations and the three syntax
definitions noted above. All 277 previous audit records are unchanged.

Only `propext`, `Classical.choice`, and `Quot.sound` occur as transitive axioms.
There are no owned axioms, unsafe or partial declarations, proof holes, or
native-decision shortcuts in the new mathematical source. The staged
proof-proxy, semantic-vacuity, placeholder, and whitespace checks pass. The
semantic scan has zero findings. All three new module compiler logs are empty.
The 41 inherited compiler warnings occur in seven unchanged source files and
are recorded separately in the verification JSON.

Local iteration uses checked source hashes and `--incremental`; the complete
declaration audit itself always executes again. **Fresh release acceptance is
the separate nonincremental GitHub workflow for the published commit.** Its
exact head, tested merge, run, artifact, and acceptance result are recorded in
the [PR #251 description](https://github.com/nickgou-nuke/info-geometry-lean/pull/251).
The local record deliberately does not promote itself to that CI attestation.

## Actual dependency poset

[`PEIRCE_PAIR_DEPENDENCIES.json`](PEIRCE_PAIR_DEPENDENCIES.json) is the complete
unmodified output of the checked declaration-graph exporter. It contains all
declaration records and all type/proof/definition constant dependencies,
restricted to the 14 stated owner modules for its order relation.

- **343 nodes**;
- **644 direct owned dependency edges**;
- **354 Hasse edges**;
- **7 topological layers**, with sizes `142, 49, 73, 40, 21, 15, 3`.

The relation is `a ≤ b` when `a = b` or `b` transitively depends on `a`.
Edges point from a dependency to its dependent. Both checked declaration types
and values contribute constants. This is the dependency order of these chosen
proofs, not a claim of unique mathematical necessity. All 25 non-owner source
dependencies import no audited owner, so no path through an external repository
module returns to an omitted owner edge.

The following are actual cover edges in that output, not conceptual arrows:

| Dependency | Dependent |
| --- | --- |
| `reflection_mul_pair_jordan` | `reflection_mul_pair_lie` |
| `reflection_mul_pair_lie` | `pair_jordan_eq_zero_iff_lie` |
| `pair_jordan_eq_zero_iff_lie` | `pair_jordan_ne_zero_iff_not_commute` |
| `pair_jordan_ne_zero_iff_not_commute` | `opposite_corners_not_commute` |
| `pair_jordan_eq_gram_sum` | `adjoint_pair_posSemidef` |
| `pair_sum_mulVec_eq_zero_iff` | `adjoint_pair_mulVec_eq_zero_iff` |
| `adjoint_pair_mulVec_eq_zero_iff` | `positive_pair_joint_kernel` |
| `pair_sum_isSelfAdjoint` | `adjoint_pair_posDef_iff_injective` |

The full source manifest, package pins, gate outputs, warning disposition,
audit and graph digests, and independent agent-review records are in
[`PEIRCE_PAIR_VERIFICATION.json`](PEIRCE_PAIR_VERIFICATION.json). Mathematical
semantic review and verification acceptance are separate roles; no authoring
agent accepts its own result.
