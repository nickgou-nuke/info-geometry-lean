# Dahm binary projective geometry: preservation draft

## Status and source identity

**This is reconstructed source for a user-requested preservation draft. Fresh
Lean elaboration and the final declaration-axiom audit have not run on this
reconstruction. It is not an acceptance certificate.**

The original temporary checkout expired before a successful result from its
corrected verification retry could be recovered. The three new mathematical owners, the small consumer
refactor, this document, and the focused workflow were reconstructed from the
recorded work. They must not be described as a byte-for-byte recovery of a
verified source tree.

The reconstruction starts from upstream main
`c143c264bc18bbf41d692be4e270b5b7f7405702`. The existing
`NativeGradedCochainTwist.lean` was fetched at that exact commit: its upstream
Git blob is `5de11d80ecee0f02aa1947f520afe5f2696931c7`, identical to the blob
at the earlier base `732d97c30f292d61ea332ca9da4d1e1d8f69bd00`. That identity
establishes the consumer's starting source, not the correctness of its new
refactor.

The task concerns the finite binary labels and projective diagrams in Rolf
Dahm, *Discrete and Lie Quantum Symmetries derived from Classical Projective
Geometry*, J. Phys.: Conf. Ser. 3152 (2025), 012008,
[DOI: 10.1088/1742-6596/3152/1/012008](https://doi.org/10.1088/1742-6596/3152/1/012008).
The declarations below retain the sign and order of ordinary matrix
multiplication.

## Source contracts and ownership

The table describes the intended statements in the candidate source. Their
native validation remains pending.

| Owner | Carrier, reuse, and intended API |
| --- | --- |
| `Clifford/BinaryPauli.lean` | Two-bit words in the existing real 2 by 2 matrices `Cl11Matrix.Eplus`, `J1`, and `Eminus`; signed multiplication through the existing `signUnit`; two-factor Kronecker matrices, cocycle and symplectic laws, exact commutation, commutator and ordered triple-product formulas, trace and scalar separation. |
| `Incidence/BinaryProjectiveGeometry.lean` | An arbitrary additive group with a `Module (ZMod 2)` structure; native Mathlib `Projectivization` and `Submodule`; unique nonzero representatives, the span of two distinct nonzero vectors, three-point lines, collinearity, unique line and third point, and the 15-point specialization in dimension four. |
| `Incidence/BinaryPauliGeometry.lean` | The bridge from binary projective points to real projective matrix rays; injectivity, 15 distinct rays excluding the identity ray, and the relation between binary line membership, signed operator products, and line commutation. |
| `Algebra/Zorn/NativeGradedCochainTwist.lean` | Reuse of the new two-bit word in the existing `coreGrade` definition and private multiplication lemma. The three-bit matrix/Zorn constructions and their public statements remain the consumer API. |

The coefficient field of the labels is separate from the coefficient field of
the matrices. The operator carrier is the full noncommutative algebra
`Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ`. It is neither a diagonal
surrogate nor a scalar encoding.

### Convention and causal order

Write a local label as `(a, b)`. The first bit selects
`Z = Cl11Matrix.Eplus`; the second selects `X = Cl11Matrix.J1`. The
four local values are

| Label | Local word |
| --- | --- |
| `(0, 0)` | `1` |
| `(1, 0)` | `Z` |
| `(0, 1)` | `X` |
| `(1, 1)` | `Z * X = Cl11Matrix.Eminus` |

Thus the convention is `Z^a X^b`. No external complex scalar is required to
obtain the real signed multiplication law.

For two-factor labels `v = ((a,b),(c,d))` and
`w = ((a',b'),(c',d'))`, the product exponent is
`b*a' + d*c'` in `ZMod 2`. Its symmetrization controls reversal of the
matrix product. The candidate development follows this order:

1. Identify the actual real local matrices and their signed product.
2. Take their native Kronecker products and retain the product sign.
3. Derive the cocycle, symplectic commutation law, and commutator on that
   noncommutative carrier.
4. Establish the binary projective representative and span APIs independently.
5. Connect binary incidence to operator products and commutation.

For distinct nonzero binary vectors, the line has nonzero representatives
`u`, `v`, and `u + v`. Incidence alone does not say their matrices
commute. The alternating pairing decides that additional condition.
Likewise, the map to real projective operator rays does not assert preservation
of ordinary real-linear collinearity.

## Existing upstream overlap and pending consolidation

[PR #305](https://github.com/nickgou-nuke/info-geometry-lean/pull/305), at
inspected head `8e5dc83403cae85880d023fde467b4cace8dfe5d`, already proposes
substantial related mathematics under different owners:

- `Projective/BinarySymplecticGeometry.lean`: the concrete four-bit
  projective space, spans, unique lines, and the 15/35/15 incidence counts.
- `Quantum/BinaryWeyl.lean`: binary signed words obtained from the existing
  Sylvester clock and shift owner.
- `Quantum/TwoQubitPauliGeometry.lean`: two-factor signed products,
  commutation, Lie brackets, and commuting triples.
- `Quantum/TwoQubitPauliBasis.lean`: a matrix basis and the special-linear
  span.

[PR #308](https://github.com/nickgou-nuke/info-geometry-lean/pull/308) adds a
phase/cocycle follow-up on that branch.

Those words use `X^a Z^b`, over a general commutative coefficient ring where
their stated hypotheses permit. This draft uses the existing Cl11 real
`Z^a X^b` core to serve the native matrix/Zorn consumer. The representations
must not be identified without an explicit convention or transport theorem.
The generic arbitrary-binary-module incidence API, real projective operator
map, and native cochain consumer refactor are the additional integration
surfaces here.

**Consolidation with #305/#308 remains a review task before merge.** This
preservation draft does not claim priority or that all its finite Pauli results
are absent from those proposals. Their reported verification results do not
validate this reconstructed source.

## Current validation record

At the 2026-11-11 reconstruction checkpoint:

| Check | Observed result and limit |
| --- | --- |
| Strict source screener on the four reconstructed owners | Passed: current `tools/infra/opengauss_screener.py --strict` reported zero traps. The local import source tree was incomplete, so this was a bounded source check. |
| Raw source marker and whitespace inspection | No prohibited proof markers or whitespace errors found in the four owners. This is a text inspection, not elaboration or an axiom result. |
| Workflow/helper interface review | The workflow uses the current main implementations of `check_clifford_dirac.py`, `check_reviewed_prs.closure`, `reviewed_audit_source.py`, and `BuildLock`; their source interfaces were inspected. YAML parsing, shell syntax, and all five embedded Python blocks passed static syntax checks. |
| Fresh Lean compilation of this reconstruction | Not run. |
| Fresh owned-declaration axiom audit | Not run. |
| Independent native acceptance | Pending. |
| Current root build and required pre-push gate | No passing result claimed. |
| Hosted workflow | Must be assessed on the published revision; no success is claimed here. |

Before the checkout expired, the earlier scoped attempt compiled baseline
dependencies and reported errors in the new source. Repairs were
prepared and source-reviewed, but the final corrected compilation and axiom
audit were not observed to complete. These historical observations are not
evidence for acceptance of the reconstruction.

Earlier root validation also encountered missing
`external_refs/homotopy-hypothesis-lean4`; the earlier dependency preflight
identified missing Atlas configuration and an uninitialized pinned GIFT
submodule. These are historical environment observations. This document does
not report a new root dependency preflight or root compilation.

## Focused workflow and its actual coverage

`.github/workflows/dahm-binary-projective.yml` selects exactly the four
owners in the source-contract table. It reads the unchanged root manifest and
toolchain, checks out Mathlib at the recorded revision, and retrieves the
native import cache under the maintained shared build lock.

The maintained checker compiles the entire repository source import closure
into isolated output, checks the Mathlib revision and toolchain, verifies
source/helper hashes before completion, and runs the native declaration audit
without `--incremental` or `--skip-audit`. The workflow separately requires
a successful fresh compilation and zero warnings for **each of the four
selected owners**, because the checker's built-in warning condition is
specific to its original CliffordDirac prefix. Existing dependency warnings
are recorded separately and do not become selected-owner warning allowances.

The audit enumerates declarations by their actual defining module, including
private and generated declarations. It collects their transitive axiom
dependencies, rejects unsafe/partial declarations, and permits only
`propext`, `Classical.choice`, and `Quot.sound`. Positive reconciled
declaration counts are required for every selected owner. It does not audit
every unrelated declaration in all imported dependency modules.

The workflow uploads the report, evidence hashes, generated audit source, and
logs. A source screener result, a kernel compilation result, and a semantic
review are different evidence. This scoped workflow supplements the required
repository gates; it does not certify the root default targets or discharge
the pre-push gate.

Once the exact pinned Mathlib checkout and cache are available, the native
checker invocation is:

```sh
python3 tools/quality/check_clifford_dirac.py \
  --mathlib-root /absolute/path/to/pinned/mathlib \
  --output /absolute/path/to/dahm-binary-projective-report \
  --target InfoGeometry.Clifford.BinaryPauli \
  --target InfoGeometry.Incidence.BinaryProjectiveGeometry \
  --target InfoGeometry.Incidence.BinaryPauliGeometry \
  --target InfoGeometry.Algebra.Zorn.NativeGradedCochainTwist
```

The workflow's separate zero-warning assertions are also required for its
acceptance claim. Do not interpret a development run with a skipped audit, or
an old report from another source tree, as this result.

## Boundaries and remaining work

This draft does not supply its own 35-line enumeration, 15/20 line partition,
matrix basis, or identification of the traceless span with a Lie algebra.
Some of those results are instead part of #305. A real 4 by 4 matrix
representation alone does not identify compact `su(4)`, quaternionic
`su*(4)`, a covering group, primitive spinor ideals, or a physical theory.
No such interpretation is an output of these candidate declarations.

Before acceptance, compile the reconstructed source at the current base,
complete the fresh selected-owner audit and independent review, assess the
published CI results and root gates at their actual scope, and resolve owner
consolidation with #305/#308. Keep this proposal in draft while those checks
remain open.
