# Dahm's line-coordinate action: theorem contract

## Source and intended result

Rolf Dahm, *Remarks on Common Representation Theory of Gauge Theories*,
Journal of Physics: Conference Series **2912** (2024), 012036,
DOI: <https://doi.org/10.1088/1742-6596/2912/1/012036>.
The supplied PDF has a cover page: article pages 2–3 are PDF pages 3–4.
The mathematical intake is section 2, equations (2)–(7), and the real
coordinate change (8). The source PDF is not redistributed in this change.

Original reviewed base: `732d97c30f292d61ea332ca9da4d1e1d8f69bd00`.
Publication base: `c143c264bc18bbf41d692be4e270b5b7f7405702`.

The target is the exterior-square representation of unrestricted four by four
matrices, its coordinate formula, and its relative quadratic invariant on
**every** bivector. Matrix products retain their order. The commutative
coefficient ring needed by ordinary minors and determinants is not a
commutativity assumption on the matrix algebra.

## Owner search and reuse

The original source search covered `lean/` and `src/`, related names, imports,
definitions, consumers, and the pinned Mathlib exterior-power API. A bounded
`context_preflight.py` packet also covered entrypoints, graph tooling, and
external references; this does not certify a live declaration database.

| Existing owner | Reused content |
|---|---|
| `Projective/KleinQuadric.lean` | `Plucker6`, `kleinQ`, `polar`, coordinate addition, `Vec4.wedge` |
| `Projective/ExteriorPowerPluckerBridge.lean` | Literal exterior-power/coordinate linear equivalence, wedge readout, decomposability |
| `Canonical/KleinBivectorLinear.lean` | Native module structure and canonical bivector coordinate equivalence |
| Mathlib `ExteriorPower/Basic.lean` | `exteriorPower.map`, generator naturality, identity and ordered composition |
| Mathlib matrix API | Ordinary matrix product, `mulVec`, `det`, native linear-map/matrix equivalences |

No new six-field carrier, projective quotient, Clifford algebra, or categorical
limit is introduced. Existing projective incidence and decomposability results
are not re-proved as a substitute for the full-space transformation theorem.

## Exact convention and obligations

Coordinates are ordered `(01,02,03,12,13,23)` throughout:

```text
q(p) = p01*p23 - p02*p13 + p03*p12.
```

Dahm uses `p31 = -p13`. Each minor sum ranges over the six independent
pairs, so there is no extra factor of two.

The polar form is the unnormalized symmetric expression
`B(P,Q) = q(P+Q) - q(P) - q(Q)`. In Dahm's oriented coordinates it is

```text
B(P,Q) = P01*Q23 + P02*Q31 + P03*Q12
       + P23*Q01 + P31*Q02 + P12*Q03.
```

These six terms are the coefficients explicitly expanded in equation (5).
Equation (6) abbreviates the pairing with an ellipsis, and equation (7)
uses that abbreviated notation. The identification uses the full expansion,
with no factor of one half.

For a commutative ring `R`, define the six by six matrix `C₂(A)` by

```text
C₂(A)[(i,j),(a,b)] = A[i,a]*A[j,b] - A[i,b]*A[j,a].
```

The dependency order to establish is:

1. Existing coordinate carriers and the six independent pairs.
2. The minor action, identity, ordered multiplication, and wedge naturality.
3. `q(C₂(A)p) = det(A)*q(p)` for arbitrary `p`.
4. Polar covariance, null-locus preservation, and equal complementary-pair
   coefficients as consequences of the full-space identity.
5. Intertwining with Mathlib's literal `exteriorPower.map 2` over `ℝ`.
6. The boost specialization, the real split-coordinate identity, and explicit
   noncommuting volume-preserving shears.

Every edge in this list is to be backed by an actual map or theorem. No
physical or group-classification conclusion is part of the formal contract.

## Source corrections and boundaries

The multiplier of the displayed boost is `γ²*(1-β²)`, rather than
`γ²*(β²-1)`. Under the explicit normalization `γ²*(1-β²)=1`, it preserves
the Klein polynomial. At `β=0, γ=1`, the displayed point transformation is
the identity, providing an immediate sign check.

For the minors of one four by four matrix, the three complete complementary
coefficients in equation (5), written as pairings in equation (7), all equal
`det(A)`. They cannot be independent unequal coefficients of a single induced
exterior-square transformation.

The real coordinates in equation (8) give a split quadratic polynomial with
three positive and three negative square terms. A compact real form requires
additional data. Polar incidence is not an operator commutator.

The present target does not derive gauge groups, Spin(8) triality, a field
theory, or a classification of all quadric automorphisms. Singular matrices
act on the affine bivector space; they do not define an action on every
projective point. No projective automorphism is claimed without invertibility.

## Implementation owners

All paths below are relative to `lean/InfoGeometry/Projective/`.

| Module | Principal declarations and scope |
|---|---|
| `PluckerMatrixAction.lean` | `secondCompoundHom`, `transform_wedge`, `kleinQ_transform`, `polar_transform`; arbitrary matrices and bivectors over a commutative ring |
| `DahmLineGeometry.lean` | Three complementary-pair identities, boost determinant and normalized invariance, real split-coordinate polynomial, noncommuting point and exterior shears, and a nondecomposable bivector with Klein value one |
| `ExteriorKleinMatrixAction.lean` | `pluckerAction`, `secondCompound_pointMatrix`, `exteriorPlucker_map`, `exteriorKleinForm_map`; the existing native real exterior square and the actual endomorphism determinant |

The generic coordinate owner imports the existing finite-matrix
noncommutativity witnesses. The examples additionally prove noncommutation
for their specific four- and six-dimensional operators. The native action
uses `exteriorPower.map 2` and an existing linear equivalence; the minor
formula is proved equal to its matrix, rather than introduced as a substitute
for the exterior-power construction.

## Validation and recovery record

This is a draft for review. It does not claim completed native QA or readiness
to merge.

On 2026-11-10, against the original reviewed base:

- `PluckerMatrixAction` and `ExteriorKleinMatrixAction` were freshly compiled
  successfully by the pinned Lean/Lake toolchain. Their selected-owner traces
  had no warnings or errors. Existing dependency warnings were replayed.
- `DahmLineGeometry` failed on a column readout and a closed `Fin.succAbove`
  computation. The two proof bodies were repaired without changing any
  theorem statement or hypothesis. Independent mathematical review and strict
  static screening passed on the repaired candidate; the actual nonempty
  staged proof/header gate also passed independently.
- The subsequent build and independent native QA were queued. No completed
  successful receipt or owned-declaration axiom audit was observed. The 63
  explicit declaration names in the checker are an inventory, not a completed
  audit count.

The transient checkout and its runtime artifacts were unavailable on
2026-11-11. The three Lean files and all four scoped verification files were
restored from retained source text. Their SHA-256 values match the recorded
candidate exactly. The unpublished local commit is not represented as an
existing upstream commit; this draft creates a new commit on the current base.
Historical compilation observations do not certify the new base.

| Restored file | SHA-256 |
|---|---|
| `PluckerMatrixAction.lean` | `2684398d2a538fe81cbbb54e93193fff12ec813b1d53691d95063c1eb6470761` |
| `DahmLineGeometry.lean` | `394ba33a9767493f1de8f50543810ed70c98097186b19ee3e80636bb2362289b` |
| `ExteriorKleinMatrixAction.lean` | `cb47f69725b4b12e5b2c45101566866143382b16957524d3c06a0e814fc87093` |
| `verification/dahm-exterior-square/check.py` | `64113ac373701e2c924abacb17cd6237671922d9cfc69da1f4acc0a3c457cfaa` |

The earlier root locked Lake build stopped before elaboration because
`external_refs/homotopy-hypothesis-lean4` was absent. Path preflight also found
an absent `Atlas` package and an uninitialized `GIFT` gitlink. GIFT's exact
pinned commit could not be fetched from its configured remote, including
after fetching the full advertised history. The inspected metadata did not
provide reproducible revisions for the other two missing local packages.

The root Lean and Mathlib pins are not changed by this PR. Once the required
pinned native dependencies are available, the scoped check is:

```bash
python3 verification/dahm-exterior-square/check.py --wait-for-build-lock
```

The checker runs a native scoped build and a fresh owned-declaration axiom
audit. It does not provision or seed dependencies, certify a fresh dependency
rebuild, or replace the root publication gate. Full current-base compilation,
the axiom audit, independent native QA, and the required publication checks
remain required before merge.
