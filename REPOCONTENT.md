# Operator-algebra research map and current owners

This page preserves the seven-stage mathematical outline from an earlier
conversational research synthesis and maps it to existing Lean owners. It is a
reading guide for one operator-algebra corridor, not an inventory of the whole
repository or a claim that the original standalone synthesis was compiled.

Selected owner declarations and imports below were source-reviewed on
2026-11-03 at commit `214f7bcf733eaf4720913bc2c082936f2480d3fc`. No new builds
were run for this review. The previous large inline Lean proposal is preserved
in the [historical version](https://github.com/nickgou-nuke/info-geometry-lean/blob/214f7bcf733eaf4720913bc2c082936f2480d3fc/REPOCONTENT.md).
It should be treated as research input, not a second authoritative
implementation or evidence of complete proof coverage.

Use [README.md](README.md) and [docs/README.md](docs/README.md) for repository
navigation, and the [deep-search protocol](docs/REPO_DEEP_SEARCH_PROTOCOL.md)
before declaring that a structure is absent. The order below is a conceptual
reading order; the actual dependency graph is determined by Lean imports.

## Seven-stage owner map

| Stage | Topic | Current starting owner |
|---|---|---|
| 1 | Lie and Jordan actions on an associative algebra | [LieJordanDuality.lean](lean/InfoGeometry/OperatorAlgebra/LieJordanDuality.lean). |
| 2 | Inner derivations, Leibniz laws, and mixed terms | The same owner, including `ad_leibniz`, `dualPlus_leibniz_defect`, and ordered-product identities. |
| 3 | Idempotent Peirce corners and tripotent inner action | [PeirceLieJordanResolution.lean](lean/InfoGeometry/OperatorAlgebra/PeirceLieJordanResolution.lean), with `ad_idempotent_tripotent` in `LieJordanDuality`. |
| 4 | Corner composition and cyclic-functional identities | `PeirceLieJordanResolution` and [PeirceDissipatorTrinity.lean](lean/InfoGeometry/OperatorAlgebra/PeirceDissipatorTrinity.lean). |
| 5 | Square-zero pairs, support, and reflexive-pair identities | `PeirceDissipatorTrinity`; concrete Witt witnesses in [LieJordanPeirceColimit.lean](lean/InfoGeometry/OperatorAlgebra/LieJordanPeirceColimit.lean). |
| 6 | Double inner derivations, dissipators, and algebraic spectral relations | [SquareZeroPairSpectral.lean](lean/InfoGeometry/OperatorAlgebra/SquareZeroPairSpectral.lean) and its component owners, especially [InnerDerivationSpectra.lean](lean/InfoGeometry/OperatorAlgebra/SquareZeroPairSpectral/InnerDerivationSpectra.lean). |
| 7 | Drazin interfaces and transport into the matrix-tower colimit | `LieJordanDuality`, [DrazinRepresentedSplit.lean](lean/InfoGeometry/OperatorAlgebra/DrazinRepresentedSplit.lean), `LieJordanPeirceColimit`, and [PeirceStarColimit.lean](lean/InfoGeometry/Canonical/PeirceStarColimit.lean). |

## 1. Lie–Jordan algebraic actions

`LieJordanDuality` works with a ring `A` that is an algebra over a commutative
ring `R`. Its operators are actual linear endomorphisms of the regular module:

\[
\operatorname{ad}_H(X)=HX-XH,\qquad
\operatorname{jordan}_S(X)=SX+XS.
\]

The Jordan action is unnormalized. The source avoids division by two and does
not assume arbitrary inputs commute. `dualPlus` and `dualMinus` add or subtract
the Jordan action from the inner derivation. These are algebraic superoperators;
the declarations do not make them affine connections on a manifold. Star
transport belongs to owners with explicit star-preservation hypotheses, such
as `PeirceStarColimit` below.

## 2. Derivations and the mixed commutator

`ad_leibniz` proves the product rule for `ad`. The Jordan-perturbed operator has
an explicit defect, recorded in `dualPlus_leibniz_defect`; it is not silently
treated as a derivation. The operators satisfy the Lie–Jordan bracket laws in
`ad_bracket`, `ad_jordan_bracket`, and `jordan_bracket`.

The ordered products retain their mixed term:

\[
(\operatorname{ad}_H-\operatorname{jordan}_S)
(\operatorname{ad}_H+\operatorname{jordan}_S)
=\operatorname{ad}_H^2-\operatorname{jordan}_S^2
+\operatorname{jordan}_{HS-SH}.
\]

Reversing the order changes the final sign. See `minus_mul_plus` and
`plus_mul_minus`. Dropping this term needs a further hypothesis. The owner
also proves conservation closure under ordered products, commutators, and
anticommutators when the supplied elements are conserved by `ad H`.

## 3. Idempotent Peirce resolution

For an idempotent `p`, the four corners act on `X` by inserting `p` or `1-p`
on its left and right. `PeirceLieJordanResolution.corner_sum` resolves the
identity action; `corner_comp` describes the sixteen compositions under
`p * p = p`. `ad_square_eq_oddPart` identifies the square of `ad p` with the
sum of the off-diagonal corners. `ad_idempotent_tripotent` then gives

\[
\operatorname{ad}_p^3=\operatorname{ad}_p.
\]

The reconstruction formulas preserve factors of two and signs. In particular,
`twice_peirce00` gives the complementary corner as

\[
2(1-p)X(1-p)=2X-\operatorname{jordan}_p(X)-\operatorname{ad}_p^2(X).
\]

`complementary_plus_sign_defect` explicitly records the defect produced by the
opposite sign. Use these owner statements instead of copying an unverified
formula from the older standalone proposal.

## 4. Corner products and trace-like readouts

`corner_mul` states the composability rule for products of corners, retaining
the middle endpoint when it matches. This is an associative-algebra result,
with the idempotence hypothesis explicit.

The cyclic-functional theorems in `PeirceDissipatorTrinity` include
`cyclicFunctional_lieOp_apply_eq_zero`,
`sumDissipator_cyclicFunctional_eq_zero`, and
`differenceDissipator_cyclicFunctional_eq_zero`. They use an additive
functional with the supplied cyclic-product property; the dissipator versions
also carry the required square-zero hypotheses. A matrix trace is one intended
setting for such a property, but a generic cyclic functional is not by itself
a positive state, an analytic trace, or a thermodynamic observable.

## 5. Square-zero pairs and genuine noncommutative witnesses

For square-zero elements `u` and `v`, the recurring combinations are

\[
\Phi=u+v,\qquad J=u-v,\qquad
V=uv+vu,\qquad\Sigma=uv-vu.
\]

Square-zero assumptions alone do not imply `V = 1` or the reflexive identities
`u*v*u = u`, `v*u*v = v`. The stronger support, sl₂, and Casimir results in
`PeirceDissipatorTrinity` name the additional hypotheses. Examples include
`reflexive_pair_sl2_relations`, `reflexive_pair_mass_idempotent`,
`reflexive_pair_casimir`, and `reflexive_pair_dirac_support_and_involution`.

For a concrete witness, `LieJordanPeirceColimit` defines stage-one
`wittCreation` and `wittAnnihilation` from the existing matrix tower.
`witt_pair_noncommutative_reflexive` proves their square-zero and reflexive
identities and that their products in opposite orders differ. This is a more
precise starting point than a scalar or dimension-only ladder record.

## 6. Dissipator and algebraic spectral relations

`PeirceDissipatorTrinity` defines `crossDissipator`, `sumDissipator`,
`differenceDissipator`, `spinDissipator`, and `sameCornerChannel` as linear
endomorphisms. `chiral_dissipator_trinity_decomposition` gives their algebraic
decomposition. The actions on square-zero and reflexive-pair sectors have
separate theorem statements and assumptions.

`SquareZeroPairSpectral.InnerDerivationSpectra` studies
`-(ad Φ)^2`, `(ad J)^2`, `-(ad Σ)^2`, their mixed products, and their sum.
Its eigen-relations have **operator-valued coefficients**, given by left
multiplication by `V` or `V * V`. The source does not normalize `V` to a scalar.
These identities should not be described as a scalar spectral theorem or a
strict positive analytic mass gap without additional structure and proof.

The umbrella `SquareZeroPairSpectral.lean` routes to the individual owners,
including mass commutation, equivariance, corners, and the trinity bridge.
Inspect the relevant component rather than treating the umbrella's subject
name as a theorem conclusion.

## 7. Drazin statements and algebraic colimit transport

`LieJordanDuality.ad_idempotent_is_own_drazin_inverse` supplies a concrete
index-one Drazin statement for `ad p` under `p² = p`.
`DrazinRepresentedSplit` provides a representation-level interface with
complementary projector laws supplied in its records; the decomposition
theorems consume those laws. That interface alone is not a construction of
generalized inverses for every operator or a simultaneous Moore–Penrose
spectral resolution.

`LieJordanPeirceColimit` transports identities through the existing `Cl(1,1)`
matrix-tower inclusions. `PeirceStarColimit` uses their actual star-preserving
maps for opposite corners, Gram expressions, refinements, and the universal
map. Its `stage_gram_posSemidef` theorem concerns the ordinary finite real
matrix Gram sum `x * star x + star x * x`.

The latter owner's stated boundary is precise: these results do not equip the
limit with an order, provide an analytic completion, or establish a strict
gap. Preserve that boundary when describing “infinite-dimensional” or
“spectral” interpretations of this corridor.

## How to extend the research outline

Start from the owning definitions above, state the intended carrier and map,
and retain each idempotence, square-zero, reflexive, cyclicity, star, or
commutation hypothesis. Link a new result to its actual declaration and
consumers. Keep physical and analytic interpretations explicitly separate
until the relevant objects and transport theorems are supplied.

For a targeted owner check, use the [root build guide](README.md), for example:

```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceLieJordanResolution
```

A successful build checks the selected source and dependencies as written.
The historical Markdown synthesis has no independent build target; copying it
into a new module would require a fresh, scoped implementation and review.
