# Constructive stabilization and presentation transport

## Source and intent

The source is Hao Song, *Superselection Rigidity of Topological
Calderbank–Shor–Steane Codes: From Koszul-Complex Models to Nonsplit
Extensions*, arXiv:2608.09913v2, 29 October 2026. The selected argument is
Section VII.1.2, Definitions 13–14 and Proposition 1, equations (118)–(124),
on PDF page 20. The downloaded PDF has SHA256
`f7d8f7b9425abcae8564ac2a592ac25b2af3f86a2129feb571027c1e28c34203`.

Primary source: <https://arxiv.org/html/2608.09913v2>.
Related existing work: <https://github.com/nickgou-nuke/info-geometry-lean/pull/342>.
That PR constructs the coupled Koszul complex and even-translation splitting;
this work starts independently from main and does not import its unmerged owners.

The intended contribution is the constructive algebra behind stabilization,
plus inverse-adjoint transport of a rectangular pairing. The paper's full
Laurent-ring, homological, and physical classification claims are separate.

## Carriers and conventions

- Coefficients are an arbitrary `Ring A`; only adjoint statements add
  `StarRing A`. Multiplication order is retained.
- Matrices, matrix units, block sums, matrix reindexing, invertibility, and
  subgroup generation use native `Matrix`, `Matrix.single`,
  `Matrix.fromBlocks`, `Matrix.reindexRingEquiv`, `Units`, and `Subgroup.closure`.
- Index types are finite and decidable, with empty types allowed. Finite
  matrix indices do not assert that the coefficient ring is finite dimensional.
- A presentation change is `U * M * V`. An elementary presentation change
  restricts the **left** unit to the scalar-entry elementary subgroup; the
  right unit remains arbitrary, as in the paper.
- Two stable formulations are treated separately on native dependent pairs
  of finite rectangular matrices: finite chains of basis changes and padding,
  using native `Relation.EqvGen`, and the paper's existential one-shot common
  padding followed by a single basis change. The ordinary/elementary
  coincidence is constructed directly for each formulation. No general
  normalization theorem identifying the two formulations is assumed.

## Owner contracts and dependencies

| Owner | Constructed result | Required predecessors |
|---|---|---|
| `Algebra.ElementaryMatrixOperators` | Explicit elementary units and inverses; actual scalar-entry elementary subgroup; arbitrary block shears belong to it; reindex transport | Native matrix and subgroup infrastructure |
| `Algebra.WhiteheadStabilization` | Block-diagonal units; four-shear factorization of `diag(U,U⁻¹)`; elementary stabilized presentation change | Elementary operators |
| `Algebra.StablePresentationEquivalence` | Ordinary and elementary move-generated stable presentation relations coincide | Whitehead stabilization and native equivalence closure |
| `Algebra.StablePaddingEquivalence` | Ordinary and elementary one-shot padded presentation relations coincide | Whitehead zero-row stabilization and finite-index padding compatibility |
| `Algebra.HyperbolicPresentationTransport` | Inverse-adjoint homomorphism, injective hyperbolic lift, symmetric/skew form preservation, full rectangular dagger-pairing transport | Block units, native adjoints, existing `SpinorialCore.Krein.IsIsometry` |

The crucial missing implication is constructed, rather than supplied in a
structure field: each block shear is a product of scalar-entry elementary
matrices. Native `Matrix.induction_on'` reduces an arbitrary block to its
single-entry summands. The Whitehead factorization then supplies the actual
elementary left multiplier after identity stabilization.

## Exact target equations

For `U` a unit in `M_m(A)` and `V` a unit in `M_n(A)`, put
`E(B) = [[1,B],[0,1]]` and `F(C) = [[1,0],[C,1]]`. Prove

\[
\operatorname{diag}(U,U^{-1})
 =E(U-I)F(I)E(U^{-1}-I)F(-U),
\]

and, for arbitrary rectangular `M`,

\[
\operatorname{diag}(U,U^{-1})(M\oplus I_m)
\operatorname{diag}(V,U)=(UMV)\oplus I_m.
\]

For the one-shot definition, use the additional rectangular identity

\[
\operatorname{diag}(U,U^{-1})\begin{pmatrix}M\\0\end{pmatrix}V
  =\begin{pmatrix}UMV\\0\end{pmatrix}.
\]

Appending zero rows after existing identity and zero padding preserves their
canonical order. Thus an existing ordinary one-shot padding witness gives an
elementary one without a general common-padding normalization theorem.

For an involutive ring, define `H(U)=diag(U,(U⁻¹)ᴴ)` and prove
`H(U)ᴴ J H(U)=J` for both off-diagonal forms, as well as

\[
(UXV)^\dagger((U^{-1})^\dagger ZW)
  =V^\dagger(X^\dagger Z)W.
\]

The last identity preserves a zero pairing for arbitrary generator maps and
reflects it when the generator changes are units.

## Bounded owner search and reuse

The search inspected repository and pinned Mathlib owner definitions,
hypotheses, alternate names, consumers, and block/adjoint APIs. Native
`Matrix.transvection` currently imposes `CommRing`, so it cannot own this
arbitrary-ring construction. The new elementary units use native
`Matrix.single` and `Units` rather than a new matrix carrier. No algebraic
Whitehead stabilization owner was found in that bounded search.

Existing `Canonical.SpinorialCore.KreinAdjoint` supplies the arbitrary-star-ring
`IsIsometry` predicate and is reused unchanged. Specialized complex Weyl and
Krein owners do not supply arbitrary-ring rectangular transport. Native
symplectic groups use commutative coefficients and ordinary transpose.

## Acceptance and limits

Promoted source must have no proof holes, custom axioms, `native_decide`, or
unsafe proof bypasses. Compilation, native declaration axiom auditing, text
checks, and independent semantic review are distinct acceptance steps. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted foundational
axioms. Build commands are serialized with the repository's shared lock.

The selected-source verification must compile its exact local dependency
closure and audit all declarations in the five new owners and the reused
Krein owner. Every new owner must
have zero compiler warnings. Root-package and tracked hook results must be
reported separately, including any pre-existing dependency blocker.

Not claimed here: a finite-depth Clifford circuit realization; finite-range
locality; superselection rigidity or classification; Schanuel or Ext
comparison; finite-index Frobenius/coextension duality; finite-torus ground
state degeneracy; nonsplitting of the coupled Koszul extension; or an
analytic/thermodynamic limit. The paper's coefficient ring is intrinsically
commutative; the arbitrary-ring generalization applies to the selected matrix
algebra, not automatically to every theorem in the paper.

The reused Krein owner is kept byte-identical. Its existing umbrella Mathlib
import also supplies analytic and dual-module APIs to historical consumers;
narrowing that import would require unrelated consumer repairs.
