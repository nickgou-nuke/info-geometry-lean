# Peirce round trips and supported partial-isometry composition

## Problem and result

The intake combines correct noncommutative Peirce identities with stronger
claims that do not follow: nonzero coupling need not have a nonzero spectral
value, and nonzero partial isometries need not remain partial isometries
under multiplication. This change proves the exact composition obstruction,
constructs a native groupoid with the required support matching, and supplies
full matrix counterexamples to both stronger claims.

The source is preserved without edits in
[`sources/peirce_roundtrip_intake_20261116.txt`](sources/peirce_roundtrip_intake_20261116.txt).
Its SHA-256 is
`703e4726d3804a8c5d902eb6aa07668e29e38021c46c16152fdcb22dd8762934`.
The integration base is `08c34e03f610b452e03422037949196dc7d92d6d` on
`nickgou-nuke/info-geometry-lean/main`.

The [independent mathematical review](PEIRCE_ROUNDTRIP_REVIEW.md) contains
the complete claim ledger, corrected formulas, existing-owner map, and
dependency sequence. Assertions about physics, cognition, empirical fit,
or logical semantics are not imported as axioms.

## Formal intent and carriers

| Owner | Carrier | Constructed or proved surface |
| --- | --- | --- |
| `Algebra.NonCommutativeIsometry` | Arbitrary `Ring A` and `StarRing A` | Ordered composition residual, exact vanishing criterion, matched-support composition, endpoint formulas, and nonzero preservation |
| `Categorical.PartialIsometryGroupoid` | Native star projections in the same arbitrary star ring | Actual `CategoryTheory.Groupoid`, with ring elements as arrows, ordered multiplication as composition, and adjoint as inverse |
| `OperatorAlgebra.PeirceRoundTripCounterexamples` | Nontrivial algebra over an arbitrary field; full `Matrix (Fin 4) (Fin 4) ℝ` | Nilpotent algebraic spectrum theorem and noncommuting Peirce countermodel with both round trips nonzero |
| `OperatorAlgebra.PartialIsometryCounterexamples` | Full `Matrix (Fin 2) (Fin 2) ℝ` | Nonzero product of two self-adjoint projections that fails the partial-isometry equation; separate zero-product example |

The general theorems impose no commutativity, finite-dimensionality,
diagonalization, norm, or scalar-field assumption on the star ring.
The finite matrix examples refute universal implications; they do not
replace the abstract operator theorems.

## 1. Exact noncommutative composition defect

Write `sourceProjection v = star v * v` and
`rangeProjection v = v * star v`, reusing the existing definitions.
Assume only

```lean
hv : v * star v * v = v
hw : w * star w * w = w
```

The added theorem `partial_isometry_mul_residual` proves

\[
(wv)(wv)^*(wv)-wv
=w\bigl[(vv^*),(w^*w)\bigr]v.
\]

`partial_isometry_mul_iff_sandwich_commutator_eq_zero` is the exact
equivalence obtained by setting this residual to zero. The outside
operators are retained. In an arbitrary star ring, the proof does not
cancel them to claim that the two intermediate projections must commute.

The subsequent results establish sufficient conditions and useful
consequences:

- `partial_isometry_mul_of_commute` uses commutation of the two supports.
- `partial_isometry_mul_of_matched_support` uses
  `sourceProjection w = rangeProjection v`.
- `star_mul_mul_of_matched_support` and
  `mul_mul_star_of_matched_support` prove `w* (wv) = v` and `(wv) v* = w`.
- `sourceProjection_mul_of_matched_support` and
  `rangeProjection_mul_of_matched_support` identify the composite endpoints.
- `mul_ne_zero_of_matched_support` proves `wv ≠ 0` when `v ≠ 0` and the
  intermediate supports match.

The pre-existing definitions and theorem signatures remain intact, and
the existing imports are retained. There is no transitive-import change
for existing consumers.

## 2. A native groupoid with the correct composition rule

Objects are `Projection A := {p : A // IsStarProjection p}`. An arrow
`p ⟶ q` contains an actual element `v : A` satisfying

\[
vv^*v=v,\qquad v^*v=p,\qquad vv^*=q.
\]

The native `Groupoid` instance is constructed, including all laws:

| Categorical operation | Underlying ring operation |
| --- | --- |
| Identity at `p` | `p` |
| `f ≫ g` | `g.val * f.val` |
| Inverse of `f` | `star f.val` |

Composition is well-defined because the target of `f` and source of `g`
are the same object. Associativity follows from ring associativity;
identity and inverse laws follow from the proved support equations.

`Arrow.ext` requires equality of the actual underlying ring elements.
Proof irrelevance is used only for their law proofs; it does not collapse
distinct operators. The zero projection is retained with its legitimate
zero identity arrow. It is generally an isolated object, not a categorical
zero object. `arrow_ne_zero_of_source_ne_zero` and `Arrow.compose_ne_zero`
give the corresponding nonzero statements for nonzero supports.
The full-support object `unitProjection` supplies a constructed canonical
identity-arrow inhabitant; `unitProjection_id_ne_zero` proves that this
model is nonzero whenever the ambient ring is nontrivial.

This is a category of mathematical data inside ordinary Lean type theory.
No logical proof interpretation, linear type calculus, or claim that a
zero morphism proves `False` is supplied or asserted.

## 3. Nonzero nilpotent round trips

Using zero-based matrix units in the full real four-dimensional matrix
algebra, define

\[
p=E_{00}+E_{11},\quad u=E_{02}+E_{13},\quad v=E_{21}.
\]

The new owner proves actual membership in the existing opposite Peirce
corners, and proves

\[
uv=E_{01}\ne0,\quad vu=E_{23}\ne0,\quad uv\ne vu.
\]

Both products, their sum, and their difference are nonzero and square-zero.
The generic theorem `spectrum_eq_singleton_zero_of_nilpotent` proves

```lean
{K A : Type*} [Field K] [Ring A] [Algebra K A] [Nontrivial A]
{a : A} (ha : IsNilpotent a) : spectrum K a = {0}
```

It uses native algebraic spectrum and power spectral mapping. All four
matrix spectra are therefore exactly `{0}`. A nonzero coupling and even
a nonzero commutator can coexist with an empty nonzero spectrum.

Existing `PartnerEigenspaces.nonzeroEigenspaceEquiv` and Mathlib's
`spectrum.nonzero_mul_comm` remain valid and are not duplicated. Equality
of the partners' nonzero spectra does not assert their nonemptiness.

## 4. Partial-isometry nonclosure in a full matrix algebra

The second countermodel uses

\[
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
\]

Both satisfy native `IsStarProjection`; their nonzero product `W=PQ`
satisfies

\[
WW^*W=\tfrac12W\ne W.
\]

The proof also establishes the corresponding nonzero sandwiched support
commutator by applying the general composition criterion. The projection
`1-P` is nonzero, yet `P(1-P)=(1-P)P=0`, demonstrating separately why
excluding zero arrows does not repair arbitrary composition.

## 5. Existing results and remaining boundaries

The review cites the actual owners for the four-corner defect, compression
defect, round-trip reflection, partner eigenspaces, supported rotor,
real-time derivative, injective algebraic direct limit, and Drazin inverse.
They are not reimplemented under new names.

The intake does not construct the further data needed for its empirical
correlation model, polar calibration, physical Spin-to-SO angle
identification, meta-level direct system, or cohomology obstruction.
These remain explicit specification/proof obligations. The review also
corrects the claimed grading of the 15-node graph; the specified graph has
maximal chains of different lengths. No Lean theorem in this change claims
that the graph establishes necessity or uniqueness of an interpretation.

## Validation and integration

The four modules are registered by the root package's existing
`InfoGeometry` submodule glob and can be imported directly. No dependency,
toolchain, Lake configuration, proof checker, or hook is changed.

Pinned environment: Lean `4.34.1`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
The exact final evidence is in
[`PEIRCE_ROUNDTRIP_VERIFICATION.json`](PEIRCE_ROUNDTRIP_VERIFICATION.json).
The focused workflow compiles the full project-source closure of the four
owners, audits every owned declaration, checks strict source gates, and
requires zero compiler warnings in the four changed owners.

The standard root Lake build was attempted and stops at the missing
`HomotopyHypothesis` path package. The read-only path preflight additionally
reports absent Atlas configuration/provenance and an uninitialized pinned
GIFT gitlink. Focused compilation does not constitute a passing root Lake
build or an exception to the repository publication gate.
