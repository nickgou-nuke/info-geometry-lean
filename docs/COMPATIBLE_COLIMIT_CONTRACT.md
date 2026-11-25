# Compatible algebraic colimit bridge

## Intake and scope

The user asked, verbatim, “how to apply the inductive colimit to these finite defs”
and then “publish a pr”. This follow-up implements the algebraic descent layer
discussed after PR #432, on its published commit
`c40e82ff31a4d5eb17aac53c63f3facbe0cd1ded`.

The original finite Euler / Weil–Krein / Stokes intake is preserved by that PR in
`docs/intake/zeta-weil-krein-stokes-20261123/`. The mathematical discussion in chat
is proposal evidence; the declarations and their executed checks determine the
scope delivered here.

This is an algebraic direct-limit construction over a nonempty directed preorder.
The carrier is native `_root_.DirectLimit`, with coherent linear or algebra-hom
transition maps. No new colimit carrier or structure containing the desired
conclusion is introduced. Noncomputability is explicit where native quotient
elimination and selection of a common upper stage require it.

## Source owners and smallest missing statements

| Inspected owner | Reuse and boundary |
| --- | --- |
| `Categorical/FilteredDirectLimitOwner` | Categorical module/ring universal properties; no replacement categorical carrier is required. |
| `Clifford/RealFockInfinityPairing` | Existing real two-lift pairing construction, specialized to the Fock tower; its representative proof pattern motivates the general form. Native `DirectLimit.lift₂` already supplies common-stage independence. |
| `Clifford/RealFockHilbertCompletion` | Positive completion precedent; completion is outside this algebraic change. |
| `Canonical/FilteredDirectLimitOperator` | Additive sequential operator descent; the present target uses linear operators on the native root carrier for a directed preorder. |
| `Modular/ModularColimitDerivation` | Derivation descent on a supplied noncommutative cocone; the present target constructs a native commutative-algebra `Derivation` directly. |
| `LinearAlgebra/PositiveRadicalQuotient` | Reuse the native radical quotient, positivity equivalence and negative-vector preservation. Repair the observed inner-product-core coercion error without changing its mathematical statement. |
| `Arithmetic/FiniteEulerLogDerivative` | Reuse exact finite Euler identities and their explicit remainder; no infinite product is assumed. |
| `Mathlib.Algebra.Colimit.DirectLimit` | Actual carrier, stage maps, representative induction and universal lifts. |

## Formal intent

1. Given compatible stage endomorphisms, construct their limit endomorphism.
   Prove stage readback and preservation of involution/reflection identities.
   Eigen-equations transport; nonzero eigenvectors need nonzero limit images.
2. Given exactly form-preserving linear transitions, construct the real bilinear
   form with native `DirectLimit.lift₂` and prove linearity by representative induction. Prove symmetry,
   same-stage readback, uniqueness and nonnegativity iff all stage forms are nonnegative.
3. Transfer a negative stage self-pairing to the limit and its radical quotient.
   The quotient cannot manufacture positivity. Stage quotient maps are provided
   only with radical stability; symmetric PSD target forms imply that stability.
4. Given algebra-hom transitions intertwining native stage derivations, construct
   the native limit derivation and prove its stage equation. Prove logarithmic
   derivative naturality on native units and transport the finite remainder.

## Applying the construction

Write the finite stages as `V : I → Type*` and their transition maps as
`f i j hij`. Supply the native `DirectedSystem` laws. The endomorphism and form
owners accept linear-map-class transitions; algebra-hom transitions use the
same native direct-limit carrier in the derivation owner.

For operators, prove `T j (f i j hij x) = f i j hij (T i x)` and apply
`CompatibleEndomorphisms.liftEnd`. Its stage equation is
`T∞ (ιᵢ x) = ιᵢ (Tᵢ x)`. The involution and `J * D * J = -D` theorems then
descend by checking stage images. The nonzero eigenpair theorem explicitly
requires injective bonds.

For forms, prove `B j (f i j hij x) (f i j hij y) = B i x y` and apply
`CompatibleBilinearColimit.form`. A pair of limit vectors has representatives
at a common upper stage, and native `DirectLimit.lift₂` makes their evaluation
independent of that choice. `form_of` and `form_unique` give the exact
representative equation and its uniqueness.

For native derivations on commutative algebras, prove the same intertwining
equation and apply `CompatibleDerivations.colimitDerivation`. Its underlying
linear map reuses `liftEnd`; the Leibniz law is proved by common-stage induction.
The finite Euler consumer applies the canonical algebra map to the original
finite sum and its remainder. Neither the finite prime set nor the truncation
order is replaced by an infinite limit.

The resulting pairing statements are

\[
 B_\infty\ge 0\quad\Longleftrightarrow\quad\forall i,\ B_i\ge 0,
 \qquad
 \overline B_\infty\ge0\quad\Longleftrightarrow\quad\forall i,\ B_i\ge0.
\]

Here the bar denotes the native quotient by `LinearMap.ker B∞`, under the
symmetry hypotheses of `quotient_nonneg_iff`. A negative stage vector remains
a nonzero negative vector in both constructions. These are algebraic
compatibility results; a particular arithmetic or geometric tower must still
supply the indicated transition maps and equations.

## Public declarations

The full qualified inventory is in `Categorical/CompatibleColimitAudit.lean`.

| Owner | Public declarations added |
| --- | --- |
| `Categorical/CompatibleEndomorphisms` | `liftEnd`, `liftEnd_of`, `liftEnd_involution`, `liftEnd_reflection`, `liftEnd_eigen_equation`, `liftEnd_eigenpair` |
| `Categorical/CompatibleDerivations` | `map_units_logDeriv`, `colimitDerivation`, `colimitDerivation_of`, `colimitDerivation_unique`, `units_logDeriv_of`, `negative_units_logDeriv_eulerProduct_of_eq_sum_add_remainder` |
| `LinearAlgebra/CompatibleBilinearColimit` | `form`, `form_of`, `form_unique`, `form_isSymm`, `form_nonneg_iff`, `negative_survives`, `negative_survives_quotient`, `quotient_nonneg_iff` |
| `LinearAlgebra/PositiveRadicalQuotient` | `radical_comap_le`, `radical_map_le_of_nonneg`, `quotientForm_mapQ`, `mapQ_injective` |

## Hypotheses that remain hypotheses

- The index is nonempty and directed; transition maps obey identity/composition.
- Operators intertwine the transition maps.
- Bilinear forms are preserved exactly on old vectors, rather than merely
  converging as spectral cutoffs grow.
- Positivity is assumed at the finite stages when constructing a positive core.
- Radical stability is a separate condition in the indefinite case.
- Algebra derivations satisfy the stated intertwining law.

No injectivity is needed for descended identities or preservation of a negative
self-pairing. A statement about an arbitrary nonzero vector does need additional
nonvanishing evidence.

## Explicit open obligations

This PR does not construct a Hilbert completion, an infinite Euler product,
analytic continuation, a Weil evaluation map, a GRH implication, a global
supertrace, or an infinite Gauss–Bonnet sum. It does not prove the general
quotient/colimit comparison isomorphism or an extended negative-index theorem.
The finite-stage radical maps are preparatory lemmas for that comparison.
Mathlib's finite-dimensional `QuadraticForm.sigNeg` is not used as an infinite
negative index.

Ordinary inclusions of prime sets do not make their partial Euler products a
compatible element. Cochains restrict contravariantly under cell inclusions.
Corner matrix maps are nonunital, and the existing unital Primon tensor bonds
do not preserve the parity-weighted supertrace in general. Those distinctions
are retained as implementation boundaries.

## Inherited compiler repairs

The base PR's CI run `45177878211` failed on the pinned compiler. This follow-up
repairs the required quotient dependency and the finite audit's other observed
errors and warnings:

- Eta-expand the bilinear form in `innerProductCore.inner` and mark the
  class-valued constructor `@[instance_reducible]`.
- Import the native finite-sum commutation owner and beta-reduce the cell
  circulation before `abel` in `FiniteIncidenceGaussBonnetStokes`.
- Remove unused `ext` patterns in the real reflection counterexample.
- Omit unused section assumptions from three chiral additivity lemmas and the
  doubled Hilbert pairing readback; remove two redundant `star_star` arguments.

The six dependency declarations are now included in the original audit,
bringing it to 52 records. The colimit audit adds 24 disjoint records. The
existing fail-closed checker therefore requires all 76 records, each exactly
once, with only `propext`, `Classical.choice`, and `Quot.sound` allowed.

## Validation status

Validation was performed on 2026-11-24 with Lean `4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Root dependency pins are unchanged.

Independent source audit (`audit_math`): **PASS**. Independent acceptance
(`qa_weil_krein`): **ACCEPTED_WITH_LIMITED_SCOPE**, covering the stated algebraic
construction and finite identities. The following checks were executed by QA:

```bash
python3 verification/zeta-weil-krein/check.py --wfail build \
  InfoGeometry.Arithmetic.ZetaDihedralWeilKreinAudit \
  InfoGeometry.Categorical.CompatibleColimitAudit
```

The combined build passed with 3,806 selected Lake jobs and no warnings. Fresh
`check.py env lean <owner>` checks passed without warnings for all thirteen
explicit Lean files in the workflow. These include both audit entry points,
all new implementations, the quotient owner, and repaired dependencies.

```bash
python3 verification/zeta-weil-krein/check_axioms.py \
  verification/zeta-weil-krein/logs/qa-file-ZetaDihedralWeilKreinAudit.log \
  verification/zeta-weil-krein/logs/qa-file-CompatibleColimitAudit.log
```

The actual fresh compiler output passed the checker: **76 expected records,
76 reported records, no rejected axioms**. The staged proof gate, strict
OpenGauss screen and whitespace check passed. The semantic-vacuity gate passed
at error severity with 17 reviewed warnings: sixteen representative readbacks
or elementary identities, and the existing `SplitInvolution.sq_eq_one` defining
field. None is reported as a new proof of a supplied hypothesis.

The successful QA run followed earlier local attempts interrupted by storage
or process-resource limits; those earlier attempts are not counted as passes.
The complete local receipt is `verification/zeta-weil-krein/logs/qa-acceptance.json`.
Logs are generated evidence, not tracked source; the workflow uploads its own
fresh evidence for the checked PR head. This focused result does not certify
the separate root publication gate or unrelated repository modules.

### Reviewed implementation fingerprints

| Owner | SHA-256 |
| --- | --- |
| `Categorical/CompatibleEndomorphisms.lean` | `24ab2ec066911d352229e2ad0b95a44d16e35339b5091b9c2be75e99ff4b144c` |
| `Categorical/CompatibleDerivations.lean` | `ebee9a9fc2bbb5be3a1e286f0b3d5d46c70ff9181528a3e209a13d450b4f93ef` |
| `LinearAlgebra/CompatibleBilinearColimit.lean` | `d47fcc156422845599cdda04bcfd84466e7fed3737f9c3775084b694883618de` |
| `LinearAlgebra/PositiveRadicalQuotient.lean` | `9917d82af1c64121e096c4750f376de7f7d853559f286b86a73349fa84a85e8e` |
