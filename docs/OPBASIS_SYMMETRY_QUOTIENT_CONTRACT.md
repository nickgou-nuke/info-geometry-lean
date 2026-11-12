# Operator symmetry sectors and ordered bases modulo relations

## Intake and provenance

Source: Nikolai Husung, *opbasis - a Python package to derive minimal operator
bases*, arXiv:2511.00165v1, 31 October 2025. The supplied paper discusses
opbasis 0.9.7. References below use its printed page numbers.

The supplied PDF has SHA-256
`9bb6693b2e3dea7d518968f9d7f3222bfd2f9cef0f65d394fcc0e2bcc844a206`.
Implementation base: `a392af178af1fe2bcba2ba39eb405700c6ee103c` in
`nickgou-nuke/info-geometry-lean`.

This development targets the structural mathematics of sections 2.3 and 2.4:
symmetry projection, completeness of projected candidates, and ordered
selection modulo an explicit relation submodule. It does not certify the
Python implementation, its string normalizer, template enumeration, or the
listed QCD operator classifications.

## Existing owners and the actual gaps

- Mathlib `Representation.averageMap` and `isProj_averageMap` already construct
  the normalized finite-group projector and prove its range is the invariant
  submodule. `Representation.quotient` constructs the action on a module
  quotient from a proof that its relation submodule is stable.
- `Algebra/SubgroupCompressionVariance.lean` applies that average to regular
  representations. Its character multiplier is different from the arbitrary
  representation character sector needed here.
- `Algebra/CyclicOrderThree.lean` owns the specialized order-three orbit sum;
  it is not replaced by another order-three API.
- Mathlib `LinearIndepOn.insert`, `Submodule.span_insert_eq_span`, and native
  `Module.Basis` constructors support a proof of greedy selection. A
  choice-based extraction of some basis does not establish the requested
  priority order.
- `Algebra/CyclicQuotient.lean` owns the actual module quotient by the span of
  associative commutators. This owner is reused; no multiplication on that
  quotient is assumed.
- Existing projection-geometry owners already establish the commutation
  conditions for products of orthogonal projections and provide nondiagonal
  noncommuting examples. Applications must add an opbasis-specific consequence
  rather than duplicate those witnesses.

## Character projection contract

Let `k` be a commutative coefficient ring, `G` a finite group, `V` a
`k`-module, `rho : Representation k G V`, and `chi : G ->* kˣ` a genuine
group character. Assume `Invertible (Fintype.card G : k)` wherever averaging
is used. The group `G` need not be abelian, and `V` need not be finite
dimensional. This is a one-dimensional character sector, not a general
decomposition into higher-dimensional irreducible representations.

Define the character twist as the native representation

\[
\rho_\chi(g)v=\chi(g)^{-1}\,\rho(g)v.
\]

Its invariant submodule is exactly

\[
E_\chi(V)=\{v:\rho(g)v=\chi(g)v\text{ for every }g\}.
\]

The projector is Mathlib's average of this twisted representation:

\[
P_\chi=|G|^{-1}\sum_{g\in G}\chi(g)^{-1}\rho(g).
\]

The results expose the weighted formula and character equations,
prove naturality under equivariant linear maps using the same character,
and establish the exact projected-span identity

\[
\operatorname{span}_k(P_\chi(C))=P_\chi(\operatorname{span}_k C).
\]

If `C` spans `V`, this equals the character sector. If it spans a submodule
`W` preserved by the projector, it equals `W` intersected with that sector.
Group stability of `W` is sufficient for projector stability. Independently
assigned signs on generators are not assumed to extend to a character.

Equation (2.3) of the paper is an unnormalized cyclic sum. Its idempotent
normalization requires the invertible order hypothesis. Orthogonality requires
additional inner-product hypotheses and is not inferred from idempotence.

## Symmetry and relation quotient contract

Let `R : Submodule k V` satisfy
`forall g, R <= R.comap (rho g)`. This is the explicit stability hypothesis
needed to use `Representation.quotient`. Write `q = R.mkQ`.

The bridge is the actual intertwining identity

\[
q(P_\chi v)=\overline P_\chi(qv),
\]

and a native linear equivalence

\[
E_\chi(V)/(R\cap E_\chi(V))\ \simeq_k\ E_\chi(V/R).
\]

The denominator on the left is represented precisely as the submodule
`R.comap E.subtype` of `E = E_chi(V)`. Surjectivity is proved by lifting
a quotient vector and averaging its lift; it is not a supplied proof field.
The equivalence uses Mathlib's linear-map quotient-by-kernel theorem.

## Ordered selection contract

Let `k` be a field, `V` any `k`-vector space, `v : iota -> V` a candidate
family, and `order : List iota` the processing priority. A list-recursive
selector scans left to right, retaining an index exactly when its vector is
outside the span of previously retained vectors. Its finite set records the
retained labels; processing order determines which representatives survive.

Required invariants are initial-set inclusion, no new labels, preservation
of linear independence from an independent initial set, equality with the
span of the initial set and all processed candidates,
and compatibility with appending a later list. A native `Module.Basis` is
constructed from these proved facts.

For a relation submodule `R`, run the selector from the empty set on
`R.mkQ (v i)`. Define `W` as the span of the labels actually appearing in
`order`. An independently specified candidate space needs an explicit
equality with that span. The result is a basis of

\[
q(W)\subseteq V/R,
\]

equivalently of `W/(R.comap W.subtype)`. It is a basis of all `V/R` only if
`R sup W = top`. The ambient module itself need not be finite dimensional.

The proved relations-first bridge connects this formulation to Listing 3:
when an initial set of labels spans `R`, ordinary selection starting with
that set agrees with adjoining that set to selection of quotient classes.
This set equality only needs a spanning initial set; independence of the
complete ambient output additionally requires independent initialization.
For Listing 3, first select the raw relation list from the empty set, obtaining
an independent prefix with the same relation span, and then use the append
theorem to process the physical list. When relation and physical labels are
disjoint, removing the selected relation labels leaves exactly the quotient
selector's physical survivors. A prefix spanning only a smaller relation
space establishes a result modulo that smaller space.

The generic selector uses classical decidability of span membership. It is
an order-sensitive mathematical construction, not a verified executable
Gaussian-elimination implementation. The repository's elimination counter is
not assumed to equal rank without the missing RREF linkage.

## Noncommutative application and boundaries

The linear-algebra contracts impose no commutativity on operator
multiplication. Ordered words are represented in native `FreeAlgebra`, and
cyclic trace relations use the existing commutator-span quotient. In
particular, distinct words can become equal only after the explicitly chosen
quotient; they are not silently identified in the ambient algebra.

The application layer should make visible the following boundaries:

1. A later cyclic projection can destroy an earlier symmetry unless it
   preserves the earlier sector. A full finite-group average handles
   noncommuting generators without such a sequential assumption.
2. Complete raw templates are sufficient for a complete projected span; they
   are not necessary when omitted directions project to zero or into the span
   of projected candidates already retained.
3. Removing zero vectors and scalar duplicates does not by itself establish
   linear independence.
4. Relations processed first remain ambient vectors. Only passage to the
   quotient makes them zero; the physical output excludes the relation prefix.
5. EOM relations, total derivatives for an action, retained total derivatives
   for local fields, and off-shell operators are different choices of `R`.
   Boundary conditions may change that choice.

These are mathematical scope conditions. A counterexample to a naive
sequential-projection interpretation is not evidence that the Python package
contains that algorithmic error.

## Dependency order

The formal dependency order is:

1. Native representations, averaging, spans, and quotient maps.
2. Character twist and projector naturality.
3. Symmetry-stable relation descent and averaged lifting.
4. Ordered independent selection and its span invariant.
5. Quotient-basis selection and the relation-prefix comparison.
6. Noncommutative word applications and projection safeguards.

No physical classification, renormalization theorem, or correctness of the
package's syntactic normalization is supplied by these dependencies alone.

## Implemented public surface

| Owner | Explicit public declarations |
|---|---:|
| `Algebra/CyclicQuotient.lean` | 12 |
| `Algebra/FiniteGroupCharacterProjection.lean` | 17 |
| `Algebra/CharacterRelationQuotient.lean` | 9 |
| `LinearAlgebra/OrderedQuotientBasis.lean` | 31 |
| `Algebra/FreeOperatorSymmetry.lean` | 9 |
| `Canonical/OperatorBasisExamples.lean` | 31 |
| **Total audited** | **109** |

The cyclic owner count includes its nine pre-existing declarations and three
new declarations. The new development therefore adds 100 explicit public
declarations. The count includes definitions and computation lemmas, not only
major mathematical theorems. `Algebra/OperatorBasisAudit.lean` enumerates the
complete surface, and `InfoGeometry.All` imports all seven files.

## Verification record

Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. The observed Lean
executable reports commit `5045d0056413266e57c625dcd7c365b10e377c52`;
Lake reports `5.0.0-src+5045d00`. All nine focused dependency checkouts match
the manifest and have clean source trees.

The explicit owner/audit build succeeded:

```bash
python3 verification/language-symmetry/check.py build \
  InfoGeometry.Algebra.OperatorBasisAudit
```

Its 109 unique axiom records matched the audit inventory exactly, with only
`propext`, `Classical.choice`, and `Quot.sound`. Independent source review
closed against the hashes below after the compilation-driven repairs.

Independent QA then freshly elaborated all seven files sequentially from
15:12:31 to 15:13:15 UTC on 12 November 2026. One invocation of the maintained
wrapper held the shared lock across the complete pass. Each compiler command
used `lean --root=<repository>/lean -o <focused-olean> <absolute-source>`;
later files imported the fresh earlier outputs. All seven exits were 0, with
zero compiler warnings. The 109 source declarations, audit entries, and fresh
axiom records matched exactly once; only the three permitted axioms occurred.
Source/configuration hashes and all nine dependency identities remained
unchanged. This QA certifies the recorded source hashes, including the repairs,
not the original failed `e3ce1b4` committed tree. The receipt SHA-256 is
`986663d3e1ac2f41b9b5e8ed53f306dbb939b99ad41a36c3b812350bc6106cdb`.

The final semantic-vacuity diagnostic covered all seven files and reported
17 `trivial_surface` warnings and zero errors. Its warning-level diagnostic
exited 1; this is not a zero-warning result. The independent reviewer examined
all findings as meaningful computation rules, canonical quotient-map formulas,
and native API lemmas. The workflow retains their full JSON and text output
and fails on errors. The strict source screen and normal staged proof hook
also passed. No warning suppression was added.

The first CI run on `e3ce1b4d007965e2f9f2f15561476e41abd3b45e` reached
compilation and exposed selector API/parser/coercion errors. Those errors were
repaired without changing the selector algorithm, weakening its conclusions,
or introducing proof holes. The exact build log and subsequent verification
remain distinguishable from the initial source-only review.

The repaired sources were published to
[PR #333](https://github.com/nickgou-nuke/info-geometry-lean/pull/333) at commit
`7658b2ad349e4aff7664955057c92d52102dfe2c`. The dedicated
`Operator symmetry and ordered quotient bases`
[workflow run 43245769400](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43245769400)
completed successfully against that exact PR head. Job `131277863367` passed
the explicit audit build, all seven fresh sequential elaborations, the
109-entry source/audit/axiom reconciliation, and source/configuration integrity
checks. Its semantic diagnostic retained the same 17 warnings and zero errors.
The run preserved its logs, source fingerprints, and axiom inventory in
[artifact 13957151629](https://github.com/nickgou-nuke/info-geometry-lean/actions/runs/43245769400/artifacts/13957151629),
whose uploaded ZIP SHA-256 is
`515970ca1ae52c66bc4be8f23f1c0175f0c6fcae39dd599abecd4580d93a4643`.
This upstream result is separate from, and agrees with, the successful local
verification. Subsequent documentation-only commits preserve the seven source
fingerprints below; their workflow status remains available on the PR.

### Verified source fingerprints

The independent source review and fresh elaboration refer to these exact
SHA-256 values. Paths are relative to `lean/InfoGeometry/`.

| Source | SHA-256 |
|---|---|
| `Algebra/CyclicQuotient.lean` | `88fa3eb27d64e068187b6e295dac09dc1d16f089a17c331270f2c7a4ee97c79a` |
| `Algebra/FiniteGroupCharacterProjection.lean` | `47195078d5d6430f4a4ab5fbce0ae222fb87495caa308920f56ae89b57969238` |
| `Algebra/CharacterRelationQuotient.lean` | `0376792430bcdf8ecbb7384c80bf6bad0f57175e54609ccb287f620234188c54` |
| `LinearAlgebra/OrderedQuotientBasis.lean` | `ad22f4230f294865638811eab8418bfdbeaefa39c06d8c3c135808aa55fa6ae1` |
| `Algebra/FreeOperatorSymmetry.lean` | `317b85709f57ae197c967d5041447a6cd543573ad120609126377b177520e875` |
| `Canonical/OperatorBasisExamples.lean` | `6d0d2b6e98287e87921b572f16ea0f22bb10e7091b1c7cf72fdcb24df665973b` |
| `Algebra/OperatorBasisAudit.lean` | `b5162c58abe880cd3d99b025024b331e4e1220202ba85d4dfa025d62fda9e63d` |

### Integration boundary

The focused workspace uses the repository's actual `lean` source tree and
explicit targets. Cache commands run from that workspace so non-Mathlib cache
archives resolve their relative package paths correctly; source checks keep
the canonical repository-root working directory and shared build lock.

The root path preflight and the initial repository-wide CI still report
missing HomotopyHypothesis and Atlas configurations and an uninitialized GIFT
gitlink. The root pre-push gate and aggregate `InfoGeometry.All` build are not
certified by the focused results. Draft publication was explicitly authorized
with that integration boundary; no dependency pins or placeholder packages
were substituted. PR #333 remains separate from the RNQT and horizon PRs.
