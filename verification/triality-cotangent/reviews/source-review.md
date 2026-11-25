# A-A source review: triality and cotangent invariants

Reviewer: `/root/triality_refuter` (independent of the theorem authors).
Date: 2026-11-24.

## Disposition

**Accepted for the stated algebraic mathematical scope, pending Lean compilation
and the separate QA/axiom checks.** This is an independent source and semantic
review, not a kernel-verification certificate. No Lean process was launched by
this reviewer. No theorem owner was edited by this reviewer.

Reviewed the complete seven owners below, their relevant original/imported
definitions, and the old-owner extraction. The initial source observations
about two non-definitional formula proofs and imprecise finiteness wording were
resolved in the canonical sources before this disposition. The added
alternation theorem for the restricted bracket-corrected form was also read.

## Exact reviewed sources

Latest reviewed source checkpoint: local commit
`497c6d6664808e8ccb3082d6aabeba76dcd4e40a`, tree
`1c58b9eb55e126ebe8179702bdfec5e20bd73021`. The parent reports the matching
remote repair head as `21816519e42b9f76a0c8004650c6b11a6024774f` on PR #444;
this source reviewer independently verified the local commit/tree and files.

SHA-256 at that checkpoint:

| Canonical owner | SHA-256 |
| --- | --- |
| `lean/InfoGeometry/Geometry/CotangentLieForm.lean` | `2c0baeda3c9030e1338c0e407956b71d8c82cbb10d0fd82bd2d3f15fcd135749` |
| `lean/InfoGeometry/Geometry/FiniteCotangentInvariants.lean` | `119bc71961b2f7ec420fc59f9c85ae26f52c3b20e09fc7949047f38d2942f38c` |
| `lean/InfoGeometry/Geometry/CotangentFixedShear.lean` | `05ff86257a14307c219d33ae6451d3185e5484ca4f4dd5f9205d42d9a8d8e062` |
| `lean/InfoGeometry/Geometry/CotangentActionGroupoid.lean` | `5c87128ca8cb33fb142ca97ed1d9e4e1198e22c08a89057a7fe69d5579f183e8` |
| `lean/InfoGeometry/Lie/CartanTriality.lean` | `6f37bbf035d2eaba74f0c9879069d67e6bb3d20ab67ac17a58ac77572d405f26` |
| `lean/InfoGeometry/Lie/CartanTrialityRepresentation.lean` | `f46c49b533ed8f5a6bd037f3e3533dcaef486270555b9537d7daaf2d96bbd4ca` |
| `lean/InfoGeometry/Lie/CartanTrialityCotangent.lean` | `5e411f959b1f150b65e4b2d3640e89f3dca831777b8d4e046ad0b664f848411d` |

At the first source checkpoint, the groupoid and Cartan canonical files were
byte-identical to the candidates reviewed, and the invariant/shear canonical
files differed only by the reviewed corrections described below. The later
elaboration-repair commits were independently re-reviewed as recorded in
sections 8 through 12; the table above records the latest checkpoint.

## 1. Algebraic Lie cotangent form

`CotangentLieForm` reuses the actual `PhaseSpaceCarrier`,
`canonicalNeutralBilin`, and `neutralOmega` from
`InfoGeometry.Clifford.NeutralPhaseSpaceCore`, together with the existing
`SouriauContragredientPairing` owner. It does not replace those carriers with a
scalar proxy. The corrected form is a native real bilinear form:

`Omega_alpha((X,beta),(Y,gamma)) = gamma(X) - beta(Y) + alpha([X,Y])`.

Native Lie-algebra structure supplies bilinearity and alternation. Testing
against all vertical covectors first forces a left-radical vector's primal
part to vanish; testing against all horizontal vectors then forces its dual
part to vanish. Skew-symmetry gives right separation. This argument is valid
for arbitrary-dimensional real vector spaces with the full algebraic dual.
It uses the ordinary algebraic dual-separation theorem; it does not need a
finite-dimensional hypothesis or an inner product.

The paired lift is a genuine linear equivalence. Its neutral and skew pairing
invariance follows from the existing contragredient evaluation identity.
Preservation of the corrected form requires bracket intertwining, and the
native Lie-equivalence specialization supplies exactly that hypothesis.

The statement `cotangentForm_apply` originally attempted `rfl`, although the
imported `neutralOmega` formula is an algebraically proved identity. The
canonical source now invokes that formula through simplification. This source
repair has been inspected; its elaboration still requires the kernel check.

## 2. Reynolds restriction and extension

`FiniteCotangentInvariants` uses `Representation.averageMap` from the pinned
Mathlib `RepresentationTheory/Invariants.lean`. The group is genuinely finite;
the real cardinal scalar is invertible because a group is nonempty. No
finite-dimensional assumption on `V` is needed.

The constructed projection is the actual Reynolds average with codomain
restricted to the invariant submodule. The proof uses both identities needed
for an inverse construction:

- the average fixes invariant vectors;
- the average is unchanged after precomposition with any group element.

Invariant dual vectors evaluate identically before/after the action and the
average. Thus `invariantDualEquiv` is the actual restriction map
`(V*)^G -> (V^G)*`, with inverse extension by composition with the average.
Its two inverse identities hold for every vector/function, not merely for a
basis or a dimension count. This proves the requested canonical relationship
in arbitrary dimension over the real field.

`fixedCotangentEquiv` identifies fixed primal/dual pairs with the canonical
phase carrier of the invariant space. It preserves the actual restricted
ambient evaluation form, and the proof transports both separating sides
through a surjective linear equivalence. This is a genuine nondegeneracy
result on the full fixed carrier.

The bracket-corrected restriction is also alternating and nondegenerate. Its
nondegeneracy does **not** require the representation to preserve the bracket
or the base covector to be invariant: the same vertical/horizontal tests kill
the radical, regardless of the bracket correction on the primal block. The
source correctly calls this the restriction of the ambient form. It does not
assert that the invariant vector subspace is a Lie subalgebra for an arbitrary
linear representation, or that the restricted form is a canonical Lie-group
cotangent form without the additional intertwining/geometry.

The introduction now correctly calls finite symmetry a sufficient condition,
rather than implying it is a necessary condition for nondegenerate fixed loci.

## 3. Exact shear counterexample

`CotangentFixedShear` constructs the actual real linear shear
`(x,y) -> (x+y,y)` and its inverse. The fixed primal space is exactly the first
axis; the contragredient-fixed dual consists exactly of covectors annihilating
that axis. These characterizations come from equality of the actual maps.

Both factors are explicitly linearly equivalent to the reals, establishing
that their product has dimension two. Every fixed primal/dual pairing is zero,
so the pullback of the existing ambient `neutralOmega` is the zero bilinear
form. A named nonzero first-axis vector witnesses that this form is not
nondegenerate. The canonical restriction of fixed covectors to fixed vectors
also vanishes. This is a substantive countermodel, not a zero-carrier example.

The canonical version now explicitly rewrites `neutralOmega_apply` before
changing to coordinate subtraction. The docstring no longer advertises an
unproved infinite-order theorem. The counterexample itself is unaffected.

The file formalizes the linear fixed-space counterexample. Its interpretation
as the cotangent lift of an additive Lie-group automorphism is mathematically
available, but that smooth group/bundle construction is not supplied here.

## 4. Native coadjoint action groupoid

`CotangentActionGroupoid` uses a bundled group representation and the existing
contragredient owner. Native `CategoryTheory.ActionCategory` supplies the
groupoid. Its action direction and native composition order agree with the
source-trivialized convention. Raw multiplication is exposed with the exact
composability equation. The source/target, unit, inverse, and associativity
laws are the actual noncommutative groupoid laws.

The arrow equivalence and its source/target covariance induce a native
functor. Fullness, faithfulness, and essential surjectivity construct the
native equivalence. This is stronger than assigning operations suggestive
names. No commutativity of the group is assumed.

The final additions give an exact raw/native composition identity
`fromHom_comp`, characterize fixed arrows componentwise, prove injectivity on
objects for the fixed inclusion, and characterize its hom-image exactly by
fixed group labels. The fixed inclusion is properly not claimed full: an
ambient arrow between fixed objects can have a nonfixed label. The restricted
fixed-subgroup action is a genuine algebraic fixed groupoid.

No smoothness, actual derivative, or symplectic fixed-locus conclusion is
hidden in its structure fields or claimed by its documentation.

## 5. Cartan matrix source and faithful representation

Compared the old block at baseline
`fe24e350b08fdea04f74c0748ef9fd9417c47529` with its new-owner block, from
`/-- Vector–Spinor Hadamard swap` through the end of
`finrank_s3FixedCartanSubmodule`.

**Extraction is byte-identical:** 5,435 UTF-8 bytes, SHA-256
`4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.
The namespace and all declaration names/types/bodies remain unchanged. The
old-owner diff contains only the new import and replacement of that block by
an ownership comment. The deeper root/G2 bodies were not changed. This is
source-preservation evidence; downstream compilation is still separate.

The new signed permutation is an involutive orthogonal map
`P(v)=(-v3,v1,v2,-v0)`. It leaves the Hadamard generator unchanged under
conjugation, changes the old fourth-axis reflection into the requested
first-axis reflection, and transports the fixed-plane membership exactly.

The new statements supply the intake's omitted order/nonidentity facts, an
actual native fixed-plane basis and dimension theorem, and all three weight
cycle transitions, pairwise distinctness, and Euclidean norm identities.

`CartanTrialityRepresentation` constructs a native six-element dihedral matrix
homomorphism on the entire four-dimensional real carrier. The two selected
entries distinguish all six images. Conversion through matrix units and the
general linear group produces genuine linear equivalences. A constructed
group equivalence with permutations of three labels gives a faithful native
S3 representation. The all-elements invariant condition is proved equivalent
to the generator-fixed plane. The finite `decide` proofs concern finite
permutation data; real matrix equalities use proof-producing arithmetic tactics.

The numerical formulas and group normal-form order agree with the pinned
Mathlib `DihedralGroup` multiplication convention. The representation does not
pretend that sector labels alone supply an action on the matrix carrier.

## 6. Exact Cartan/vector-group specialization

The seventh owner, `CartanTrialityCotangent`, was read in full. It constructs
the native `Representation` from the faithful S3 linear action and proves
that its invariant submodule is exactly the already constructed fixed Cartan
plane. It identifies the representation's dual action with the existing
contragredient map, so the later identifications refer to the same action.

Every linear symmetry gives an actual multiplicative automorphism of
`Multiplicative (Fin 4 -> R)`. The chosen adjoint representation is explicitly
the trivial model for the additive vector group. Its compatibility with the
linear symmetry is immediate, and the general native groupoid equivalence is
instantiated using those specific objects. Equal source and target and the
additive group-coordinate composition law are correctly stated for this
abelian specialization. The source does not substitute this model for a
nonabelian Spin group.

The all-elements fixed-arrow and fixed-phase conditions are both proved
equivalent to the actual invariant primal and dual conditions. The phase
lift reuses `CotangentLieForm.cotangentLift`; it preserves the ambient skew
form. The new `fixedCartanCotangentEquiv` composes the established invariant
dual restriction equivalence with the proved equality of invariant submodules.
Its form-preservation theorem uses the actual ambient inclusion and the
canonical form on the fixed Cartan carrier. This rules out a dimension-only
identification. The separate rank computations give 2 for each fixed factor
and 4 for their product. Nondegeneracy and alternation follow from the exact
finite invariant owner.

The initial seventh-owner draft contained the identical declaration
`fixedCartanCotangentEquiv_omega` twice. That compilation-blocking duplicate
was reported to the parent, removed, and the resulting source re-read. The
`vectorAdjoint_intertwine` documentation now accurately says "specified
trivial adjoint model". The hash above is the corrected version.

## 7. Contract and validation metadata review

Read `docs/TRIALITY_COTANGENT_CONTRACT_20261124.md` completely. Its carriers,
source/target convention, counterexample, finite-group repair, seven-owner
scope, exact extraction provenance, and geometric limitations match the
reviewed source. In particular it explicitly says that the final
specialization is an abelian vector-group model and that the S3 operators
remain noncommuting on the full real four-dimensional carrier.

The contract distinguishes arbitrary-dimensional algebraic duality from
finite-group symmetry and does not claim finiteness is necessary. It does not
promote Euclidean orthogonality to a concrete Killing identity or a matrix
fixed plane to an integrated G2 subgroup. The primary-source links match the
conventions independently checked during the initial challenge.

Also read the verification README and initial validation record. Both
distinguish the focused build, fresh axiom check, and separate changed-consumer
regression target. The validation record explicitly marks kernel validation
pending; this review has not independently observed the reported local lock
wait/cancellation and does not certify execution of those workflow commands.

Metadata hashes at this checkpoint:

| File | SHA-256 |
| --- | --- |
| `docs/TRIALITY_COTANGENT_CONTRACT_20261124.md` | `d5fbddf9c4e3eb48f74f4faa79b40403c93546a0dc83655c2f9d72f149d2cc78` |
| `verification/triality-cotangent/README.md` | `c7c5c1f98b30f8a28dc88f13d7f816098397dbad972a885ea22f92e998965568` |
| `verification/triality-cotangent/VALIDATION.md` | `14662fabe6141fb0fc82f53f3e780686565ed83ecf416ab8f81cf9f783e16b14` |

## 8. Re-review of the first CI elaboration repairs

Read the complete four-file diff at commit
`40524ac6ac26db06a1c215c80854a42adf1645e7`, verified its tree hash, and
recomputed all seven owner hashes. The other three mathematical owners and
the metadata in section 7 are unchanged. The canonical sources have no
uncommitted modifications at this checkpoint; only candidate/review files
are untracked.

**Disposition: the repaired source preserves the accepted mathematical
scope.** No new mathematical hypothesis, weakened conclusion, alternate
carrier, sign change, axiom, or proof bypass was introduced by the repairs.
This does not assert that the repaired code has passed Lean; the parent
reports the new CI run pending, and no compiler/log verification was
performed by this reviewer for that run.

The exact changes are:

1. `CotangentLieForm` and `FiniteCotangentInvariants` now separate their
   generic linear sections from their Lie sections. Lie statements quantify
   over one coherent `LieRing`/`LieAlgebra` structure, rather than retaining
   unrelated ambient additive/module instances beside the additive/module
   structures inherited from the Lie instances. The intended bilinear forms,
   maps, and conclusions are unchanged. This corrects instance coherence; it
   does not assume the sought nondegeneracy or equivariance.
2. `CotangentActionGroupoid` supplies the same constructed action explicitly
   to native `ActionCategory` and `ActionCategory.instGroupoid`. Marking the
   two constructed action definitions `instance_reducible` controls instance
   elaboration and introduces no logical axiom. The source still uses the
   native groupoid/category operations. The remaining changes replace
   projection-sensitive rewriting by fully instantiated equalities and
   typed fixed-point hypotheses. Fullness, faithfulness, essential
   surjectivity, and the exact fixed hom-image remain the same claims.
3. `CartanTriality` uses explicit coordinate goals for the inverse of the
   fixed-plane parametrization and for signed-permutation plane transport.
   These are the same coordinate equalities as before. The originally
   extracted 5,435-byte block was checked again and remains byte-identical
   to the baseline, with SHA-256
   `4accd6d59f1397005999062100d15ab0a046f9199829a646907f2ddffbd81ea2`.

Because the earlier sources had elaboration errors, this reviewer compares
their written mathematical propositions and definitions, not nonexistent
successful earlier kernel declaration types. Actual declaration signatures
and foundational-axiom dependencies must come from the eventual successful
Lean run and audit.

## 9. Re-review of the second CI elaboration repairs

Read the full three-owner diff at local commit
`1f25de0af0a511911fc916bc95ab6cfa30ff7265`, independently verified tree
`5624c120b6f20beb2789391ca5d20ae04d81ce75`, and recomputed all seven source
hashes. The changed files are exactly `CotangentActionGroupoid`,
`CotangentFixedShear`, and `CartanTrialityRepresentation`; the other four
owner hashes are unchanged from the previous review.

**Disposition: accepted for the same mathematical scope.** The written
definitions and theorem statements are unchanged. The repairs alter only
proof elaboration and unused binder spelling:

- Essential surjectivity now closes its object identity with the explicitly
  action-parameterized native `ActionCategory.objEquiv.apply_symm_apply`.
  This is the same native object equivalence used by `object`, not a new
  surrogate groupoid or an assumed equality.
- The shear proofs explicitly use linearity for coordinate decomposition,
  rewrite `0 - 1` to `-1`, prove zero coordinates of the embedded real axis
  by their additive/scalar laws, and use two explicit linear-map
  extensionality steps before evaluating the restricted form. The real
  shear, its fixed submodules, and the zero-form/nonzero-radical claims
  remain identical.
- The faithful dihedral representation proofs normalize `ZMod 3` values
  and finite modular sums/differences before expanding real matrix powers.
  Generator readouts and fixed-space proofs use the same explicitly
  normalized exponents. No group, matrix, coefficient field, action,
  multiplication order, or faithful-image claim changes.

These changes add no hypotheses, axioms, unsafe operations, or weakened
conclusions. The original Cartan extraction is untouched in this commit.
This remains source-review acceptance. The parent reports partial module
compilation in CI before these repairs; independent QA owns verification of
those actual CI logs. This reviewer did not run Lean or label the repaired
run successful.

## 10. Re-review of the symbolic dihedral multiplication proof

Independently checked local commit
`0552cb77f230a6122b93c3716a0edec1a7af79e2`, tree
`5dd098208cc57e2a9922988d38a7f2e74d0b42b0`, its complete one-owner diff, and
all seven current hashes. Only `CartanTrialityRepresentation` changed;
the other six owner hashes remain identical to section 9's checkpoint.

**Disposition: accepted, with no change to the theorem scope or its recorded
boundaries.** All public definitions and theorem statements remain unchanged.
The matrix-multiplication proof now uses the already proved group presentation
symbolically instead of expanding all finite matrix cases:

- The local `hrot` derives modular-exponent addition from the existing exact
  order-three theorem and Mathlib's `pow_mod_orderOf`. The lemma's direction
  and the native `ZMod.val_add` formula were inspected in the pinned source.
- Local `hCS` and `hSC` derive the two reflection/cycle interchange identities
  solely from `S²=I` and `S C S=C²` in the actual matrix monoid.
- Local `hconj` proves `C^i S = S C^(-i)` using native `ZMod.neg_val'` and
  the three possible residue values. Its orientations are correct in all
  three cases, including `i=2`, where the symmetric `hSC` identity applies.
- The four native dihedral products are proved by associativity, these
  interchange laws, and modular exponent addition. In particular both mixed
  and reflection-reflection products use the correct `j-i` convention of
  Mathlib's `DihedralGroup`, rather than silently replacing it by `i-j`.
- The injectivity proof still distinguishes the same six real matrices by
  the same two entries. Its arithmetic tactics are sequenced so that a
  contradiction in the first entry may finish the goal before the second
  entry is inspected.

The previous two-million-heartbeat override for the multiplication proof was
removed. All new helper propositions are local proof obligations discharged
from existing results; no new public hypothesis or declaration was added.
There is no change to the full noncommutative matrix carrier or to the
faithfulness claim. The parent reports earlier partial CI success separately;
this reviewer has not run a compiler or inspected the newest run's logs and
does not mark the current kernel check passed.

## 11. Re-review of the vector-space freeness import

Independently checked local commit
`f41176fb74c49e1576a6c76b123d7cd739a5801c`, tree
`66627fad6e0a5c2c522ed89f1a003a1425385acd`, its complete diff, and all seven
current owner hashes. The sole change is the addition of
`import Mathlib.LinearAlgebra.Basis.VectorSpace` to
`CartanTrialityCotangent`. All definitions, theorem statements, and proof
bodies are unchanged. The other six owner hashes match section 10's checkpoint.

**Disposition: accepted, with no change to mathematical scope or hypotheses.**
The pinned Mathlib source defines `Module.Free.of_divisionRing` as a proved
instance, using `Module.Free.of_basis` applied to `Module.Basis.ofVectorSpace`.
Its requirements are a division ring, an additive commutative group, and a
module over that division ring. They apply to the native real vector space
`cartanRepresentation.dual.invariants`, as well as to the primal invariants.
No finite-dimensional hypothesis is required for this instance. This native
basis construction proves freeness of real vector spaces; importing it adds
no new assumption or custom axiom. The source check established that general
mathematical fact, not that the required instance would be synthesized in
the actual theorem elaboration.

The parent reports that CI4 compiled the six preceding owners and then
reported this missing freeness instance in `finrank_fixed_cartan_phase`.
The parent subsequently reports that CI5 still failed to synthesize the
required `Module.Free` instance in that final dimension proof, although the
six prerequisite owners compiled. Thus the import-only attempt was not a
successful compilation repair. Those logs have not been independently
inspected by this reviewer, and no Lean process or build was launched here.
The replacement proof is reviewed in section 12; current verification status
is governed by that later source checkpoint.

## 12. Re-review of the explicit finite basis dimension proof

Independently checked local commit
`497c6d6664808e8ccb3082d6aabeba76dcd4e40a`, tree
`1c58b9eb55e126ebe8179702bdfec5e20bd73021`, the complete one-owner diff,
and all seven current owner hashes. The only source change is the proof of
`finrank_fixed_cartan_phase`. Its statement and all definitions remain
unchanged. The other six owner hashes match section 11's checkpoint.

**Disposition: accepted, with no added mathematical assumptions.** The
replacement constructs an actual basis of the invariant product rather than
asking `Module.finrank_prod` to infer freeness of its factors:

- `fixedCartanBasis` is the existing native `Fin 2`-indexed basis of
  `fixedCartan`, obtained from the proved explicit coordinate equivalence.
- Mathlib's `dualBasis` gives a basis with the same finite index of
  `Module.Dual ℝ fixedCartan`. The required finiteness is witnessed by
  `Fin 2`; it is not a new hypothesis about the ambient space.
- Mathlib's `Basis.prod` gives a `Fin 2 ⊕ Fin 2`-indexed basis of
  `fixedCartan × Module.Dual ℝ fixedCartan`, definitionally the existing
  `PhaseSpaceCarrier fixedCartan`.
- `Basis.map fixedCartanCotangentEquiv.symm` transports that basis to the
  actual carrier
  `cartanRepresentation.invariants × cartanRepresentation.dual.invariants`.
  The inverse-equivalence direction is correct. This uses the previously
  reviewed restriction/Reynolds equivalence for the dual factor, not an
  unproved identification of invariant covectors with arbitrary covectors.
- `Module.finrank_eq_card_basis` equates the finrank with the cardinality
  of that concrete basis. Its native signature does not require a
  `Module.Free` instance for the target module. The sum index has cardinality
  `2 + 2 = 4`, giving precisely the original theorem conclusion.

The basis is a local definition assembled from existing proved data. There
is no new axiom, premise, carrier replacement, or weakened statement. The
relevant native `dualBasis`, `Basis.prod`, `Basis.map`, and
`finrank_eq_card_basis` definitions/signatures were read in the pinned
Mathlib source. No build was run. Current-revision compilation and the
independent QA/axiom checks remain pending CI6; this review is not a
kernel-verification certificate.

## Remaining scope and verification boundaries

- These owners construct algebraic groupoids and fiberwise alternating forms,
  not a smooth Weinstein symplectic groupoid or its multiplicativity theorem.
- A group automorphism and its associated linear/Lie equivalence still need
  the actual differential identification for a geometric cotangent-lift claim.
- Matrix orthogonality refers to the standard real dot product; a Killing
  normalization for a specified concrete Cartan embedding is not proved.
- The real Spin(4,4) outer-automorphism realization and complete G2 fixed-group
  identification are not consequences of the 4D matrix theorem alone.
- The seven reviewed mathematical files still require successful compilation,
  declaration coverage, foundational-axiom audit, and an independent QA
  disposition on the final source revision. This review does not label those
  unrun checks as passed.
