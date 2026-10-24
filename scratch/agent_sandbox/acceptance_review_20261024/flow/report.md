# Stream 2 mathematical/native-carrier review — task 15

**Status: CONDITIONAL interpretation / source review only.** No compiler, build, test, CAS, or axiom-audit command was run. Existing proof bodies were inspected, not independently kernel-certified. No owner, dependency, or existing file was edited; no commit was made.

## Scope and provenance

Read `AGENTS.md`, canonical pipeline, commandments, deep-search protocol, categorical map, and check-workflow/trap guidance. Read the complete Stream 2 owner and its three repo-owned direct Meta imports. Inspected the actual relevant native definitions, instances, proofs, and import consumers listed below. Broad lexical searches covered `lean/InfoGeometry` and targeted `lean`, `tools`, `scripts`, `src`, `lakefile.lean`, and `package.json`; `context_preflight.py` was run read-only (including entrypoint and graph-indexing-surface scans). No graph freshness or compiled dependency-graph claim is made. External references were not needed or searched; generated reports were not used as proof authority.

Owner: `lean/InfoGeometry/Canonical/RootsOfZeroUnityMoebiusModularG22.lean` (782 lines in this inspection).
SHA-256: `cd82c66763e9a4fb6328af2a929fc93d00871023009a7fd875ce24e3204e6827`.
Line references below are to the inspected working-tree sources; concurrent team changes may shift aggregator lines. Paths abbreviated `Canonical/`, `Algebra/`, `Lie/`, etc. are under `lean/InfoGeometry/`.

## Ground-truth theorem contract

1. **Associative lane:** `[Ring A]`, elements `d B : A`, with `hd : d*d=0`, `hB : B*B=0`, `hr : d*B*d=d`, `hs : B*d*B=B`. Scalar results additionally use `[CommRing R] [Algebra R A]`; this supplies central scalars. Individual lemmas use strictly smaller subsets below. Neither nonzero generators, nontrivial support, full support, nor characteristic zero is assumed.
2. **Objects:** `P+=dB`, `P-=Bd`, `Delta=P++P-`, `P0=1-Delta`, `Gamma=P+-P-`, `Q1=d+B`, `Q2=d-B`, `D(a,b)=a•P++b•P-+P0`, `w=P0+Q2`, `wInv=P0-Q2`. Parentheses use associative ring multiplication in this lane.
3. **Nonassociative lane:** local eight-coordinate record `SplitOctonion R`, explicit `one/add/neg/mul`, over `[CommRing R]`; its witness is specialized to `R=Int`. It is not a `Ring A` instantiation of item 1. The exact native replacement is `InfoGeometry.Algebra.ZornVectorMatrix R` with explicit Zorn product.
4. **Imports/consumers:** owner lines 6–9 import `Mathlib` and three Meta modules, not the native flow or Zorn owners. Exact owner-name references outside the owner were found in its axiom-audit file and `Canonical/All.lean`; no other direct owner-name consumer was found in that search. This is a bounded source-search observation, not an absence claim about indirect dependents.
5. **Smallest compatibility gap:** the reviewed owner contains no map from its newly declared local `SplitOctonion` to native Zorn. The cited existing native-to-native maps do not have that local source type. A narrowly scoped, uncompiled migration candidate is supplied separately as `LocalZornCompatibilityCandidate.lean`. No new group, derivation, flow, Klein, or basis construction is needed.
6. **Not established by this owner:** an actual two-parameter group of arbitrary scalar values; analytic modular flow/KMS; a Klein bottle or fundamental-group identification; a global Bruhat decomposition/BN pair/Moufang building; any exceptional automorphism group; finite `G2(2)` or real split `G_{2(2)}` identification. The existing native infrastructure below must not be described as absent.

## Findings at the exact owner statements

### A. Active support, not automatically ambient unity

Owner lines 50–173 and 424–458 establish polynomial identities with `Delta`. `Gamma^2=Delta`, `Q1^2=Delta`, `Q2^2=-Delta` are not unconditional ambient roots of `+/-1`. With the full pair laws, these are active-corner identities; `Delta` is idempotent but need not be the ambient unit or central in all of `A`. The pair `d=B=0` is allowed. The ambient `w^4=1` at line 358 means order **divides** four, not exact order four.

Existing support and ambient-unit owners already make this distinction: `GrassmannianBundleCyclotomicOrientability.active_support_absorbs` (646), `active_support_idempotent` (657), `ambient_reflection_square` (667), `ambientReflectionUnit` (685). The last unit has value `d+B+(1-Delta)` and inverse itself; it works without `Delta=1`.

Recommendation: say “active-support polynomial roots and complementary ambient units”; do not infer spectral, harmonic, Hodge-adjoint, or topological content from the local names.

### B. `hyperbolicModularFlow_conj_d` is an unrestricted sandwich identity

Owner lines 284–289 have exactly `[Ring A] [CommRing R] [Algebra R A]`, `hd`, `hr`, and arbitrary `lam mu : R`:

`D(lam,mu) * d * D(mu,lam) = (lam*lam) • d`.

No `lam*mu=1`, `hB`, or `hs` is required. The dual result (292–297) uses just `hB`, `hs` and gives `(mu*mu)•B`. These statements are appropriate sandwich identities. Calling the swapped factor an inverse requires additional proof. Under all four pair laws, native `diagonal_mul` and `diagonal_inverse` prove that `lam*mu=1` is sufficient for two-sided inversion (the reverse follows with commutativity). This scalar constraint is not universally necessary: a degenerate support can erase it. The precise generic product is `D(lam*mu,mu*lam)`, not automatically `1`.

The owner header (22–24) advertises diagonal multiplication but the owner exports no general multiplication lemma for its local `hyperbolicModularFlow`; reuse native `diagonal_mul` instead. Its header's extra zero term does not make the unrestricted theorem a conjugation theorem.

Owner matrix witness (486–497): `lam=3`, `mu=1` over integers gives left/right factors `diag(3,1)` and `diag(1,3)` with product `3I`, not `I`. Its scale nine is deliberately a sandwich, not conjugation in integer matrix units. This calculation is source-level mathematical analysis, not a new checked counterexample.

**Consumers:** master theorem lines 424–458 and `arch2ParabolicHyperbolicFlow` 692–703 intentionally accept all scalar pairs; keep that scope and rename/reword to sandwich. For a separate conjugation statement consume `diagonalUnit` or add the inverse hypothesis. Do not silently strengthen the existing lemma's minimal hypotheses just to reuse a more bundled native theorem.

### C. Grading sign reversal is not the Klein relation

Owner `klein_bottle_orientation_reversal` (408–420) says only

`(d+B) * (dB-Bd) * (d+B) = -(dB-Bd)`

under all four pair laws. `Q1` is a reflection relative to active support. Even with full support, `Gamma^-1=Gamma`, whereas the displayed result is `-Gamma`; sign reversal is not inversion of this grading. In characteristic two the sign distinction collapses; no universal geometric orientation interpretation follows.

The genuine presented-group relation is `a*b*a^-1=b^-1`, in `Canonical/KleinPresentedGroup.lean:27–47`; its universal map is `kleinRep` at 109. Existing `reflexiveKleinRep` uses **Weyl unit** for `a` and **invertible diagonal flow** for `b`, not the grading. `ReflexiveKleinKernel.reflexiveKleinRep_not_injective` proves this representation is never faithful: the nonidentity fourth power of the abstract glide is in its kernel. Therefore not even that stronger native representation is an identification of its image with the Klein group or a deck-action construction.

**Consumers:** master theorem and `arch4KleinBottleAndG22Fusion` (720–734). Rename the grading clause in prose to “odd-reflection grading sign reversal.” If the task genuinely needs a group representation, import the existing Klein representation/kernel owners and report the nonfaithfulness boundary.

### D. Local octonion witness is coordinate algebra, not `G2`

Owner lines 501–543 duplicate the native eight-dimensional carrier and Zorn product. Lines 548–575 supply four integer basis vectors and a finite conjunction. The actual product is `octU0 * octU1 = octV2`, not `octU2`. Header lines 463–469 incorrectly say `u2` in the anticommutativity and fusion formulas; its stated associativity witness also differs from the actual theorem's third argument `octV0`. Correct prose to the literal declaration.

The actual nonassociativity witness reads `(U0 U1)V0 != U0(U1 V0)`: native table gives left side `-U1`, right side zero. The integer noncommutativity follows from `V2 != -V2`; do not generalize this inequality to every commutative ring (characteristic two is an obstruction). The multiplication equalities themselves hold over every commutative ring. Native `nonassociative_witness` uses a different triple `U0,U1,U2`, and only `[Nontrivial R]`; cite that existing theorem for a generic nonassociativity assertion rather than pretending the triples coincide.

No automorphism is defined in this owner. A nonassociative algebra element `1+U0`, or a product of two such elements, is not by itself a multiplication-preserving linear automorphism. Do not label this witness “construction of G2,” “G2 parabolic group,” or “exceptional-group fusion.” Its exact scope is “integral Zorn nilpotent basis multiplication and a nonassociativity witness.” `arch4` contains only grading reversal AND one product formula; the conjunction supplies no interaction map between the matrix and octonion carriers.

## Exact native replacement and convention freeze

Native owner `Algebra/ZornVectorMatrix.lean:318–323` stores `(a,v,w,b)`. For local `x=(re,im,u0,u1,u2,v0,v1,v2)`, fix once and for all:

```
F(x).a = x.re
F(x).v = ![x.u0,x.u1,x.u2]
F(x).w = ![x.v0,x.v1,x.v2]
F(x).b = x.im
```

No swap, conjugation, or sign is present in this local-to-native map. Native `mul` (413–418) is

```
a' = a*c + dot(v,z)
v' = a*y + d*v - cross(w,z)
w' = c*w + b*z + cross(v,y)
b' = dot(w,y) + b*d
```

The local `mul` agrees after commutative scalar reordering and `Fin 3` dot expansion. Positive cross convention: basis 0 cross basis 1 = basis 2. Thus `octU0 -> U 0`, `octU1 -> U 1`, `octV2 -> V 2`, `octV0 -> V 0`, local one -> native one. The candidate states a full coordinate equivalence plus one/add/neg/product preservation, not merely selected basis equalities. It does not claim a `RingEquiv` or add an associative instance.

**Catto/Gunaydin–Gursey is a different signed ordering.** `Canonical/CattoGurseySplitBasis.lean:34–50` owns the native linear equivalence

`splitCoordinates(a,b,x,y) = <b,-y,x,a>` in Zorn `(a,v,w,b)` slots,

with inverse `(Z.b,Z.a,Z.w,-Z.v)`. Therefore the same local element has signed coordinates

`(im,re, local_v, -local_u)`.

Its signed generators are `uZero=E22`, `uStarZero=E11`, `u_i=V i`, `uStar_i=-U i`. Local `octUi` is **minus** the signed `uStar i`, and local `octVi` is signed `u i`. Reuse `splitCoordinates_mul` and `signedBasis`; never identify local `u_i` with signed `u_i` by name. Reference star-labels are not canonical octonion conjugation.

## Proof reuse inventory (statements inspected, not recompiled)

In this table `H` means all four pair laws above. `G` abbreviates `Canonical/GrassmannianBundleCyclotomicOrientability.lean`; `F` abbreviates `Canonical/ReflexiveNilpotentFlows.lean`.

| Owner local result | Native owner declaration / lines | Precise assumptions / reuse |
|---|---|---|
| poles idempotent (70,76) | `G.active_pos_idempotent` 349; `active_neg_idempotent` 354 | `hr` only; `hs` only; unfold pole names |
| orthogonality (82,88) | `G.active_pos_mul_neg` 359; `active_neg_mul_pos` 364 | `hB` only; `hd` only |
| active support / grading square (135,153) | `G.active_support_sq` 369; `active_grading_sq` 377 | `H` |
| skew square (168) | `G.cyclotomic4Op_sq` 391 | `hd,hB`; `cyclotomic4Op=d-B` |
| complement routing / idempotency | `F.complement_annihilates` 38; `support_table` 152–169 | `H`; table includes all nine products of the three idempotents |
| parabolic addition (227,233) | `F.unipotent_add` 136; `unipotent_inverse` 142 | square-zero of the one generator; arbitrary commutative central scalar ring, specialize to integers |
| hyperbolic flow (241) | `F.diagonal` 130; `diagonal_mul` 171 | definition aligns by unfolding; multiplication under `H` |
| swapped-factor inverse | `F.diagonal_inverse` 177 | `H` and `a*b=1`; native unit packaging is preferable |
| unrestricted scalar sandwiches | `F.diagonal_scale_d` 182; `diagonal_scale_B` 191 | native statements take `H`; local statements retain weaker two-law hypotheses |
| conjugation of unipotents | `F.diagonal_scale_unipotent` 200 | `H`, `a*b=1`, result parameter `a*a*s` |
| Weyl factorization (313) | `F.weyl_factorization` 46; inverse factorization 51 | `hd,hr` only |
| inverse law (345) | `F.weyl_mul_inverse` 57; `inverse_mul_weyl` 63; `weylUnit` 68 | `hd,hB,hr` only, stronger reuse than local four-law theorem |
| fourth power (358) | `F.weyl_fourth` 82 | `H`; `weyl_square` 74 gives `1-2•support` |
| swap `d`, supports (379,393) | `F.weyl_swap_d` 90; `weyl_swap_B` 98; `weyl_swap_supports` 105 | respectively `hd,hr,hs`; `hB,hr,hs`; `H` |
| grading reversal (408) | `G.reflection_conjugates_grading` 482 | `H`; identical polynomial statement |
| native diagonal unit group | `ReflexiveFlowUnits.diagonalUnit` 18, `diagonalUnitsHom` 31, `weylUnit_conjugates_diagonalUnit` 47 | namespace is `ReflexiveNilpotentFlows`; `H`, scalar `t:Rˣ`; hom `Rˣ ->* Aˣ` |
| native parabolic unit group | `ReflexiveParabolicUnits.parabolicUnitsHom` 17; kernel criterion 31 | same namespace; `hd`; `Multiplicative R ->* Aˣ`; kernel iff parameter annihilates generator |
| unit Weyl triple / exchange | `ReflexiveParabolicUnits.parabolic_triple_eq_weylUnit` 58; `weylUnit_conjugates_parabolic` 49 | triple: `hd,hB,hr`; exchange also `hs` |
| actual Klein representation | `ReflexiveKleinRepresentation.reflexiveKleinRep` 19, generator readbacks 23,28 | same namespace; `H,t:Rˣ`; source `KleinPresentedGroup.KleinGroup` |
| representation's kernel | `ReflexiveKleinKernel` 24,49,59 | glide integer power trivial iff exponent zero; explicit fourth-power kernel; not injective for every `H,t` |
| integer color square/fusion | `Algebra/ZornVectorMatrix.U_mul_self_zero` 929; `V_mul_self_zero` 939; `U_zero_mul_U_one` 961; `U_one_mul_U_zero` 985 | `[CommRing R]`, explicit native product |
| exact local associator factors | `ZornVectorMatrix.V_two_mul_V_zero` 1025; `U_one_mul_V_zero` 1065 | `[CommRing R]`, gives `-U1` vs zero; nonzero must be supplied |
| general native nonassociativity | `ZornVectorMatrix.nonassociative_witness` 1257 | `[CommRing R] [Nontrivial R]`; triple `U0,U1,U2` |
| expand `(1+U0)(1+U1)` | native `mul_add` 1266, `add_mul` 1280, `one_mul` 640, `mul_one` 636, `U_zero_mul_U_one` 961 | generic distributive/unit laws; no new multiplication table required |
| complete signed basis/table | `CattoGurseySplitBasis.splitCoordinates_mul` 43, `signedBasis` 68, `fusion_table` 100, `mixed_table` 111 | `[CommRing R]`, signed order above |
| forbid false ring realization | `CattoGurseySplitBasis.no_injective_associative_realization` 180 | `[Nontrivial R]`, additive `f` into `[Ring A]` preserving full Zorn product implies `not Injective f` |

### A valid operator connection already exists

Do not apply `[Ring A]` flow lemmas to Zorn element multiplication. For associative operators on the Zorn module, use existing `Canonical/ZornReflexiveMatrixRepresentation.lean:12–29`:

`zornColorMatrixHom (i : Fin 3) : Matrix (Fin 2) (Fin 2) R ->ₐ[R] Module.End R (ZornVectorMatrix R)`.

It takes `q=L_map(U i)`, `c=L_map(-V i)`, derives negative CAR using `Algebra/ZornSignedCAR.lean:41,50,81`, and normalizes to `(q,-c)` by `F.negative_car_reflexive` (117). Its operator support is the full identity. `Canonical/ReflexiveMatrixCorner.lean:16,23,33,45,68,77` already owns matrix units, multiplicative linear readout, a unital **corner** ring hom, and (with `support=1`) an ambient algebra hom. This is the correct native operator route. It is not a multiplicative embedding of octonion elements into an associative ring, and not automatically an automorphism of their nonassociative multiplication.

## Real automorphism / derivation infrastructure versus finite `G2(2)`

- `Canonical/SplitOctonionAutomorphism.lean:49,70,78,116` defines real linear candidates, the unit/product predicate, its subgroup, and `RealSplitOctonionAut`. Readbacks at 129,134,147,161 give unit, multiplication, determinant and null preservation. This is actual automorphism-group infrastructure, not a coordinate toy. Some header “open debt” prose is stale relative to the later declarations and downstream Lie owners; cite the declarations instead.
- `Algebra/Zorn/CanonicalVectorMatrixBridge.lean:14,78,110` owns `canonicalVectorEquiv : Canonical.ZornMatrix Rreal ≃ ZornVectorMatrix Rreal` at `Rreal=ℝ` and forward/reverse multiplication compatibility. Reuse it after the local-to-vector map; do not reconstruct a second canonical-real carrier alignment.
- `Algebra/ZornVectorMatrix.lean:1900,2452,2493` owns explicit derivations and their Lie ring/algebra instances. `Lie/CanonicalZornDerivation.lean:19,38,73` owns `IsDerivation`, the actual `LieSubalgebra ℝ (Module.End ℝ CZ)`, and `vectorToCanonicalDerivation`.
- `Lie/CanonicalZornDerivationRealAutBridge.lean:64,97,197` owns `zornFlowRealAut`, product preservation, and `zornFlowRealAutGroupHom : Multiplicative ℝ ->* RealSplitOctonionAut` for each actual `D:canonicalZornDerivations`. These require a Leibniz derivation, not just a square-zero octonion element or arbitrary endomorphism.
- `Lie/SplitG2RealFormCapstone.lean:30–61` supplies dimension 14, the parameter linear-equivalence readout, 12-root data, and integrated native automorphism flows. The cited capstone expressly does not make a global Lie-group classification identification. Do not turn this scoped observation into a repository-wide nonexistence claim.
- A separate **finite field** lane exists: `OperatorAlgebra/G2TwoAutomorphismTheorem.lean:238–317` constructs `SplitOctF2Aut` with a genuine group structure on a Boolean eight-coordinate `F2` algebra. Its displayed multiplication convention is `(f*g)(X)=g(f(X))` (317), which must be respected in transports. Its theorem at 337 is conditional on an enumeration premise, not a count inferred from the name. `Algebra/SplitCayleyF2AutomorphismTransport.lean` supplies native F2 carrier transport. None of these turns the owner's integer witness into finite `G2(2)`.
- `Algebra/Zorn/FiniteChevalleyG2TwoBridge.lean:45–51` is numerical order-formula arithmetic, explicitly not an automorphism-cardinality proof. No finite-group order/classification conclusion is needed for this review.

**Required naming:** `G2(2)` refers to the finite-field lane; real split `G_{2(2)}` refers to the real-form lane. The ambiguous filename suffix `G22` is not mathematical evidence for either. Remove exceptional-group assertions from this owner's witness prose unless a concrete native automorphism/derivation map and the desired classification theorem are explicitly supplied.

## Consumer-aware integration plan (parent only)

1. Preserve the current owner's public results while correcting their prose: sandwich vs conjugation; grading reversal vs Klein; integral Zorn table vs exceptional group. Also fix `u2` to `v2` and retain the theorem's actual associator triple. Exact finite witnesses can remain, but must not stand in for native structures.
2. Import the native reflexive-flow owner for reused polynomial proofs; use the minimal existing lemma where its hypotheses match. Most local definitions are definitionally the same after unfolding `polePlus/poleMinus/activeSimplex/harmonicZeroPole` and native `support/complement`. Do not add a suite of duplicate alignment lemmas for mere definitional equalities.
3. For the octonion portion, preferably switch the theorem to `ZornVectorMatrix ℤ` and native `U/V/one/add/mul`; eliminate the duplicate record/table only through a parent-owned, consumer-reviewed change. If preserving local public types temporarily, first validate the sandbox equivalence/product candidate, then transport existing native proofs. That candidate is a migration aid, not a recommendation for another permanent bridge owner.
4. Keep associative matrix/operator results separate from nonassociative element results. If an action on Zorn is wanted, reuse `zornColorMatrixHom` and explicitly state `Module.End` composition. If nonassociative-product automorphisms are wanted, use the real derivation/native-automorphism lane and prove the actual chosen operator is a derivation; no such claim follows merely from color fusion.
5. Real Klein content uses `reflexiveKleinRep` together with its nontrivial-kernel theorem. Existing `ReflexiveKleinKernelRegression.lean:28–68` already exhibits rational `d,B`, a nontrivial invertible parameter 2, noncommuting images, and the grading/inversion distinction. Cite it rather than adding another scalar/matrix proxy.
6. Update internal consumers together: master theorem (424), matrix witness (486), local color witness (562), `arch2` (692), `arch4` (720), statement map (749), rules (755), and axiom-audit name list (`RootsOfZeroUnityMoebiusModularG22Audit.lean:9–98`). Review `Canonical/All.lean`'s direct import (2339 at last search) if the module is split. Native flow consumers include `ReflexiveFlowUnits`, `ReflexiveParabolicUnits`, `ReflexiveMatrixCorner`, `IdempotentOrbitContracts`, `PeirceWeightedTrace`; Klein consumers include `SuperMetriplectic/WittKleinRepresentation` and the kernel regression. Signed-basis consumers include `Algebra/ZornSignedCAR`, `Superalgebra/CattoGurseyOctonionicHadronicSuperalgebra`, and `Superalgebra/CattoGurseyOctonionicStandalone`.
7. Subsequent kernel/build/axiom verification belongs to the parent through the shared build lock, not this worker. The candidate, source prose, and search results are **not kernel certification**.

## Meta certification boundary

The source-level `TypedArchetype` definitions are populated with proofs of their literal claims. `Meta/ArchetypePipeline.lean:42–58` implements proof extraction; axiom collection at 110–137 tests permitted foundational axioms, not the correspondence between a slogan and a proposition. `#register_archetype` at 170 rejects `sorryAx` on proved entries, but nonstandard axioms produce a warning; `#audit_archetype` at 225 logs results. No execution of these commands was performed here.

The owner's prerequisite order (625) is declared scheduling data. Its rules (755–761) ignore predecessor evidence and discharge already provided proofs. `Meta/MetaEpistemicCompiler.executable_certified_compilation` (168–189) gives a valid complete schedule and the supplied statements; it does not derive a missing carrier map, classify a group, or authenticate the physical/geometric labels. In particular the two independent conjuncts in `arch4` do not become a synthesis theorem merely through their common node name.

## Deliverables / open verification

- This report: mathematical/native alignment and source references.
- `LocalZornCompatibilityCandidate.lean`: narrow local-record/native-Zorn equivalence and operation compatibility, **UNCOMPILED**. It does not duplicate native color, flow, Klein, G2, or derivation theorems.
- No new theorem has been certified by this review. Parent must compile any adopted candidate and verify intended semantics separately from axiom auditing.
