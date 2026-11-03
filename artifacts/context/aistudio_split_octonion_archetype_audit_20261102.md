# AI Studio split-octonion transcript: repository-grounded archetype audit

## Provenance and extraction boundary

The primary source is [`1xSSy_Z8fOSORG_mJGQISEOkQzV5lsP_1__Algebraic_Framework_of_Split-Octonions.json`](../../cached/aistudio_download_20261102/1xSSy_Z8fOSORG_mJGQISEOkQzV5lsP_1__Algebraic_Framework_of_Split-Octonions.json), with readable ordered rendering at [`full_transcript_with_attachments.md`](../../cached/aistudio_download_20261102/full_transcript_with_attachments.md) and extractor outputs in [`aistudio_extracts`](../../cached/aistudio_extracts/1xSSy_Z8fOSORG_mJGQISEOkQzV5lsP_1__Algebraic_Framework_of_Split-Octonions/).

The export contains 76 visible chunks (26 user, 50 model), 31 Lean code fences, and one text attachment in user turn 35. It has no separate `thought` field. This audit extracts visible prompts and responses; it does not claim recovery of private chain-of-thought. Ten of the eleven Drive links downloaded. `1R4cSvtth-2-5VDZ3YwrK0vq8p9_hze1Lj` returned HTTP 404. IDs `1SyAZ0b3H1KQij1R0_vzH959f1jekn6Oi` and `1iUvTlsUdZfBMgTHBGd__big54dTLpiFY` yielded byte-identical content (SHA256 `e3639590bc7ed2eef95278954d30b8fe9d24b4149e1e624f9f4655e57e431aae`). The machine-readable inventory is [`download_manifest.json`](../../cached/aistudio_download_20261102/download_manifest.json).

The ten downloaded Drive texts are complete plain-text payloads; the transcript extractor accepts the AI Studio JSON schema and therefore does not accept these text files as JSON. They remain byte-for-byte preserved in the download directory. Their first-line subject index is:

| Drive ID prefix | Intake theme | Formalization disposition |
|---|---|---|
| `1zXzG…` | Peirce decomposition, nilpotent defects, split-octonion overlay | Peirce and defect claims map to A1–A4; tensor/exterior identification is not assumed. |
| `1fFi1…` | Plato / Prop–Type / HoTT / univalence analogy | Type-theoretic analogy; no Peirce or Zorn theorem follows without a formal map. |
| `1byXi…` | Noncommutative Zorn–Nambu products and associator claims | Separate associative Peirce carrier from concrete nonassociative Zorn; inspect associator in A7. |
| `1lxzo…` | Bimodule insertion, temporal–spatial commutators, Faraday/Bianchi language | Candidate operator formulas only; no differential/field bridge promoted here. |
| `1en-o…` | 3+1 Zorn–Nambu, gauge/Pontryagin/Hodge/trace claims | The Hodge sector swap is now proved multiplicative for the explicit four-coordinate product; the ordered opposite-sector Pontryagin supertrace split and full self-associator vector-component formulas are also formalized. Claimed field equations/action interpretations are not inferred. |
| `1X7tk…` | Fourth-order Zorn–Nambu and supertrace/Yang–Mills sourcing | The pure commutator-curvature divergence contraction is formalized as A5e; sourced field equations and variational claims remain unpromoted without their analytic/action carriers. |
| `1LtuF…` | HoTT Prop vs Type and Zorn/Kantor reflection | Separate type-theoretic branch; no cross-carrier identification established. |
| `1SyAZ…` | Four-pillar Zorn/octonion gauge synthesis | Byte-identical duplicate of `1iUvT…`; keep one mathematical content record. |
| `1iUvT…` | Same four-pillar synthesis | Duplicate; see `1SyAZ…`. |
| `10VJy…` | Peirce sectors vs exterior grades, Fréchet–Lie convection | Inner derivation and Leibniz law map to A5; the ring-valued divergence/curl convection identity is now proved in `Physics/NoncommutativeZornBdGDerivations.lean`. Sector-to-exterior-form identification remains unproved. |

Full filenames, sizes, statuses, and SHA256 digests are in the download manifest; this audit does not rewrite any source payload.

## Atomic archetypes in causal order

Edges below mean proof dependency, not thematic resemblance. `P : B` is an idempotent in an associative ring; no diagonal, scalar, or commutativity model is substituted for this carrier.

| Node | Mathematical content extracted from the transcript | Repo owner evidence | Classification |
|---|---|---|---|
| A0. Associative operator carrier | Ring multiplication is ordered; commutator and defect use that order. | `OperatorAlgebra/PeirceSpine/Basic.lean`: `comm`, `conePlus`, `coneMinus`, `genV`, `genSig`. | Owner-backed |
| A1. Binary Peirce cut | `P²=P` gives the complementary cut `1-P`, four corner components, and the even/odd projections. | `Basic.lean`: `grade_projection_laws`; corner support and annihilation lemmas. | Owner-backed |
| A2. Graded product and square | Even/odd components multiply by the two parity rules; `even_odd_square_decomposition` and `even_odd_sum_square` give the ordered square decomposition. | `Basic.lean`: `evenGrade_mul`, `oddGrade_mul`, `grade_projection_laws`, `even_odd_square_decomposition`, `even_odd_sum_square`. | Owner-backed; the arbitrary `D+O` theorem requires its four explicit support equalities. |
| A3. Inner charge and spectral channels | `ad_S(X)=[S,X]` for `S=P-(1-P)` satisfies `ad_S³=4 ad_S`; polynomial expressions recover scaled even and two off-diagonal channels without division. | `Supercharge.lean`: `invS_commutator_cubic_and_scaled_peirce_channels`. | Owner-backed; scaled equations are not idempotent projectors in arbitrary characteristic. |
| A4. Defect iteration | `δ(x)=x²-x` and finite iterates preserve intertwining and split over two mutually annihilating Peirce cycles. | `Core/IdempotentDefectIteration.lean`; `OperatorAlgebra/PeirceSpine/DefectTower.lean`: `qgt_cycles_orthogonal`, `genV_defect_iterates_cycle_split`, support/projection theorems. | Owner-backed; “entropy”, “area”, or “aporia” interpretations are not consequences. |
| A4b. Defect as a generator of graded identities | Polarization gives `δ(X+Y)-δ(X)-δ(Y)={X,Y}`; specialize to the Peirce tetraktys and combine with the existing defect-transfer iterates. | `OperatorAlgebra/PeirceSpine/GeneratorDefect.lean`: `archetype_A55_idempotency_defect_grade_generator`, reusing `idempotencyDefect_add_polarization`, `defect_deriv_sig_sub_j_transfer_iterate`, and `defect_proj_phi_j_transfer_iterate`. | Kernel-checked over an associative ring with an idempotent Peirce cut. This is a distinct archived A55 claim from the already catalogued crossed-support extremal brackets; it does not assert that arbitrary `δ(X)` is an idempotent. |
| A4c. Defect jump under an odd cross-term law | In an associative ring, `p²=p` and `p*y+y*p=y` imply `δ(p+y)=y²`; on the Peirce transfer, `δ²(P+Φ)=V²−V`. | `Core/IdempotentGraphGrassmannian.lean`: `idempotencyDefect_idempotent_add_of_cross_sum`; `OperatorAlgebra/PeirceSpine/GeneratorDefect.lean`: `defect_transfer_second_iterate`. | The generic lemma assumes the cross-sum law explicitly. The Peirce statement is proved in its idempotent corner setup; no general renormalization or physical interpretation is implied. |
| A5. Fréchet–Leibniz operator derivation | On the existing finite operator algebra, the continuous inner derivation generated by an idempotent satisfies the ordinary noncommutative Leibniz rule; separately, the Peirce odd differential has a graded Leibniz law. | `Optics/OperatorDerivationForms.lean`: `FrechetOperatorDerivation`, `.ofInner`; `Canonical/PeirceFrechetOperatorArchetypes.lean`: `cutDerivation_leibniz`, `cutOddDifferential_graded_leibniz`, `cutDerivation_square_eq_oddGrade`, `cutDerivation_cube_eq_self`. | Owner-backed; preserve the distinction between an ordinary Fréchet–Leibniz derivation and a graded superderivation. |
| A5b. Inner-derivation vector calculus | For `p,A,C : Fin 3 → B`, use `∇ᵢx=[pᵢ,x]`, ordered `crossNC`, divergence, and left/right convection. Then `-curl(∇(A×C))ᵢ = div(A) Cᵢ - Aᵢ div(C) + (A·∇)Cᵢ - (∇A)·Cᵢ`, with the displayed factor order retained. | `Physics/NoncommutativeZornBdGDerivations.lean`: `innerGradient3_mul`, `negative_curl_crossNC_eq_divergence_convection`; the audit owner checks their axioms. | Kernel-checked over an arbitrary associative ring. This does not identify the vector carrier with exterior forms or assert a Hodge/Dirac–Kähler complex. |
| A5c. Bimodule insertion and inner-derivation covariance | The right insertion `(v·a)×v - v×(v·a)` is `v×[a,v]`; the left insertion `(a·v)×v - v×(a·v)` is `[a,v]×v`. Their sum is the componentwise commutator of `a` with `v×v`, by the derivation law. | `Algebra/NoncommutativeZornNambuAssociator.lean`: `bimodule_insertion_commutator_forms`, `cross_commutator_derivation`, `bimodule_insertions_sum_eq_self_cross_variation`. | Kernel-checked over an associative ring. This is the algebraic identity only; it does not define spacetime derivatives or a field equation. |
| A5d. Nambu contraction/Jacobi decomposition | The difference between the left and right contractions `v·(v×v)` and `(v×v)·v` is the cyclic commutator Jacobi sum, which vanishes by associativity. | `Algebra/NoncommutativeZornNambuAssociator.lean`: `commutator_jacobi_sum`, `nambu_contraction_difference_eq_jacobi_sum`, `nambu_cyclic_invariance`. | Kernel-checked for the explicit ordered three-coordinate expression; no arbitrary products are declared cyclic. |
| A5e. Commutator-curvature Bianchi contraction | For the inner derivations `∇ᵢ=[pᵢ,-]`, the ordered curvature components `(p×p)ᵢ` have vanishing contraction `Σᵢ[pᵢ,(p×p)ᵢ]=0`; this is the three-term Jacobi identity. | `Physics/NoncommutativeZornBdGDerivations.lean`: `commutator_curvature_divergence_eq_zero`. | Kernel-checked for arbitrary `p : Fin 3 → A` over `[Ring A]`; no differential-geometric field or equation-of-motion interpretation is assumed. |
| A5f. Four-sector Hodge swap | On the explicit carrier `ZornNC R = R × Vec3 R × Vec3 R × R`, the map `(α,x,y,β) ↦ (β,y,x,α)` is an involutive equivalence and multiplicative map; it is also additive and subtraction-preserving, transports the ordered associator, and fixes exactly the elements with `α = β` and `x = y`. It preserves the ungraded diagonal sum, negates the diagonal difference, and swaps pure upper/lower elements. | `Algebra/NoncommutativeZornNambuAssociator.lean`: `hodgeSectorSwapEquiv`, `hodgeSectorSwap_mul`, `hodgeSectorSwap_involutive`, `hodgeSectorSwap_fixed_iff`, `hodgeSectorSwap_add`, `hodgeSectorSwap_sub`, `hodgeSectorSwap_associator`, `ungradedTrace_hodgeSectorSwap`, `superTrace_hodgeSectorSwap`, `hodgeSectorSwap_pureUpper`, `hodgeSectorSwap_pureLower`. | Kernel-checked for the displayed product over arbitrary `[Ring R]`. Associator transport is a covariance identity; it does not imply associativity or alternativity of the Zorn product. |
| A5g. Opposite-sector Pontryagin split | The products of pure upper and pure lower elements land in opposite diagonal coordinates, and the supertrace of their anticommutator is `Σᵢ[yᵢ,xᵢ]` with the given order. | `Algebra/NoncommutativeZornNambuAssociator.lean`: `pureUpper_pureLower_products`, `superTrace_pure_sector_anticommutator`. | Kernel-checked as an identity for arbitrary coordinates; it does not assert the commutator sum is nonzero without extra hypotheses. |
| A5h. Full four-sector self-associator decomposition | For the explicit ordered multiplication on `ZornNC R`, both vector components of `(A*A)*A - A*(A*A)` are given by formulas retaining both diagonal coefficients, ordered dot products, self-cross terms, and left/right scalar actions; the two diagonal components are the opposite Nambu cubics. | `Algebra/NoncommutativeZornNambuAssociator.lean`: `self_associator_upper_component`, `self_associator_lower_component`, and synthesis `self_associator_full_components`; diagonal source `self_associator_diagonal_nambu`. | Kernel-checked for arbitrary `[Ring R]`. The formula is on this specified four-coordinate multiplication; it does not assert a split-octonion alternative law or associative Zorn product. |
| A6. Corner homotope bracket | The antisymmetrized triple product using an upper cone and a lower reference is a Lie bracket on the upper cone; its reference pairing gives a commutator of interior products. | `OperatorAlgebra/PeirceSpine/KantorCornerAnomaly.lean`: `upper_homotope_jacobi`, `upper_anomaly_reference_pairing`, `upper_anomaly_reference_pairing_jacobi`, trace cancellation. | Owner-backed for this defined homotope bracket only. |
| A7. Concrete split-octonion product | The actual Zorn vector-matrix carrier is alternative/nonassociative; its commutator is governed by associator identities and satisfies Malcev-type structure, not a general Lie Jacobi law. | `Algebra/Zorn/AssociatorObstruction.lean`: explicit nonzero associator and commutator Jacobiator; `Canonical/SplitOctonionMalcevIdentity.lean`: associator and Malcev proof; `Algebra/ZornVectorMatrix.lean` owns the concrete product. | Owner-backed, with counterexample to the transcript's unrestricted Jacobi claim. |
| A8. Classical 3-vector cross product | `cross3` is defined over a commutative coefficient ring and has skew/self-zero laws. This is not identified with the generic associative Peirce homotope or the concrete split-octonion commutator without a proved map. | `Algebra/ZornVectorMatrixCrossProductBridge.lean`: `cross3` and `master_zorn_cross_product_synthesis`. | Separately owner-backed; bridge to A6/A7 remains unproved here. |
| A9. Physical and psychological readings | Black-hole entropy, gauge charges, color confinement, Jungian shadow, or “consciousness” are interpretations, not propositions derived from the preceding ring laws. | No operator-to-physics interpretation map is supplied by the cited algebraic owner declarations. | Interpretation-only / open bridge. |

Dependency poset: `A0 → A1 → A2 → A3 → A4`; `A1 → A5`; `A1 → A6`; `A7` and `A8` are separate algebraic branches. Any edge connecting A6/A7/A8, or any edge from A0–A8 to A9, requires an explicit carrier map and compatibility theorem.

## Corrections to generated Lean claims

1. `Ring B` already supplies associativity, so its commutator has Jacobi. That fact does not make the concrete Zorn vector-matrix carrier associative. The concrete owner records a nonzero commutator Jacobiator on `(u1,u2,u3)`; the true split-octonion branch is alternative/Malcev.
2. The transcript’s ordered upper-cone formula `N₊(A) N₋(C) N₊(Z) - N₊(Z) N₋(C) N₊(A)` is exactly the repo’s `upperHomotopeBracket` after unfolding `opKantorAnomaly`. The owner now exposes this as `upperCornerCrossProduct` and proves its Jacobi identity. This is the associative Peirce homotope bracket; it is not the vector cross product or commutator of the nonassociative split-octonion `ZornVectorMatrix` carrier, whose commutator Jacobi counterexample remains valid.
3. A bundled Fréchet–Leibniz derivation is not the nonlinear Fréchet derivative of a field. The repo explicitly models the former and proves its Leibniz law.
4. Diquark, baryon, SU(3), color confinement, trace-zero-as-unimodularity, black-hole entropy, Page curves, and dyon mass formulae do not follow from corner support or a commutator identity alone. The downloaded generated code contains proposed definitions, not verification evidence.
5. The stage labels D65–D67 and biological/psychological metaphors are transcript notation, not repository theorem dependencies.

## Ground-truth formalization contract

- **Carrier:** arbitrary associative `Ring B` with a specified idempotent `P` for Peirce statements; finite operator algebra with its existing norm/topology for continuous Fréchet derivations; concrete `ZornVectorMatrix R` over `[CommRing R]` for split-octonion statements.
- **Ordered operations:** `comm X Y = X*Y - Y*X`; `conePlus=P*A*(1-P)`; `coneMinus=(1-P)*C*P`; multiplication order is material.
- **Reuse:** the declarations in A1–A8 above. The transcript's generic names are not introduced as duplicate APIs.
- **Gaps addressed in this pass:** the generic inner-derivation divergence/curl convection identity in `Physics/NoncommutativeZornBdGDerivations.lean`, and the insertion/Jacobi decomposition in `Algebra/NoncommutativeZornNambuAssociator.lean`. The all-spin cyclotomic composition, corrected raw Reynolds identities, nilpotent clock candidates, and unipotent conjugation already have owners in `OperatorCyclotomicParafermions.lean`. A unified theorem identifying the separate Peirce homotope, 3-vector cross product, exterior forms, and nonassociative split-octonion product is not asserted.
- **Verification boundary:** previous targeted checks recorded for the staged `Basic.lean` and `Supercharge.lean` changes cover those owners only. No claim is made that the entire repo or every transcript fence has been compiled. This report is an extraction/audit artifact, not a theorem.

## Canonical noncommutative Lean spine already in the repo

```lean
-- Associative Peirce carrier, existing owner declarations:
evenGrade_mul hP X Y
oddGrade_mul hP X Y
even_odd_square_decomposition hP X
invS_commutator_cubic_and_scaled_peirce_channels (P := P) hP X
genV_defect_iterates_cycle_split hP A C n

-- Existing finite-operator Fréchet–Leibniz owner:
cutDerivation_leibniz P X Y
cutDerivation_square_eq_oddGrade P X

-- Distinct bracket/product branches:
upper_homotope_jacobi hP C A Z W
associator_e11_u1_u2_ne_zero
not_jacobi_commutator_concrete_zorn
malcev_identity  -- see SplitOctonionMalcevIdentity owner
```

Names are shown as source-level navigation, not as a newly compiled combined module. The owner statements and proofs remain authoritative.

## Canonical carrier and structure map

This is the prerequisite type map for any further theorem work. “Operator” is
not a common Lean carrier across these branches. Each row names the native
mathematical structure that the claims actually require; a bridge between rows
must be an explicit homomorphism/intertwiner with its laws proved.

| Archetype family | Canonical carrier / Lean structure | Core operations | What its claims can prove | Required bridge before identification |
|---|---|---|---|---|
| Ordered operator algebra, Peirce cut, defects, cyclotomic sums | Associative `Ring B`; an idempotent is a term `P : B` with `P * P = P`. For a genuine module of operators, use an endomorphism ring such as `Module.End R M`, not an arbitrary ring renamed “operator.” | Ordered multiplication, commutator, polynomial evaluation, `δ x = x*x-x`, Peirce corners. | Ring identities, Peirce decomposition/support, finite geometric sums, nilpotent inverses, commutator identities. | Calling `B` bounded operators, matrices, or observables requires a representation and any needed norm/star/topology structures. |
| Isotropic/nilpotent pair and emergent corners | Two elements `u v : B` with `u*u=0`, `v*v=0`; a square-zero submodule/ideal is additional closure structure. | Ordered composites `u*v`, `v*u`, Jordan sum and Lie difference. | Mutual annihilation of round trips; tetrad identities; conditional idempotence under regularity `u*v*u=u`, `v*u*v=v`. Nilpotence alone does not imply idempotence. | Peirce-corner interpretation requires a specified idempotent and support proofs, or regularity hypotheses deriving one. |
| Homotope cross product / Kantor bracket | Associative ring with homotope product on its additive group, `x ⋆c y := x*c*y`; prove any cone carrier is closed before restricting. | Homotope product and commutator `x⋆c y-y⋆c x`. | Associativity of `⋆c`, hence Jacobi for its commutator; explicit triple-product expansions and corner support. | This is not the cross product or element commutator of the Zorn split-octonion algebra. Identification needs a bracket-preserving map. |
| Concrete split-octonion/Zorn algebra | Actual Zorn vector-matrix carrier over its coefficient ring, with nonassociative multiplication and alternative/Malcev structure. | Zorn multiplication, associator, commutator. | Alternative identities, associator formulas, Malcev identity; counterexamples to unrestricted commutator Jacobi. | Associative-ring facts cannot be transferred without a representation preserving operations; associativity cannot be silently assumed. |
| Peirce grading, Sylvester table, DeWitt LDU | Associative `Ring B` plus `P²=P`; all blocks are terms in the same ring. | Complement, corners, unipotent factors, ordered products. | Block decomposition, Schur correction identities, stripping/inverses, parity-string transfer. | General block-matrix Schur theory needs its matrix carrier and invertibility assumptions; internal Peirce factorization is not that theory automatically. |
| Jordan–Wigner chain | One associative ring with involutive parity string and explicit cross-site laws; alternatively an indexed tensor product with site embeddings. | Dressed modes and anticommutators. | Two-site nilpotent-sum and additive-metric closure under stated relations. | An actual multi-site representation requires site-indexed carriers, embeddings, and recursion; two-site relations do not construct it. |
| Derivations, differential forms, gauge/Lax equations | Lie algebra of derivations acting on an algebra/module; differential forms over it; for NLS, formal-jet ring and matrix-valued connection. | Derivation bracket, covariant derivative, curvature, exterior differential, formal total derivatives. | Curvature/Bianchi identities and formal zero-curvature equivalence to jet residuals at declared scope. | Analytic PDE requires function spaces, regularity, and a formal-to-analytic bridge; a Peirce commutator is not an NLS evolution theorem. |
| Coxeter/reflection theory | Coxeter system `(W,S)` or geometric/reflection representation with root/module carrier. | Simple reflections, length, braid moves. | Reflection-product orders and Matsumoto coherence from Coxeter axioms. | An operator quadratic does not define a Coxeter system; a representation and relation proofs are required. |
| Cyclotomic/Reynolds operators | Associative ring with one element `x` and finite sums of its powers. A true averaging projector additionally needs an action and normalization/invertibility hypotheses. | Geometric sum and raw weighted conjugation sum. | Telescoping and centralizer/intertwiner endpoint laws. | Raw sum is not automatically idempotent; `xⁿ=1` does not supply a primitive root, braid law, or parafermion representation. |
| Categorical synthesis | Actual category, functor, natural transformation, diagram, and (co)limit with universal property. | Morphism composition and universal maps. | Categorical consequences of the specified diagram and verified universal property. | A documentation dependency DAG is not itself a category or categorical theorem. |

### Typed dependency order

Edges are proof dependencies, not narrative chronology:

```text
associative ring
  ├─ idempotent → complement → Peirce corners → grading / LDU / Jordan–Wigner identities
  ├─ square-zero pair → round-trip identities → [regularity] emergent idempotents
  │                                  └→ homotope product → Lie commutator / Jacobi
  ├─ one element + finite powers → geometric/cyclotomic telescoping → conditional inverse/intertwiner
  └─ derivation Lie algebra + connection → curvature identities
       └─ formal-jet matrix connection → NLS residual equivalence

alternative Zorn algebra → associator → Malcev law
Coxeter system/representation → reflection order → Matsumoto braid coherence
category + diagram → (co)limit universal property
```

The regularity edge is an additional hypothesis. There is no edge from
homotope Jacobi to Zorn commutator Jacobi, an operator quadratic to Coxeter
classification, formal jets to analytic solutions, or a dependency graph to a
categorical colimit without the corresponding structure/map and compatibility
proof.

### Implementation rule for gaps

For every unowned row, write an atomic theorem contract: exact owner and
carrier, definitions, ordered proposition, hypotheses, and targeted kernel
build. Reuse existing owner declarations. Add a new lemma or theorem only after
a repository-wide semantic search establishes the specific proposition is
missing. The audit itself is navigation, not kernel evidence that every
declaration in generated transcript code exists or compiles.

## Supplemental Drive-note extraction and formalization

The additional supplied Drive items resolve to nine distinct downloaded text
notes plus one duplicate pair; the separate split-octonion AI Studio JSON is
the 76-chunk transcript above. The remaining Drive ID recorded as HTTP 404 is
not evidence and is excluded. Across the readable notes, the reusable
mathematical spine is:

1. **Ordered operator algebra:** associative coefficient multiplication and
   commutators, with order retained.
2. **Peirce cut and four corners:** the diagonal/off-diagonal decomposition
   and the support rules of the two transition directions.
3. **Cyclic cubic / Jacobi contraction:**
   `X * comm Y Z + Y * comm Z X + Z * comm X Y` is the six-term alternating
   cubic. Its left and right commutator contractions agree by associativity;
   repeated adjacent inputs vanish.
4. **Corner localization:** when the three inputs are positive-sheet
   transition products `qgtPlus`, the alternating cubic is supported in
   `P B P` and is neutral under the Peirce grading.
5. **Separate Zorn branch:** the actual Zorn product is nonassociative and its
   element commutator is not a Lie bracket in general; its Malcev identity is
   the relevant closure law.

The cubic claims in items 3–4 are now kernel-checked in
`lean/InfoGeometry/OperatorAlgebra/PeirceSpine/AlternatingCornerTriple.lean`.
They are proved for arbitrary associative `[Ring B]`, with the Peirce support
premise only where needed. This is an associative Peirce-corner result; it
does not identify the cubic with the concrete split-octonion cross product.

Other note claims remain classified rather than imported wholesale:

- The transcript's explicitly defined noncommutative four-sector product has
  now been formalized in `Algebra/NoncommutativeZornNambuAssociator.lean`.
  Over an arbitrary associative coefficient ring, its norm-associator diagonal
  is exactly `nambu(y) - nambu(x)` and the opposite on the other diagonal,
  where `nambu(p) = p · (p × p)` preserves factor order. This verifies the
  displayed algebra identity for that explicit product; it does not identify
  the product with an associative algebra, the separate `ZornVectorMatrix`
  split-octonion carrier, or a Yang–Mills/Nambu field equation.
  The same owner also proves that self-crossing is the vector of three
  coefficient commutators and that the right-ordered cubic contraction
  `dot (cross p p) p` equals `dot p (cross p p)` by cyclic permutation of the
  six ordered monomials. This is a property of this cubic polynomial, not a
  general cyclicity law for arbitrary products in the coefficient ring.
  For the explicit pure upper-cone element, its left- and right-associated
  cubes are now proved to land in opposite diagonal coordinates with the same
  negative Nambu coefficient; their self-associator therefore has opposite
  Nambu coefficients on those two coordinates, while their sum has equal
  negative coefficients on both diagonal coordinates. The Nambu cubic is
  also proved equal to the cyclic coordinate/commutator expression. These
  statements are scoped to the transcript's displayed four-sector
  multiplication. The same owner proves the transcript's algebraic
  supertrace formula for the partial-bar right norm:
  `superTrace(X * conj X) = [α, β] + Σᵢ[xᵢ, yᵢ]`. This does not imply a
  Yang–Mills Gauss law or any physical zero-point interpretation. It also
  proves the right-norm components of the symmetric state `psiCov(a,p)`: equal
  diagonal terms `a² + p·p` and both vector slots `-(commVector(a,p)+p×p)`.
  The upper-vector component of the self-associator for the lower-sector state
  `(a,0;p,0)` is now proved to be
  `cross (vecRightMul p a) p - vecLeftMul a (cross p p) -
  cross p (vecRightMul p a)`, with left and right scalar actions kept
  separate. The attachment's proposed nonvanishing
  witness uses `p=(0,b,b)`; its upper-vector anomaly is actually zero for
  every `a,b`, as `repeated_lower_coordinates_have_zero_insertion` proves.
  A replacement witness in `InsertionMatrixWitness` uses the noncommutative
  operator algebra `Matrix (Fin 2) (Fin 2) ℤ`: the vector coordinates are
  orthogonal matrix units and commute, while an off-diagonal matrix unit in
  the Zorn diagonal coefficient produces a nonzero upper-vector associator.
  Thus the general
  insertion formula and a valid conditional finite-dimensional witness are
  formalized, while the original witness is rejected.
  The full self-associator diagonal claim is also proved for every element of
  the explicit carrier: its diagonal coordinates are `nambu(x)-nambu(y)` and
  the opposite, with the scalar-sector terms cancelling in the ordered
  expansion. The general upper and lower vector components are now proved as
  `self_associator_upper_component` and `self_associator_lower_component`,
  retaining their ordered dot, cross, and scalar actions; `self_associator_full_components`
  collects all four coordinates in one theorem.
- The Fréchet–Leibniz derivation and the signed graded Leibniz differential are
  distinct existing owner theorems in `Canonical/PeirceFrechetOperatorArchetypes.lean`.
  The drafts' BV/Dirac–Kähler identities need their own exact operator-form
  definitions and are not consequences of those derivation laws.
- Proposed equalities between Zorn multiplication, exterior wedge, Hodge
  contraction, and Yang–Mills operators require a proved map between their
  carriers. No such equality is inferred from matching coordinates or
  metaphors.
- The proof-relevance/univalence, physical confinement, black-hole, and
  Jungian interpretations are not consequences of the Peirce and cubic
  identities formalized here.
- Custom scalar-coordinate `Op` snippets in the notes are not used as
  substitutes for the repository's arbitrary noncommutative ring or actual
  operator-valued Zorn carrier.

The resulting dependency chain is `Ring → idempotent cut → corner products →
commutator Jacobi/alternating cubic → positive-corner support and neutral
grading`. The concrete nonassociative Zorn/Malcev results and the Fréchet
operator-derivation branch remain separate nodes until a compatibility map is
proved.

## Supplemental Sylvester / DeWitt / Jordan–Wigner archetypes

The later Sylvester–Wigner material adds the following ordered operator claims.
The verified statements live in
`lean/InfoGeometry/Algebra/PeirceDeWittChiralSplit.lean`; they are proved in
the same associative ring with a Peirce idempotent, rather than by identifying
that ring with a tensor product or with classical Sylvester matrices.

| Node | Exact mathematical content | Disposition |
|---|---|---|
| SW1. Peirce block LDU | For `n = (1-p)c p`, `u = p a (1-p)`, and arbitrary lower diagonal block `d`, `(1+n) (p + (d - n*u)) (1+u) = p + u + n + d`. In the owner notation this is `dewitt_peirce_LDU`. | Kernel-checked. The correction is the ordered product `n*u`; it is an algebraic block correction, not an expression involving inverses of `p` or `1-p`. |
| SW2. Unipotent inverse | Peirce off-diagonal corners square to zero, hence `1±n` and `1±u` are mutual two-sided inverses. | Kernel-checked as `dewitt_unipotent_inverse`. |
| SW3. Block stripping | Multiplying the reconstructed block on the left and right by the corresponding inverse factors gives back `p + (d - n*u)`. | Kernel-checked as `dewitt_peirce_block_diagonalization`, derived from SW1 and SW2. |
| SW4. Parity-string commutator transfer | If `n*s = -(s*n)`, then `{n,s*x} = -s[n,x]`, with products kept ordered. In the Peirce cut, grading times the odd part is exactly `p*x - x*p`. | Kernel-checked as `jw_commutator_to_anticommutator`, `grading_oddPart_left_action`, and `grading_oddPart_eq_cut_commutator`. Cross-site commutation remains a separate hypothesis. |
| SW5. Two-site sum closure | Square-zero `x,y` with `{x,y}=0` have `(x+y)^2=0`; paired sums have additive anticommutator when both mixed anticommutators vanish. | Kernel-checked as `jw_two_site_sum_square_zero` and `jw_two_site_metric_additive`. These are composition lemmas, not a construction of a tensor chain. |
| SW6. Dressed two-site closure | For an involutive string `s`, commuting site-2 modes, square-zero site modes, and the four cross-site anticommutator relations, dressing by left multiplication with `s` preserves square-zero and yields a square-zero total mode; the total anticommutator is the sum of the two site anticommutators. | Kernel-checked as `jw_dressing_preserves_square_zero` and `jw_two_site_chain_closure`. This is an internal associative-ring theorem with its inter-site relations explicit. It does not construct the hypotheses from a tensor product or a family of Peirce idempotents. |

The stronger transcript assertions that the round-trip products are Schur
complements in a general block-matrix inverse problem, or that the internal-ring
lemmas alone construct an `n`-site Jordan–Wigner representation, are not
claimed. The latter needs an explicit site family, parity-string recursion,
and cross-site relations. Existing owners in
`Physics/JordanWignerMultiDyads.lean` and
`Canonical/Cl11TensorTowerCrossSiteCAR.lean` supply separate indexed/tensor
constructions; this supplemental algebra does not replace or identify those
carriers.

## Supplemental Lax-pair and Coxeter archetypes

| Node | Owner-backed mathematical statement | Boundary |
|---|---|---|
| LAX1. Abstract Peirce commutator | `OperatorAlgebra/PeirceSpine/ParaKahlerBregmanModularNoetherPoset.lean`: `archetype_M5_four_wave_mixing_and_zakharov_shabat_nls_lax_pair` proves the four cubic identities and `[Σ+Φ, VΣ] = -2 V²J` in an arbitrary associative ring with an idempotent cut. | Kernel-checked by targeted build. This is a commutator identity in that abstract Peirce algebra; it is not by itself the differential zero-curvature equation or an NLS evolution theorem. |
| LAX2. AKNS formal-jet curvature | `Physics/CubicNLSAKNSLaxPair.lean`: `curvature_eq_nls_residuals` and `flat_iff_nls_residuals_zero` identify the entries of a specified 2×2 matrix zero-curvature expression with coupled cubic NLS jet residuals; the focusing reduction is handled by separate theorems. | Kernel-checked by targeted build. The carrier is `Matrix (Fin 2) (Fin 2) ℂ` with formal jet coordinates; this is not a theorem identifying it with the abstract Peirce operator pair, and it supplies no function-space/analytic PDE bridge. |
| LAX3. Derivation-based noncommutative connection | `OperatorAlgebra/DerivationDifferentialForms.lean`: `covariantDerivative_commutator` identifies `[∇ₓ,∇ᵧ] - ∇_[x,y]` with `ad_(F(x,y))`; the Maurer–Cartan zero-curvature condition removes the defect, and `connectionCurvature_bianchi` proves the covariant Bianchi identity. `OperatorAlgebra/DerivationGaugeTransport.lean` proves exact gauge covariance using the faithful regular-module action. | Existing associative-algebra owner, with ordered products and possibly noncommuting derivation directions. This supplies the general connection/curvature archetype; no custom duplicate was needed. |
| COX1. Geometric Coxeter representation | `Exceptional/CFSGPort/CoxeterMatsumoto/Geometric.lean` proves the exact order of products of simple reflections from the geometric representation. | Repo-owned Lean theorem; its geometric representation is the relevant Coxeter source. The arbitrary-ring quadratic for the Bruhat element does not imply a Coxeter system or crystallographic classification. |
| COX2. Matsumoto braid coherence | `Exceptional/CFSGPort/CoxeterMatsumoto/Matsumoto.lean` proves reduced-word equivalence by braid moves and a monoid-valued reduced-word invariance theorem. | Separate Coxeter-system result; no map from the parafermion/Peirce operators to those simple reflections is formalized by the Lax identities above. External source copies under `external_refs/` are references, not repo-owned proof authority. |

The Lax and Coxeter nodes therefore remain distinct in the causal graph:
Peirce cut → abstract Peirce commutator formula; derivation Lie algebra +
connection one-form → curvature operator identity/Bianchi/gauge covariance;
formal-jet matrix connection → NLS residual equivalence; Coxeter matrix/geometric
representation → exact reflection-product order → Matsumoto braid coherence.
Any edge between these branches requires an explicit representation/intertwining
theorem.

## Supplemental operator-cyclotomic parafermion archetypes

The parafermion claims have distinct operator-algebraic owners in
`Algebra/OperatorCyclotomicParafermions.lean` and
`Algebra/IsotropicCyclotomicGalois.lean`:

| Node | Kernel-checked owner content | Scope boundary |
|---|---|---|
| PF1. Green/DKP identities | `square_zero_green_dkp_relations` now proves both ordered Green commutators, both symmetric anticommutator relations, the sum/difference cubic equations, and the mixed double-commutator pair. | For square-zero `u,v` in an associative ring, with the generated anticommutator retained as an operator coefficient. |
| PF2. Bruhat/Coxeter polynomial | `bruhat_inverse_pair`, `bruhat_quadratic_relation`, and `bruhat_cyclotomic_evaluations`. | Operator coefficients establish identities for this ordered product; a Coxeter classification still needs a representation into the repo's Coxeter reflection systems. |
| PF2a. Reynolds operator carrier | `parafermionReynoldsAddHom` and `parafermion_reynolds_addHom_quasi_idempotent`. | The raw Reynolds construction is an additive endomorphism of `B`; its finite-order relation is quasi-idempotence under composition. It is not elementwise idempotence. A normalized projection requires a scalar/module carrier in which the order is invertible and a separately proved normalization theorem. |
| PF3. Cyclotomic defect/Galois | `cyclotomic_polynomial_calculus`, root/meta-defect results, and the support-qualified isotropic-pair results in `IsotropicCyclotomicGalois.lean`. | Absolute cyclotomic polynomials in one ring element are distinct from relative polynomials with the generated support as constant term. The latter close under mutual regularity. The four sandwiches are not claimed as a global V₄ action off support. |
| PF4. Cube-zero inverses | `cube_zero_cyclotomic_inverses` and `cube_zero_conjugation_automorphism`. | Exact polynomial inverses and inner automorphism for `a³=0`; no division is used. |
| PF5. Adjoint tower | `cube_zero_inner_derivation_tower` proves the degree-two through degree-five formulas. | An identity for the inner derivation in any associative ring, not a represented quantum-group or analytic parafermion model. |
| PF6. Pair condensation | New `cube_zero_pair_condensation` applies the cube-zero square lemma to `a²,c²`, then derives the tetraktys and Bruhat cyclotomic evaluations for that square-zero pair. | The two cube-zero generators need no commutation relation; claims are only those in the theorem's displayed conjunction. |

The generated sign claims required correction. With `Σ=[u,v]`, the square-zero
Green identity is `[u,[v,u]]=+2Vu`, and the symmetric one is
`[v,[u,v]]=+2Vv`; writing the first as `-[Σ,u]` gives the wrong sign. For
`Φ=u+v`, `J=u-v`, the two mixed DKP identities are
`[Φ,[J,Φ]]=-4VJ` and `[J,[Φ,J]]=+4VΦ`. These exact signs are now stated in
the owner theorem and pass the target build. The draft's `-4VΦ` second sign
was incorrect.

### Ground-truth contract: DeWitt body/soul to Peirce parity bridge

- **Claim:** for an associative ring with `ChiralPeirceSystem`, the four
  `PL`/`PR` corner formulas in `DeWittPeirceSuperalgebra.body` and `.soul`
  coincide with `evenPart PL` and `oddPart PL` from
  `PeirceDeWittChiralSplit`; the grading elements coincide as well.
- **Carrier and conventions:** one `[Ring A]`; products retain order;
  `PR = 1 - PL` is derived from the owner field `PL + PR = 1`.
- **Source facts:** `ChiralPeirceSystem` provides idempotence, the partition
  equation and one orthogonality direction; `IdempotentProjectorAlgebra`
  defines the four Peirce corners; `PeirceDeWittChiralSplit` defines the
  grouped even/odd parts and grading.
- **Smallest gap:** no owner theorem identified these two projections and
  gradings on the same carrier.
- **Result:** `Algebra/DeWittPeirceChiralBridge.lean` now proves the derived
  complement, both projection equalities, grading equality, and a combined
  decomposition theorem; it is exported by `Algebra.lean` and kernel-checked.
- **Adjacent claims excluded:** this bridge does not construct a tensor
  product, identify the abstract ring with a matrix ring, or transfer analytic
  or physical interpretations.

The `interband_sylvester_table` in `Algebra/PeirceDeWittChiralSplit.lean` was
also checked against ordered multiplication and corrected: with
`Φ = u + v`, `J = u - v`, `V = uv + vu`, and `Σ = uv - vu`, square-zero
`u,v` imply `ΦΣ = -VJ` and `JΣ = -VΦ`. The previous `VΦ`/`VJ` right sides were
false (already for the opposite matrix units `E₁₂`, `E₂₁`). The owner now
builds with the corrected identities.

### Supplemental living-Sylvester, DeWitt–Schur, and Jordan–Wigner archetypes

The latest transcript's `SW₁–SW₅` claims map to existing operator owners; the
proofs below retain ordered multiplication in associative rings and do not
replace the operators by scalar or diagonal models.

| Archetype | Repo-owned Lean result | Precise scope |
|---|---|---|
| Living Sylvester table | `Algebra/PeirceDeWittChiralSplit.lean`: `interband_sylvester_table`. | Peirce-supported square-zero corners give the tetrad product table. The mixed products are `ΦΣ = -VJ` and `JΣ = -VΦ`. |
| DeWitt–Schur LDU | Same owner: `dewitt_peirce_LDU`, `dewitt_peirce_dual_LDU`, `dewitt_golden_transfer_LDU`. | Exact ordered Schur corrections are `N₋N₊` and `N₊N₋`; no inverse of a corner idempotent is introduced. |
| Unipotent stripping | Same owner: `dewitt_unipotent_inverse`, `dewitt_peirce_block_diagonalization`, `dewitt_golden_transfer_stripping`. | Square-zero off-diagonal Peirce blocks make the unipotent factors invertible and recover the stated Schur block. |
| Internal parity-string identity | Same owner: `jw_commutator_to_anticommutator`. | It assumes the exact sign law `n*s = -(s*n)` and derives `{n,s*x} = -s[n,x]`; the Peirce specializations follow from the grading lemmas. |
| Two-site chain closure | Same owner: `jw_two_site_chain_closure`, using the named sum-square, dressing, and metric-additivity lemmas. | A single associative ring suffices, with involutive string, square-zero site modes, string commutation at site 2, and explicit cross anticommutator hypotheses. This is the abstract internal operator theorem; it does not assert that arbitrary commuting idempotents alone supply all site relations. |

The shift-norm passage also needed correction. `Algebra/HuaBergmanZornExtensions.lean`
now proves `zorn_norm_one_sub_genPhi`, namely `(1-Φ)·conj(1-Φ)=1-V`, and
`zorn_norm_P_add_genPhi`, whose exact result is `P-J-V`. The proposed identity
`Norm(P+Φ)=P-Q₊` is false in general: its right side omits the ordered
off-diagonal terms. The existing `zorn_norm_genPhi` already supplies the
metric-shift identity `Norm(V+Φ)=V²-V`. These are Peirce quadratic products
defined by the involutive conjugation, not a claim that an associative Peirce
ring norm is the classical nonassociative split-octonion determinant.


### All-index geometric sums and Reynolds intertwiners (Stage D80 core)

The D80 operator claims have been normalized to statements in the existing `OperatorCyclotomicParafermions` owner. They are proved for arbitrary `[Ring B]`; there are no scalar phase parameters or commuting ambient assumptions.

| Extracted archetype | Kernel-checked declaration | Mathematical scope / correction |
|---|---|---|
| Finite geometric tower | `operator_geometric_sum_telescopes` | Both ordered products `(1-x) Cₙ(x)` and `Cₙ(x) (1-x)` equal `1-operatorPower n x`. The two-sided inverse follows when the `n`th power is zero. |
| Nilpotent ladder inverse | `operator_geometric_sum_inverse` | Conditional on the exact recursive power being zero; division is not used. |
| Reynolds endpoint identity | `parafermion_reynolds_raw_commutator` | The recursively ordered sum has commutator `xⁿ y-y xⁿ`; `parafermion_reynolds_commutes` gives centralizer membership when `xⁿ=1`. The weighted sum is explicitly unnormalized. |
| Clock consequence | `operator_geometric_sum_zero_implies_power`, `geometric_sum_zero_gives_clock_and_reynolds_invariance` | If `Cₙ(x)=0`, telescoping forces `xⁿ=1`; both the raw sum and its left-`x`-weighted version then commute with `x`. This is a centralizer-valued intertwiner statement, not an idempotent-projector theorem. |
| Finite divisor factorizations | `operator_geometric_sum_two`, `_three`, `_four`, `_six` | The identities at 2, 3, 4, and 6 hold with their displayed factor order. `Cₙ` means the geometric sum; it is not described as an irreducible cyclotomic polynomial in general. |
| Dyadic index doubling | `operator_geometric_sum_dyadic` | `C_(2n)(x)=(1+x)C_n(x²)` in the associative ring, proved by induction and same-operator power commutation. |
| Arbitrary translated window | `operator_geometric_sum_block`, `operator_geometric_sum_window` | The cut-and-tail law splits at any `m`; the translated window has both left and right telescoping products equal to `x^m-x^(m+n)`, preserving ordered multiplication. |
| D80 package | `stage_D80_all_index_operator_cyclotomic_core` | Packages telescoping, the raw Reynolds boundary law, low-order factorizations, and dyadic doubling. |

The slogan that the Reynolds sum is a “projector” needs qualification: these proofs establish that its image commutes with the clock when `xⁿ=1`. Idempotence of the unnormalized sum is not part of this D80 contract; normalized averaging requires an additional invertibility/normalization condition. Likewise, `Nⁿ=0` is an algebraic nilpotency condition and does not by itself encode parafermion spin, a clock-shift braid representation, or a physical Fock space. Those require explicit structure maps and hypotheses. The D80 owner target was checked with the repository locked Lake build.

The supplied D80 Lean draft also states a false fourth-root defect formula.
From `cyclo4 x = x² + 1 = 0`, one gets `x² = -1`, hence `(x²)² = 1`
and `idempotencyDefect (x²) = x⁴ - x² = 1 + 1` (equal to `2` in
integer notation), not `1`. The owner now proves this corrected consequence
as `cyclo4_root_square_and_defect`; this is a conditional ring identity and
does not assert a primitive root or a parafermion representation.

The all-index tower also now exposes `operatorPower_add` and
`operator_geometric_sum_block`: for arbitrary `m n`,
`C_(m+n)(x) = C_m(x) + x^m C_n(x)`. This is the ordered cut-and-tail law
underlying the finite telescoping argument. It asserts no scalar spin label,
Galois action, or physical parafermion structure. `parafermionReynoldsRaw_commuting`
is proved for a clock-commuting input; its integer multiplicity is an additive
consequence, not a normalized averaging projector.

The operator-phase exchange claim is now formalized in the same owner by
`operator_power_braiding`: in an associative ring, from `x*y = q*y*x` and
`x*q = q*x`, one obtains `xⁿ*y = qⁿ*y*xⁿ` for the owner's recursive power.
`finite_clock_order_forces_braiding_phase_stabilization` then proves
`xⁿ=1 → qⁿ*y=y`; `geometric_sum_forces_braiding_phase_stabilization` composes
this with the existing implication `Cₙ(x)=0 → xⁿ=1`. The phase `q` need not be
scalar or commute with `y`. These are conditional exchange theorems: they do
not construct `x`, `q`, or a parafermion representation from the nilpotent
pair, and do not identify this ring action with the distinct categorical
Sylvester phased-state representation or the concrete qutrit matrix owner.
The targeted owner build succeeds with these declarations.

The projector interpretation is now closed with
`normalized_parafermion_reynolds_fixes_centralizer`: under finite clock order,
an element commuting with the clock is fixed by the normalized Reynolds map,
provided the coefficient `c` satisfies `c * ((n+1) • 1) = 1`. Together with
`normalized_parafermion_reynolds_comp_idempotent`, this is an idempotent
retraction on the additive endomorphism carrier. It does not claim a
normalization exists in every ring; in particular, one cannot divide by the
order in arbitrary characteristic. The owner module builds successfully with
this additional theorem.

### Two-site Jordan--Wigner sum law (SW5)

The operator-metric statement from SW5 is now proved by
`InfoGeometry.Core.BosonParityString.jordan_wigner_two_site_nilpotent_metric_additivity`.
For square-zero modes `a,b` at site 1 and `c,d` at site 2, an involution `s`
that anticommutes with `a,b`, commutes with `c,d`, and explicit inter-site
commutation, the dressed total modes `a+s*c` and `b+s*d` are square-zero and
their anticommutator is exactly `(a*b+b*a) + (c*d+d*c)`. Each site's metric
remains an arbitrary element of the noncommutative ring. This formalizes the
two-site algebra independently of the concrete finite matrix/tensor Jordan--Wigner
realizations already owned elsewhere in the repository. The generic owner
passes its targeted locked Lake build.

### All-spin continuation (D81–D84): owner audit and corrections

The D81–D84 claims map to existing declarations in
`InfoGeometry.Algebra.OperatorCyclotomicParafermions`; they were not absent
from the checkout. Their canonical carriers and owner results are:

| Stage | Mathematical carrier | Existing owner result |
|---|---|---|
| D81 | Finite geometric sums of one element in an associative ring | `operator_geometric_sum_composition`, with explicit `operator_geometric_sum_triadic` and `operator_geometric_sum_hexadic` corollaries |
| D82 | Two square-zero elements and their ordered composites | `square_zero_pair_cyclotomic_candidates`; it proves the stated off-shell cyclotomic defect with no idempotent hypothesis |
| D83 | The raw Reynolds additive intertwiner and its commutator | `parafermion_reynolds_raw_commutator`, endpoint specializations, and `isotropic_tetraktys_reynolds_mode_selection` |
| D84 | Inner conjugation by `1 - x` with the finite geometric sum as inverse | `para_unipotent_conjugation_off_shell` and `para_unipotent_conjugation_is_inner_auto`; `paraUnipotentConjRingHom` packages the conjugation as a unital `RingHom` under `xⁿ=0` |

The cyclotomic vanishing consequence is now an explicit reusable theorem:
`operator_geometric_sum_zero_implies_power_eq_one` derives `operatorPower n x = 1`
from `operatorGeometricSum n x = 0` using the left telescope, and
`pow_eq_one_of_operator_geometric_sum_eq_zero` exposes the same result in
Mathlib's ordinary `x ^ n` notation. Only this implication is claimed; the
reverse direction would require extra hypotheses because `1 - x` may be a
zero divisor.

Two advertised D83 identities do not match the repository's Reynolds
definition and are not promoted as theorems. Here
`parafermionReynoldsRaw (n+1) x y` is the ordered sum with `n+1` terms
`xʲ y xⁱ`; setting `y=1` gives `(n+1) • xⁿ`, not
`1+x+…+xⁿ`. The theorem `parafermion_reynolds_raw_one` records this
correct evaluation via the existing commuting-input lemma. On `1-x`, its
value is `(n+1) • (xⁿ * (1-x))`; `parafermion_reynolds_raw_coboundary`
records that formula. The square-zero tetraktys mode theorem proves the
order-two and order-four transverse annihilations together with the
longitudinal operator-valued outputs. The commutator endpoint theorem remains
the correct general Reynolds intertwining statement.

The owner had additional source-order/proof-script defects: the early
conjugation proofs referenced later telescope results, one inverse theorem
name did not exist, and the composite-index proof had invalid rewrites. These
are repaired with private early telescope/inverse helpers and corrected
power-commutation arguments. `square_zero_pair_cyclotomic_candidates` also
now uses explicit square-zero consequences during normalization. The new
triadic and hexadic results specialize the already-proved multiplicative
composition law. `stages_D81_to_D84_operator_cyclotomic_synthesis` packages
these results in causal order, carrying the corrected Reynolds claims and
the nilpotency condition required for the inner automorphism. The targeted locked build succeeds for
`InfoGeometry.Algebra.OperatorCyclotomicParafermions`.

The D84 `RingHom` uses the ring's canonical additive and multiplicative
operations, with unit preservation discharged by the geometric-sum inverse.
The same owner build also exposed and repaired coercion elaboration in
`bruhatUnit_sixth_power_on_shell`; the unit-power statement is now explicitly
transported through `Units.ext`, while the cyclotomic-root statement is kept
on the underlying ring element.

Follow-up sign audit of the D82 Bruhat comparison: for the order-sensitive
unit `bruhat u v = (1+u)(1-v)`, the exact complement is
`1 - bruhat u v = u*v - u + v`; for the reversed unit it is
`1 - bruhatInv u v = v*u + u - v`. In particular,
`bruhat (-u) (-v) = 1 - (u*v + u - v)`. The last formula is the precise
connection between the square-zero cyclotomic candidate and the ordered
Bruhat unit. It is now proved by `bruhat_complements` in the Lean owner, with
no nilpotency or commutation assumptions. The superficially similar claim
`bruhat u v = 1 - (u*v + u - v)` has the wrong sign on the linear terms and
is not asserted.
