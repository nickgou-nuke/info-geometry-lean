# G₂ semantic audit addendum — 2026-08-26

This addendum records verified findings from the current checkout.  It does
not promote names, comments, CAS payloads, or conditional interfaces into
mathematical results.

## Direct findings

| Owner | Evidence | Classification |
|---|---|---|
| `G2FlagCellWitnessCertificate.lean` (historical; absent in current tree) | Historical `leftWitness`/`rightWitness` data-only owner; it cannot serve as current source evidence. | STALE: historical reference |
| `G2FlagCellWitnessSoundness.lean` (historical; absent in current tree) | Historical selected-row readback reference; it cannot serve as current source evidence. | STALE: historical reference |
| `G2GAPFlagWitnessReadback.lean` | Defines `gapWitnessMatrixSound` as a proposition parameter and derives group/quotient conclusions only from that parameter; its module comment explicitly says it does not assert matrix soundness for imported data. | RED: no imported-row verification |
| `G2FlagFactorizationNormalizedData.lean` | `Data.reversed` is arbitrary input and `sound` requires `hraw`, the complete desired native factorization, as an argument. It performs no orientation discovery or matrix verification. | RED: normalization is assumption-backed |
| `G2SymbolicBN2.lean` | `ReflectionBN2Spec` stores `toPC_mem_B`, `toPC_surj`, and both branch equations as fields; the resulting BN2 theorem is valid only after supplying the entire concrete interface. | ORANGE: symbolic schema, not native BN2 proof |
| `G2QuotientRepresentativeInjectivity.lean` | Its quotient-alignment theorems take complete `hfac`, cell-separation, and residual-alignment premises. They assemble these premises but do not prove the 189-row factorization or quotient injectivity. | YELLOW: explicit assembly boundary |
| `G2FlagFactorizationMatrixSoundness.lean` | `factorizationMatrixValid_of_sound` derives matrix equality from `C.sound`; it does not construct `C` or validate the imported GAP table. | YELLOW: faithful conditional readback |
| `G2NativeBruhatRootSubgroupSystem.lean` | The native system proves membership, Boolean root laws, and injectivity for the literal `xRoot`/`rootSubgroup` definitions; it explicitly leaves product normal forms and peeling out of the structure. | GREEN: honest local interface |
| `G2ResidualExponentRealizationBoundary.lean` | Defines realization as `Nonempty` of an equivalence and correctly proves the `(2,true)` counterexample and top-parameter realization. It does not generalize the false equivalence. | GREEN: corrected boundary |
| `G2NativePointStabilizerLineFiber.lean` | `nativePointStabilizer_lineFiber_surjective` and `nativePointStabilizer_lineAction_surjective` prove surjectivity of a fixed automorphism's transport map. They do not prove that the point stabilizer orbit of `lineZero` is the whole base fibre; that requires the separate three-witness theorem. | YELLOW/RED: surjectivity naming risk |
| `G2FlagFactorizationOrientation.lean` | `normalizedFactorization_of_orientation_certificate` is a conditional rewrite. `orientationCellFactorizationCertificate` requires an externally supplied `reversed` table and full `hsound`; it does not determine orientation or establish soundness. | RED: normalization wrapper, not verification |
| `G2Fin189OrbitMembershipCertificate.lean` | No such filename is present in the current checkout; the current similarly named `G2Fin189OrbitMembership.lean` is a conditional assembly theorem taking `CellFactorizationCertificate`. | STALE/RED: previously claimed artifact absent |
| `G2TwoPCMatrixCertificate.lean` | Its module header advertises the complete carrier product identity, but the displayed `pcWord_mul_eq_pcCombine` and `matrixWord_mul_matrixWord` block is inside a block comment and is inactive. | RED: header overclaims inactive theorem |
| `G2Fin189Certificate.lean` | `FlagFiber` is a canonical combinatorial sigma carrier and `flagFiberEquivFin189` is an equivalence to `Fin 189`; the file explicitly contains no quotient-orbit membership proof. | YELLOW: index census, not native quotient identification |
| `G2FiniteChevalleyGroupBridge.lean` | `FiniteAut O` is a generic automorphism of an arbitrary associative `Ring O`; `g2TwoOrder` is defined as the numeral `12096`, and its “order” theorems are arithmetic identities. No `Ring` instance or equivalence identifies this carrier with split-octonion automorphisms. | RED: named concrete group is not constructed |

### Payload coverage is not proof coverage

The current `G2GAPFlagWitnessData.lean` contains 189 explicit pattern-match
rows in each of `gapLeftWitness` and `gapRightWitness` (the remaining input
pairs use the default branch).  This establishes only that a table payload is
present.  It does not establish that any row satisfies
`gapWitnessMatrixSound`.  The only live bridge inspected here takes that
proposition as an argument, so the correct status remains:

```text
189 data rows      !=      189 kernel-proved readback rows
```

In particular, the presence of a row, its subgroup membership, and a quotient
conclusion conditional on `gapWitnessMatrixSound` are three different claims.
No full-row matrix certificate was found in the current source search.
| `G2FlagCellQuotientWitness.lean` | Concrete quotient witnesses exist for selected rows `(1,45)`, `(1,73)`, `(1,178)`, `(4,18)`, plus `hcell_one` and anchors. | YELLOW: partial coverage |
| `G2CellFactorizationCertificate.lean` | `sound` is a structure field whose type is the desired factorization theorem. | ORANGE: assumed proof authority |
| `G2FactorizationAlignmentCertificate.lean` | `base`, `step`, `separation`, `residual_alignment`, and `residual_injective` are all fields; an earlier semantic-vacuity report recorded 16 findings, including two `pure_proof_carrier` errors (that count is not treated as current evidence here). | RED: proxy/proof package |
| `G2Fin189OrbitMembership.lean` | `fin189_orbit_membership` takes `CellFactorizationCertificate` as an explicit argument. | YELLOW: conditional bridge |
| `G2ConcreteBruhatOrbitCertificate.lean` | `covering_eq_univ` requires `enum`, complete `hcell`, and `hpartition`. | YELLOW: conditional coverage |
| `G2NativeFlagStabilizerTransport.lean` | `unipotentSubgroup ≤ nativeFlagStabilizer` is proved. | GREEN: inclusion only |
| `G2NativeFlagStabilizerCardinality.lean` | Stabilizer equality requires group order, flag cardinality, and transitivity. | YELLOW: conditional equality |
| `G2NativeFlagStabilizerFullPeel.lean` | Stabilizer equality requires a full-peel hypothesis. | YELLOW: conditional equality |
| `G2NativeLineFiberDistinctness.lean` | `lineInfinity = lineOne` is proved. | RED against the earlier three-distinct-lines claim |
| `G2BruhatResidualSimpleEquiv.lean` | For `(2,true)`, the exponent carrier has cardinality 8 while the native residual has cardinality 32; no equivalence exists. | GREEN: counterexample |
| `G2SchubertCalculus.lean` | Current checkout compiles with `lake env lean`; it defines a finite convolution carrier and conditional structure-constant interfaces, not a full geometric/quantum-cohomology construction. | YELLOW: finite/conditional scope |
| `G2GroupOrderReduction.lean` | Its header says “All proofs are complete”, but the file itself states that the ambient order is reduced to the still-missing quotient-cardinality/equivalence hypothesis. | YELLOW: wording overpromotes closure |
| `G2BruhatCellDecomposition.lean` | Its “12096” theorem is a sum of abstract numerical weights; the same header explicitly says it is not a concrete cell-cardinality or coverage theorem. | GREEN for arithmetic, not Bruhat classification |
| `G2NativePointTransitivity.lean` | Point-action surjectivity is proved through `native_point_orbit_cover`; this is a 63-point result and does not imply flag transitivity. | GREEN: point scope only |
| `G2NativeIntrinsicFlagBridge.lean` | `nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189` is `Fintype.equivOfCardEq`; it is an arbitrary finite-cardinality equivalence, not an action-equivariant or geometric carrier identification. | ORANGE: cardinality proxy |
| `G2IntrinsicLineFiberTransport.lean` | `intrinsicLineMapEquiv` transports dependent fibers honestly, but no theorem makes the base fiber have three elements or makes its stabilizer action transitive. | YELLOW: transport only |
| `G2SymbolicBN2.lean` | The pointwise BN2 theorem is structurally valid, but it requires a `ReflectionBN2Spec` whose `toPC_surj`, branch equations, and memberships are supplied fields. | YELLOW: conditional BN2 interface |
| `G2BigCellPolynomialWitnesses.lean` | The “main” reductions require `h_carrier` containing the complete big-cell factorization for every active exponent. | ORANGE: CAS identity assumed |
| `G2NativeWeylRootSpaceMembership.lean` | Root-space membership requires explicit `hbracket`, `hcartan`, and `hweight` hypotheses; no real Weyl-generator normalization is proved. | YELLOW: abstract transport lemma |
| `G2NativeWeylFiniteWeightBridge.lean` | It explicitly proves `cycleWeight_not_cAction_dual`. | RED against the earlier claim of native cycle/root-weight compatibility |
| `G2TwoRealSplitClassification.lean` | Its capstone proves finrank `14`, root count `12`, and a one-parameter flow law; it does not prove the finite `G₂(2)` order, Weyl/root-space compatibility, or a full real representation identification. | GREEN for stated local facts, not the earlier global capstone narrative |
| `G2CanonicalResidualLengthOne`–`Five.lean` | The named length equivalences are built via `Fintype.equivFin` from cardinality equalities; they do not give root-product maps or native residual-subgroup equivalences. | GREEN for finite carrier arithmetic, ORANGE if read as structural normal forms |
| `G2CanonicalResidualFiberCoordinate.lean` | The owner explicitly proves `residualFiberSixBits_injective` and `residualFiberToW0Exponent_injective` only; its header says surjectivity needs a separate alignment theorem. | GREEN: injection only |
| `G2NativeRootIndexAlignment.lean` | `rootIndexOf` has proved injectivity, surjectivity, and canonical derivation readback. | GREEN: finite/native index bridge only |
| `G2NativePositiveRootSubgroupSystem.lean` | The ordered six-root product has proved membership, injectivity, and image cardinality 64; the file explicitly does not identify its image with the whole positive-root subgroup. | GREEN: image normal form only |
| `G2RootWeylAdjointCharacter.lean` | It proves a finite root-permutation fixed-point character and separate canonical derivation eigenbasis facts; it does not prove that the finite Weyl action is the real adjoint action on the 14-dimensional carrier. | YELLOW: two separate readouts |
| `G2PeirceParabolicStabilizer.lean` | Peirce-stabilizer equality and order require `h_peirce_rigidity`, `hB₀_fix`, `hs₂_fix`, and a parabolic-cardinality hypothesis; the unconditional incidence fiber count is a different finite geometry statement. | YELLOW: conditional stabilizer, separate incidence census |

## Withdrawn claims

The following earlier statements were false or materially overstated:

1. The full 189-row brute-force artifact was kernel-verified.
2. The current `leftWitness/rightWitness` tables were proved aligned with the native representative carrier.
3. A uniform exact `left · Weyl · right` factorization held for every row.
4. PR #65 supplied a structural, non-enumerative solution; its attempted row closure used finite case enumeration and failed matrix propositions.
5. Full quotient orbit membership and Bruhat coverage were closed.
6. The quotient representative was unconditionally an equivalence on `Fin 189`.
7. Stabilizer equality and transitivity were complete.
8. The native residual subgroup was generically parametrized by the Weyl-length exponent carrier.
9. The three-line base fiber supplied the proposed transitivity proof.
10. Schubert/quantum cohomology was complete as a geometric `QH^*(G₂/B)` construction.  The current file compiles, but its stated scope is a finite convolution/conditional interface, not that construction.
11. The spectral stabilization files proved global `E∞` convergence; they provide conditional interfaces with explicit hypotheses.
12. The repository had globally zero proof debt.  A lexical current-checkout inventory reports `1939` `sorry`, `258` `admit`, and `683` `axiom` occurrences; these counts include comments/tooling and therefore require semantic classification, but they disprove an unqualified zero-count claim.
13. A passing `lake env lean` invocation was treated as evidence for semantic completion.  Compilation proves only that the displayed statement follows from its imports and hypotheses; it does not prove that the statement matches the intended mathematical bridge.
14. A finite `Equiv` obtained from equal cardinalities was described as a native/geometric identification.  `Fintype.equivOfCardEq` supplies a carrier bijection only; it supplies no compatibility with actions, incidence, quotient maps, or representatives.
15. A “complete BN2” or “certified big-cell” label was treated as proof of the concrete branch identities.  The actual declarations package those identities as specification fields or hypotheses.
16. The earlier proposed `nativeRootWeight_cycle_compat` bridge was treated as available.  The current owner instead contains a concrete counterexample showing that the presently defined `cycleWeight` is not the contragredient `cAction` on the displayed labels.
17. The real-form “capstone” was described as closing the complete split-`G₂` representation.  Its actual conjunction is only dimension/root-count/flow data; the carrier and Weyl compatibility bridges remain absent.
18. The canonical length-one-through-five equivalences were described as ordered root-product constructions.  Their definitions are cardinality-induced finite bijections and contain no multiplication/readback semantics.
19. The six-bit residual-fiber map was described as a full coordinate equivalence.  The owner proves injection only and explicitly leaves surjectivity as a separate obligation.
20. The finite root fixed-point character was described as the genuine 14-dimensional adjoint Weyl character.  The current owner contains no finite-to-real adjoint compatibility theorem; its character is on finite root labels, while its 14-dimensional facts are separate canonical readouts.

## Additional owner check: `G2PCCollection` and `G2TwoPCMatrixCertificate`

`G2PCCollection.lean` compiles, but its advertised scope is stronger than
its theorem boundary.  It defines `PCExp := Fin 6 → ZMod 2` while its header
also records order-four generators (`e₁² = e₂² = e₅`).  The active theorems
are identities for the chosen `mulGen` functions; they do not prove that the
binary carrier is a unique polycyclic normal form for the concrete subgroup.
Moreover, several proofs explicitly split all six coordinates and close by
`decide`, so this owner is computational enumeration, not the structural
collection proof previously claimed.

`G2TwoPCMatrixCertificate.lean` has a direct source-level contradiction:
its module header advertises a completed concrete multiplication theorem,
but `pcWord_mul_eq_pcCombine` and `matrixWord_mul_matrixWord` occur inside a
block comment (`/- ... -/`) in the current source.  They are therefore not
exported declarations from that owner.  The active owner proves matrix
readbacks and selected entries, but not those advertised matrix-transport
declarations.  This is an owner/header mismatch, not a claim that the entire
repository lacks the multiplication law: `G2TwoPCConcreteCollector` exports
`pcWord_mul_pcWord`, and `G2TwoPCSubgroupClosure.pcWordMulEquiv` uses it.

## Additional owner check: Weyl completion and parabolic quotient

`G2WeylGroupCompletion.lean` is a genuine carrier wrapper, but its
surjectivity is inherited from `weylG2Subgroup_coverage_pair` in
`G2TwoBruhatClassification.lean`.  That imported owner explicitly states
that global carrier coverage and global Bruhat classification are not
proved.  The completion file therefore packages an upstream coverage
hypothesis; it does not independently establish the concrete twelve-element
Weyl subgroup.

`G2FlagAndParabolicQuotient.lean` proves valid generic quotient facts for
arbitrary groups and subgroup inclusions.  Its G₂-specific constants in the
header (64, 192, 189, 63, 3) are not conclusions of this file: the active
declarations contain no G₂ instantiation deriving those numbers.  Calling it
a completed G₂ parabolic quotient owner is consequently an overstatement;
its proved content is generic quotient infrastructure.

## Additional owner check: BN₂ peeling and recovery

`G2BN2InductivePeeling.lean` is structural but entirely conditional.  Its
main theorem requires, as explicit arguments, the involution law for `s`,
the simple-root Levi identity, membership of every generator in `B`, and
conjugation membership for every complementary generator.  Consequently
`peeling_factorized_bn2` proves a generic implication from a supplied BN₂
specification; it does not establish those concrete identities for the
split-octonion carrier.

`G2PCRecoveryFactorization.lean` genuinely proves the full-peel reconstruction
identity for the current `fullPeel` functions.  Its consequence
`factorization_of_fullPeel_eq_weyl`, however, still requires the hypothesis
that the residual `fullPeel f` is one of the twelve Weyl representatives.
Thus it is a valid recovery decomposition, not a proof that every carrier
element has a `U · W · U` Bruhat factorization.

## Additional owner check: current flag certificate boundary

`G2FlagFactorizationConcreteCertificate.lean` exports `verifiedRows : Fin 5 →
VerifiedRowData`, containing only five rows (`(0,0)`, `(1,24)`, `(4,6)`,
`(4,18)`, `(1,45)`).  Its `verifiedRows_sound` theorem is therefore a
five-row theorem, not a 189-row certificate.  `anchorFactorizationData_sound`
proves only the twelve anchors.

`G2CellFactorizationCertificate.lean` does not construct a certificate.  The
structure field `sound` has exactly the desired all-cell factorization as an
input.  Its `factorization_of_mem`, matrix soundness downstream, and
`G2Fin189OrbitMembership.fin189_orbit_membership` merely consume that field.
Thus those declarations are valid conditional assembly, but cannot be cited
as proof of the CAS table or of all-row alignment.

`G2Fin189Certificate.lean` proves only a finite equivalence for the canonical
flag-fiber index and its cardinality 189.  Its module comment explicitly says
it contains no quotient-orbit membership proof; it is not a concrete
`Fin 189` Bruhat certificate.

## Additional owner check: counting is not concrete group order

`G2TwoBruhatCounting.lean` proves arithmetic identities for locally defined
lists and formulas: the displayed length list sums to 189, and the formal
product evaluates to 12096.  It does not quantify over the concrete
`SplitOctF2Aut` carrier, define the twelve concrete cells, or prove that those
cells partition the carrier.  Its theorem
`g2_two_structural_order_eq_12096` therefore is a numerical identity of
definitions, not a proof that the concrete group has order 12096.  The
docstring phrase “structural order” is materially overstated.

`G2BNPair.lean` contains valid generic Tits-system consequences, but the
master `doubleCoset_eq_iff` and `unique_bruhat_cell_weyl` are parameterized by
a `TitsSystem` object whose cover, disjointness, kernel, and compatibility
properties are fields.  They do not instantiate those fields for the current
G₂ concrete carrier.  Treating these generic consequences as a completed
concrete Bruhat theorem was false.

## Additional owner check: Weyl polynomial and Chevalley-order claims

`G2TwoBruhatCounting.lean`, `G2BruhatCardinalities.lean`,
`G2CyclotomicPoincareFactorization.lean`, and
`G2FiniteChevalleyGroupBridge.lean` contain correct elementary arithmetic
identities for explicitly defined naturals, lists, and polynomials.  Their
names and docstrings promote these identities to concrete statements about
`G₂(2)`, Bruhat cells, flags, or automorphism-group order, but the active
declarations do not connect those local definitions to the concrete
`SplitOctF2Aut` carrier.  In particular, `g2two_chevalley_order_from_cyclotomic`
proves only `2^6 * P(2) = 12096`, and `g2TwoOrder_factorization` is `rfl` for
the definition `g2TwoOrder := 12096`; neither proves
`Nat.card SplitOctF2Aut = 12096`.

The same issue applies to `full_flag_coset_sum_189` and
`parabolic_coset_sum_63`: they sum hard-coded abstract length functions over
`Fin 12`/`Fin 6`, not concrete quotient-cell carriers.  These are arithmetic
targets, not certified finite geometry.

## Additional owner check: abstract dimension and adjoint packaging

`G2ClassificationBoundaryClosure.lean` names the equalities
`8 + 3 + 3 = 14` and `2 + 12 = 14` an “exact dimension decomposition of
G₂”, but both are `rfl` arithmetic over `Nat`; they do not identify any
native derivation, root, or carrier subspaces.  Its dual-map theorem is a
valid generic ring calculation, not a split-octonion derivation theorem.

`G2RootWeylAdjointCharacter.lean` does prove finite permutation facts and
imports genuine characteristic-zero derivation interfaces, but it does not
prove an equality or intertwining between the finite `G2Root` Weyl action and
the real 14-dimensional adjoint action.  The active finite character is thus
not the claimed genuine real adjoint character.

## Additional owner check: positive-root packet

`G2SteinbergPositiveRoots.lean` proves three explicit root automorphisms,
their relations, and an eight-element word image.  The exported theorem is
only `positiveRootSubgroup_card_lower_bound : 8 ≤ ...`; it does not prove
that the packet generates all six positive-root groups or that the subgroup
has order 64.

`G2NativePositiveRootSubgroupSystem.lean` is correctly scoped: it proves
membership, injectivity, and cardinality 64 for the ordered six-root-product
image, while explicitly not identifying that image with the full
`positiveRootSubgroup`.  Any earlier statement that this owner closed the
full positive-root/unipotent classification was false; the source itself
records the missing equality.

## Additional owner check: rank-one BN₂ interfaces

`G2IndexTwoRankOneBN2.lean` proves a sound generic lemma, but its conclusion
requires the index-two split, conjugation stability, Levi identity, and
coset decomposition as arguments.  It does not prove any of these premises
for the concrete G₂ carrier.  The “eliminates matrix verifications” wording
describes a reusable reduction, not a completed concrete BN₂ proof.

`G2BNBruhatFramework.lean` does prove some concrete low-level separation and
intersection facts, but its Sylow conclusion is explicitly conditional on
`Nat.card SplitOctF2Aut = 12096`.  It therefore cannot be used as an
independent source of that ambient order.

## Additional owner check: quotient injectivity and finite Chevalley labels

`G2QuotientRepresentativeInjectivity.lean` does not prove injectivity of the
concrete quotient representative.  Its theorem
`quotientRepresentative_injective_of_residual_alignment` requires both
same-cell residual injectivity and a quotient-to-common-cell alignment
theorem.  Its order theorem then takes a finished equivalence as an explicit
argument.  These are assembly interfaces, not the missing certificate.

`G2FiniteChevalleyGroupBridge.lean` defines a generic `FiniteAut O` for an
arbitrary ring and separately defines `g2TwoOrder := 12096`,
`psu33Order := 6048`, and `pgl33Order := 5616`.  The “exact” theorems are
arithmetic (`rfl`/`decide`) on those constants; no definition identifies
`FiniteAut O` with the repository's `SplitOctF2Aut`, and no carrier
cardinality or subgroup index is proved there.  Presenting this file as a
formalization of `Aut(𝕆_s(𝔽₂))` or of the PSU/PGL group structure was false.

## Additional owner check: point versus flag carrier

`G2CASNativePointAction.lean` is a genuine positive result: it checks the
exported permutations against the native point action and proves bijectivity
of the seven concrete point permutations.  Its `casPoint_pc_action` proof is
nevertheless a finite `Fin 6 × Fin 63` computational check, and its scope is
the 63-point action only.  It does not prove action on the 189 dependent
flags, flag transitivity, or an orbit equivalence.

`G2ParabolicGeometry.lean` similarly proves the incidence-table degrees and
`flags.card = 189`; its own module boundary explicitly leaves the
identification with automorphism orbits open.  The valid 63/189 table facts
were previously overpromoted to global flag geometry.

## Additional owner check: concrete Weyl cardinality

`G2TwoConcreteWeylGroup.lean` first proves that the twelve displayed Weyl
words are distinct and derives
`concreteWeylSubgroup_card_lower_bound : 12 ≤ Fintype.card concreteWeylSubgroup`.
The same file later proves the exact theorem
`concreteWeylSubgroup_card_eq_twelve`.  Thus the earlier audit wording that
this owner supplied only a lower bound, or that exact order 12 was not
justified there, is withdrawn.  The exact result is nevertheless obtained
through an explicit finite word-closure/surjectivity computation (`fin_cases`
and `decide`), not through an independent structural proof of the Weyl
presentation.  Classify this owner GREEN for the stated concrete cardinality,
with that computational provenance recorded.

## Additional owner check: symbolic BN₂ assembly

`G2SymbolicBN2.lean` and `G2SymbolicBN2Assembly.lean` prove valid generic
assembly lemmas from `ReflectionBN2Spec`/`LeviRootDecomposition`.  Those
structures contain exactly the hard premises: PC surjectivity, branch
identities, root factorization, complement invariance, rank-one Levi behavior,
and involutivity.  No concrete instance supplying these premises for the
current G₂ carrier is exported by these files.  Their “complete BN₂” wording
therefore describes the implication proved by the schema, not a concrete
BN₂ theorem.

## Additional owner check: GAP quotient bridge

`G2GAPCosetHomomorphismBridge.lean` is generic Mathlib quotient algebra.  Its
`actionHom` is constructed from a supplied enumeration
`enum : Fin n ≃ G ⧸ H`; it does not prove that a GAP permutation table equals
that action.  The intertwining theorem also requires
`h_enum : ∀ i, enum i = QuotientGroup.mk (reps i)`.  Therefore the file is a
transport lemma, not a verified GAP-to-native carrier identification.

`G2CosetActionHomomorphism.lean` is even more explicit: it is an abstract
`Fin 63` contract and declares no concrete `SplitOctF2Aut` action.  Calling
its permutation identities a concrete quotient certification was false.

## Additional owner check: projective quotient bridge

`G2ProjectiveQuotientBridge.lean` proves valid generic facts for a projective
subtype and a quotient of admissible bases.  The concrete conclusions exposed
there are `Fintype.card projectiveSplitOctF2 = 255`, faithfulness of the
projective action, a trivial stabilizer for one admissible basis (inherited
from the framework), and only `Nonempty` for the Weyl-orbit quotient.  It
does not prove a quotient equivalence, an orbit census, or a relation between
that quotient and the 189 incidence flags.  The heading “connects ... via
quotients and covering maps” was therefore broader than the active proof.

## Audit of the audit report itself

`reports/theory_audit.md` is not a reliable current-state proof ledger.  Its
current text still lists `G2SchubertCalculus.lean` at lines containing
`sorry`, while the current owner has been checked separately and contains no
such proof terms and compiles.  The report also contains many global lexical
inventories and copied docstring claims whose scope is not theorem-level.
It must therefore be treated as stale navigation evidence until regenerated
from the current checkout; it cannot certify either proof debt or completion.

### Reproducible line anchors

The principal findings can be checked directly at these current source
locations: `G2FlagFactorizationConcreteCertificate.lean:59-87` (five rows),
`G2CellFactorizationCertificate.lean:20-36` (`sound` as an input field),
`G2TwoBruhatCounting.lean:83-100` (arithmetic order identities),
`G2TwoConcreteWeylGroup.lean:153,330-359` (lower bound followed by exact
cardinality), and
`G2SymbolicBN2.lean:48-60` (BN₂ specification fields).

## Critical certificate-boundary finding: no certificate soundness is constructed

The current `G2CellFactorizationCertificate.lean:20-26` defines
`CellFactorizationCertificate` with a field
`sound : ∀ k i, i ∈ orbitCells k → ...`.  This is an arbitrary proof supplied
to the structure constructor.  Its `factorization_of_mem` theorem at lines
29-35 merely returns `C.sound`; it does not derive any row from
`leftWitness`, `rightWitness`, a matrix readback, or native algebra.

The apparent matrix verification does not repair this boundary.  In
`G2FlagFactorizationMatrixSoundness.lean:33-38`,
`factorizationMatrixValid_of_sound` proves matrix equality by rewriting with
`C.sound`.  The reverse theorem at lines 40-48 uses `autMatrix_injective`,
but only after a matrix equality has already been supplied.  Thus the owner
contains a faithful lift, not a proof-producing validation of the data.

The orientation layer has the same issue.  `G2FlagFactorizationOrientation.lean`
defines `orientationCellFactorizationCertificate` at lines 95-117 with an
`hsound` hypothesis containing the entire desired exact factorization.  Its
downstream theorems only specialize that hypothesis.  `Data.sound` and
`toCellFactorizationCertificate` in
`G2FlagFactorizationNormalizedData.lean:23-70` likewise require `hraw`, which
is the desired row equality in conditional form.  Therefore these files do
not prove normalized CAS witness correctness; they package an assumed
normalization and propagate it.

Consequently the honest status is:

```text
native matrix injectivity                         GREEN
selected row theorems already present             GREEN
certificate-data payload                          DATA ONLY
CellFactorizationCertificate construction          ASSUMPTION INPUT
normalized orientation correctness                 ASSUMPTION INPUT
189-row matrix soundness                           UNPROVED
189-row quotient/Bruhat coverage                   UNPROVED
```

Any earlier statement that the normalized certificate or its matrix
soundness was implemented and kernel-verified is false and is withdrawn.

## Fiber/transitivity bridge is not a transitivity proof

`G2NativePointStabilizerLineFiber.lean:18-22` is frequently described as
point-stabilizer transitivity on the base line fibre.  Its theorem quantifies
an arbitrary `g` together with `_hg` and returns surjectivity of
`nativeLineFiberMap g nativeBasePoint` solely by applying the surjectivity of
the underlying `Equiv`.  It does not quantify over `nativePointStabilizer`,
does not construct stabilizer witnesses, and does not prove that the
stabilizer acts transitively on the three lines.  The hypothesis `_hg` is not
used in the proof.  Therefore it cannot activate global flag transitivity.

`G2NativeIntrinsicLineFiberBridge.lean:25-41` obtains an abstract
`Fintype.equivOfCardEq` from cardinality equality.  This is a noncanonical
finite-type equivalence; it is not a native/intrinsic line-incidence map and
does not prove equivariance.  The same issue occurs in
`G2NativeIntrinsicFlagBridge.lean:27-41`: the `NativeFlag` equivalence is
constructed from the assumed 189 cardinality and has no action compatibility.
These are cardinality bridges, not geometric transport theorems.

The named-line caveat is proved rather than resolved:
`not_three_distinct_named_parabolic_lines` explicitly proves that the three
named lines are not pairwise distinct.  Hence any earlier claim that two
stabilizer witnesses automatically complete a three-line fibre is unsupported
until the actual `NativeLine` carrier and its action are identified.

## Quotient/equivalence and order theorems remain conditional assembly

`G2QuotientRepresentativeInjectivity.lean:248-285` does not construct the
quotient equivalence from the current representative table.  The definition
`quotientRepresentativeEquiv` requires both a cellwise residual-injectivity
proof (`hcell`), a quotient-alignment proof (`halign`), and independent
surjectivity (`hsurj`).  The theorem
`nat_card_splitOctF2Aut_eq_12096_of_quotientRepresentativeEquiv` then merely
passes the supplied equivalence to `ambient_order`.  Any earlier claim that
this owner proves quotient injectivity, quotient surjectivity, or the group
order is therefore an overstatement.

Similarly, `G2QuotientRepresentativeCoverage.lean:213-246` proves only the
logical equivalence between quotientRepresentative surjectivity and a group
cover, and derives a cover from an explicitly supplied right-factor theorem.
It does not supply that theorem.  `G2QuotientFlagEquiv.lean:20-35` is generic
orbit-stabilizer transport parameterized by `h_surj` and `h_stab`, not a
concrete G₂ quotient/flag equivalence.

## Correction to the claimed non-enumerative proof style

Several current finite G₂ owners use explicit finite computation.  For
example, `G2FlagWordCertificate.lean` proves partition, cell cardinalities,
and disjointness with `decide`/`native_decide` (lines 51-79), and
`G2TwoConcreteWeylGroup.lean` closes its exact twelve-element result through
finite word closure and `decide`.  These are legitimate kernel-checked
certificates, but they are enumeration/computation-based.  Earlier claims
that the corridor had been completed without brute-force or finite case
analysis were false as engineering descriptions and are withdrawn.  The
correct claim is narrower: selected calculations are kernel checked; the
global structural bridges are still conditional or absent.

## Spectral comparison boundary

`SpectralColimitComparison.lean:27-37` defines
`StabilizedTailAssociatedGradedData` with
`pageToGraded_isIso : ∀ n, IsIso (pageToGraded n)` and compatibility as
structure fields.  Its `filtration`, `exhaustive`, and `separated` fields are
not used to construct those isomorphisms.  The definition
`stabilizedTailColimitIsoAssociatedGraded` at lines 102-115 applies colimit
uniqueness after installing the already supplied `IsIso` instances.  It is a
valid consequence of assumed isomorphic legs, but it does not derive the
associated-graded identification from filtration data.

`SpectralAssociatedGradedReconstruction.lean:26-42` similarly defines
`FiltrationReconstructionData` using `hN`, `hk`, `hIncoming`, and `hOutgoing`;
it contains no filtration object, exhaustiveness field, or separatedness
field.  Its equivalence is a wrapper around the existing
`iteratedPageEquivAssociatedGraded`, conditional on those exact-couple
hypotheses.  The earlier claim that these owners prove an `E∞ ≃ gr(H)`
abutment theorem is withdrawn.

## Counting file is arithmetic, not a group-order proof

`G2TwoBruhatCounting.lean:12-100` defines a literal list of twelve lengths
and proves arithmetic identities for locally defined natural-number
expressions.  The declarations named `g2_two_structural_order_eq_12096` and
`chevalley_g2_two_order_eq_12096` do not mention `SplitOctF2Aut`, a concrete
BN-pair, a quotient, or a bijection.  Calling either theorem a proof of the
native automorphism-group order is false.

`G2GroupOrderReduction.lean:47-71` explicitly assumes quotient cardinality
189 or an equivalence with `Fin 189`; it is a reduction theorem, not that
missing quotient proof.

`G2WeylGroupCompletion.lean:15-36` is a finite-carrier wrapper, but its range
equality invokes `weylG2Subgroup_coverage_pair` from the concrete Bruhat layer.
It is not independent evidence for that coverage.

`G2FiniteChevalleyGroupBridge.lean:95-127` is even weaker than its header
claims: `g2TwoOrder` is defined literally as the numeral `12096`, and its
“order” theorems are `rfl` arithmetic about that definition.  The generic
carrier `FiniteAut O` is not identified with `SplitOctF2Aut`.  The native
counterpart `G2TwoFiniteChevalleyGroup.lean:21-27` explicitly requires
`h_enum : Fintype.card SplitOctF2Aut = 12096` and only rewrites it to the
ledger numeral.  Thus this bridge cannot certify the native finite group
order or the claimed Chevalley identification.

`G2TwoAutomorphismOrderLedger.lean` is an external GAP/Atlas numeric ledger:
`g2TwoOrder`, `g2TwoDerivedOrder`, and related quantities are literal natural
number definitions.  Its arithmetic packet proves consistency of those
numbers only; it contains no group carrier, enumeration, or isomorphism.  A
theorem importing this ledger is therefore not evidence that the native
split-octonion automorphism carrier has the ledger order.

`G2TwoPCMatrixCertificate.lean:13-22` advertises a complete matrix-product
certificate and a carrier product identity.  The declarations at
`lines 539-555` (`pcWord_mul_eq_pcCombine` and `matrixWord_mul_matrixWord`)
are inside a block comment, so they are not Lean declarations in the current
checkout.  The active file proves generator matrix readbacks and selected
matrix-entry lemmas, but not the advertised complete PC multiplication
identity.  The header claim is therefore stale/false as a description of the
compiled owner.

`G2BruhatCellDecomposition.lean:20-31` and
`G2ChevalleyPoincareCombinatorics.lean:115-136` use similarly strong Bruhat
and Chevalley language for identities involving locally defined lists,
polynomials, and formulas.  Their conclusions do not quantify over the
native `SplitOctF2Aut` carrier and do not establish disjoint concrete cells,
coverage, or a BN-pair.  These owners are GREEN for their numerical
identities, but RED as evidence for native Bruhat decomposition or group
order.  Earlier prose that promoted these arithmetic evaluations to such
geometric conclusions is withdrawn.

`G2QuotientLowerBound.lean:22-43` is correctly a lower-bound owner: its
conclusion is `12096 ≤ Nat.card SplitOctF2Aut`, conditional on a quotient
lower bound `189 ≤ Nat.card (SplitOctF2Aut ⧸ unipotentSubgroup)`.  It cannot
be promoted to equality.  Likewise, `G2BruhatCardinalities.lean:35-50`
evaluates a hand-defined `Fin 12` length function to 189; it does not prove
that these numerical cells partition the native quotient.  Earlier uses of
these results as exact native quotient/cardinality theorems were false.

## GAP permutation “homomorphism” is reconstructed, not compared with GAP

`G2GAPCosetHomomorphismBridge.lean:66-113` defines `actionHom` by
conjugating the canonical left-coset action through an assumed equivalence
`enum : Fin n ≃ G ⧸ H`.  Its intertwining theorem also assumes
`h_enum : ∀ i, enum i = QuotientGroup.mk (reps i)`.  No GAP permutation array
is imported or compared with this action, and no theorem proves equality of
the exported permutations with the native action.  This is a generic
construction from quotient data, not a verified GAP-to-native homomorphism.

`G2CosetActionHomomorphism.lean` is explicitly an abstract `Fin 63` contract;
its commutator theorem assumes the relevant permutation equalities.  It is
not concrete `SplitOctF2Aut` action verification.

## Factorization-alignment package is a proof obligation container

`G2FactorizationAlignmentCertificate.lean:28-73` stores the universal exact
factorization, predecessor recursion, cell separation, residual alignment,
and residual injectivity as fields.  The theorem `concrete_factorization` at
lines 81-87 only projects the `base`/`step` fields through the generic
recursion theorem.  No constructor in this owner derives those fields from
the current `flagRepWords` or CAS witness data.  The later
`concrete_quotientRepresentativeEquiv` and
`concrete_factorization_alignment` additionally require an independent
`hsurj`.  Therefore the package is a valid contract boundary, not a concrete
189-row factorization or quotient completion.

## Bruhat covering owner explicitly consumes the missing certificate

`G2ConcreteBruhatOrbitCertificate.lean:22-47` requires an equivalence
`enum : Fin 189 ≃ CarrierQuotient`, a cellwise witness `hcell`, and a cell
partition before it can conclude `concreteBruhatCovering = Set.univ`.
Its `quotient_card` and `ambient_order` theorems at lines 49-61 derive
cardinality only from an already supplied `enum`; they do not construct the
quotient enumeration or orbit witnesses.  Thus “the covering is closed” is
false unless all three premises are independently present in the importing
owner.

## Correction to this audit

The first two table entries above refer to historical owners that are absent
from the current working tree (`test -f` fails for both
`G2FlagCellWitnessCertificate.lean` and `G2FlagCellWitnessSoundness.lean`).
They must not be cited as current source files.  The current repository
evidence for the surviving selected-row boundary is
`G2FlagFactorizationRows.lean` and
`G2FlagFactorizationConcreteCertificate.lean`; the latter contains five
`verifiedRows`, while the quotient-witness owner contains the selected
quotient cases and anchors.  This correction supersedes the two historical
table labels; it does not turn the absent files into evidence for completion.

The earlier audit wording incorrectly called `G2SchubertCalculus.lean` a
current file with `sorry` holes.  In the present checkout it contains no
`sorry`/`admit` token and passes:

```text
lake env lean lean/InfoGeometry/Algebra/Zorn/G2SchubertCalculus.lean
```

Its remaining limitation is semantic scope (finite convolution and
conditional interfaces), not a current compile failure or proof hole.  The
global lexical counts above also include comments and audit/tooling text and
must not be read as counts of theorem-body holes.

A scoped check of the 310 local `G2*.lean` owners found seven files matching
`sorry`/`admit`, but those matches are the literal “0 sorry” wording in
docstrings, not proof terms.  The G₂ proof-hole issue is therefore semantic
conditionality and missing carrier alignment, not seven newly discovered G₂
`sorry` bodies.

## Weyl finite-weight obstruction is explicit

`G2NativeWeylFiniteWeightBridge.lean:84-95` proves an explicit
`cycleWeight_not_cAction_dual` counterexample.  Thus the currently defined
coordinate permutation `cycleWeight` is not the contragredient action of the
native `cAction` on the displayed root labels.  The requested compatibility
theorem cannot be obtained by unfolding or relabeling this definition; a new
correct action or a proved transport map is required.

`G2NativeWeylRootSpaceMembership.lean:30-75` is correctly conditional on
`hbracket`, `hcartan`, and `hweight`.  It proves root-space membership and a
nonzero scalar coefficient only after those three bridges are supplied.  It
does not prove the real Weyl generators normalize the Cartan or determine
their signs.  Earlier claims that the real Weyl/root-space transport was
already essentially closed were false.

`G2RootWeylAdjointCharacter.lean:463-476` does contain a genuine finite-root
to canonical-derivation readback and should be retained as GREEN.  It does
not state that finite `weylRootAction` agrees with conjugation by the real
characteristic-zero Weyl automorphisms, nor that the finite permutation
character is the trace of the real 14-dimensional adjoint action.  The
dimension/eigenbasis declarations later in that file establish the canonical
14-dimensional decomposition independently; they do not supply the missing
Weyl-action intertwiner.  A completed genuine 14-dimensional adjoint
character therefore remains unproved.

## Root-subgroup naming boundary

`G2RootSubgroup.rootSubgroup` is not a subgroup constructed from a general
root-subgroup law.  Its carrier is definitionally the two-element set
`{1, rootAut α}` (`G2RootSubgroup.lean:15-33`).  Therefore
`rootSubgroupEquivBool`, `rootSubgroup_card`, and the additive/inverse lemmas
are valid for that explicitly defined two-point subgroup, but they do not by
themselves identify it with a Chevalley root subgroup of the intended finite
group.

The honest status is:

```text
two-point native subgroup generated by one involution: proved
identification with the intended Chevalley root subgroup: unproved
```

This cannot be used as evidence that an arbitrary `residualSubgroup` is a
product of root subgroups.  Separately, `G2BruhatResidualRoots` uses a closure
of six concrete positive-root packets for `positiveRootSubgroup`; its equality
with `pcSubgroup` is conditional on an explicit generator correspondence.

## Point-stabilizer line-fiber naming boundary

`G2NativePointStabilizerLineFiber.nativePointStabilizer_lineFiber_surjective`
does not prove that the point stabilizer acts transitively on the three lines.
Its hypothesis is named `_hg` and is unused; the conclusion is the
surjectivity of an already supplied `Equiv` (`...LineFiber.lean:18-22`).
Thus it is a carrier-level equivalence/readback lemma, not the missing
base-fiber orbit theorem.  The latter remains an actual obligation before
`intrinsicFlag_orbit_surjective` can be promoted.

## Cardinality-induced equivalence boundary

Several objects named `...Equiv` are not constructed from the mathematical
maps suggested by their names.  For example,
`G2CanonicalResidualLengthOne`--`Five` build equivalences through
`Fintype.equivFin` and `finCongr` after proving equal cardinalities
(`G2CanonicalResidualLengthFour.lean:8-15` is representative).  Likewise,
`G2NativeIntrinsicFlagBridge` uses `Fintype.equivOfCardEq`, and
`G2HexagonIncidence.parabolicFlagEnum` uses `Fintype.equivFinOfCardEq`.

These are valid noncomputable finite-type equivalences, but they do not prove
coordinate readback, incidence preservation, equivariance, or compatibility
with a native quotient/action.  The previous narrative that treated them as
canonical geometric identifications was false.  Their honest classification is
finite-cardinality bridge only, unless a separate map-compatibility theorem is
present.

## Quotient/order circularity boundary

The quotient/order owners are valid reductions, but they do not supply the
missing numerical theorem.  In particular,
`G2GroupOrderReduction.nat_card_eq_of_quotient_189` derives
`Nat.card SplitOctF2Aut = 12096` from the quotient-cardinality hypothesis, and
`G2TitsRepresentativeInjectivity.quotientRepresentative_surjective_of_ambient_order`
derives quotient-table surjectivity from that ambient-order equality.  Using
both in the same closure argument without an independently proved quotient
equivalence is circular.

Likewise, `G2ConcreteBruhatOrbitCertificate.ambient_order` requires an
explicit `Fin 189 ≃ CarrierQuotient`; it is not an independent proof of the
equivalence.  The honest status is reduction/interface, not closure of the
`189 → 12096` chain.

## Finite-Chevalley and BN₂ naming boundary

`G2FiniteChevalleyGroupBridge` does not define the finite split-octonion
automorphism group or prove an isomorphism to it.  It defines an independent
generic `FiniteAut O` carrier and assigns the numerals `g2TwoOrder := 12096`,
`psu33Order := 6048`, and `pgl33Order := 5616`; the displayed theorems are
arithmetic identities (`...Bridge.lean:94-127`).  Calling this an exact order
theorem for `SplitOctF2Aut` was false.

Similarly, `G2BNPair.TitsSystem` and `G2SymbolicBN2.LeviRootDecomposition`
package the BN/Tits premises as structure fields.  Their generic conclusions
are valid once those fields are supplied, but no concrete `G₂(2)` instance is
constructed there.  The symbolic BN₂ theorem therefore cannot be cited as a
proof that the native Borel and Weyl generators satisfy BN₂.

## Formal-weight arithmetic is not native cell counting

`G2TwoBruhatClassification.flagVarietyCosetCount_eq_189` and
`bruhatCellWeights_sum_eq_12096` are `rfl` identities for hand-defined lists
(`inversionSubgroupSizes` and `formalCellWeights`,
`G2TwoBruhatClassification.lean:65-102`).  The same owner explicitly states
that global coverage, disjointness, and ambient order are not proved.
Therefore the numbers `189` and `12096` in these declarations are formal
combinatorial targets, not cardinalities of the native quotient or of
`SplitOctF2Aut`.

The native cell definitions exist, but the bridge from those list entries to
all native cells remains an unproved theorem.  Calling the list sum a Bruhat
classification was therefore an overclaim.

## CAS generating-system provenance boundary

`G2CoxeterGeneratingEquality` proves an equality between two subgroups that
are both defined in Lean: `casSubgroup` is generated by the locally defined
`casS1` and `casS2`, while `concreteWeylSubgroup` is generated by native Lean
automorphisms.  The relations are checked internally, including finite
evaluation of the maps.  No GAP-generated permutation/group object is
imported or compared in this owner.  Therefore `cas_lean_generating_equality`
is a genuine native subgroup equality, but the phrase “CAS generating system”
does not constitute an external CAS-to-Lean validation.  Earlier claims that
this file independently certified a GAP correspondence were unsupported.

## Dimension-partition naming boundary

`G2ClassificationBoundaryClosure.g2_trifactor_dimension_partition` and
`g2_cartan_root_dimension_partition` are numeral equalities (`rfl`), not
dimension theorems about a Lie algebra, derivation carrier, or representation.
The same file's `Dual` construction is generic over an arbitrary `Ring A`.
Thus the statements are harmless arithmetic scaffolding, but the earlier
description of them as an exact `G₂` dimension decomposition was unsupported
until an actual finite-dimensional carrier and equivalence are supplied.

## Peirce-parabolic completion claim is conditional

`G2PeirceParabolicStabilizer.lean` advertises “all proofs are complete” and
labels `peirceStabilizer_eq_parabolicSubgroup` and `peirceStabilizer_card` as
main theorems.  Their exact statements require the premises
`h_peirce_rigidity`, `hB₀_fix`, `hs₂_fix`, and, for the cardinality result,
`h_parabolic_card` (`...Stabilizer.lean:101-127`).  The file proves generic
assembly from those premises; it does not prove those premises for the native
split-octonion carrier.  The headline “completed parabolic stabilizer” was
therefore an overclaim.

## Flag-carrier separation boundary

The repository has several distinct flag carriers: `NativeFlag` is a sigma of
`NativeLinesThroughPoint`, `GlobalFlag` is a subtype of the exported incidence
table, and `IntrinsicFlag` is a sigma of `IntrinsicLine`.  Their owners
explicitly keep them separate (`G2NativeFullFlagCarrier.lean:5-10`,
`G2GlobalFlagCarrier.lean:4-9`, and `G2IntrinsicFlagAction.lean:4-12`).
`IntrinsicFlag` has a native action, while `GlobalFlag` has the table
cardinality; no incidence-preserving, action-equivariant equivalence between
these carriers is supplied.  Therefore “189 flags” on one carrier cannot be
used as transitivity or quotient evidence on another.

## PC normal-form documentation contradiction

`G2PCCollection.lean` records generator orders `(2,4,4,2,2,2)` and the
relations `e₁² = e₂² = e₅` in its header, but its `IsSortedPC` documentation
describes the absence of repetitions as following from `eᵢ² = 1`
(`...PCCollection.lean:47-58`).  That explanation is false for the two
order-four generators.  A two-valued exponent carrier can still be valid if
the collection law explicitly absorbs the square into `e₅`, but the current
comment must not be cited as a proof that the six generators are involutions
or that the normal form is the naive square-free word basis.

## Advertised matrix-certificate API is commented out

`G2TwoPCMatrixCertificate.lean` labels `pcWord_mul_eq_pcCombine` and
`matrixWord_mul_matrixWord` as its main theorem/corollary, but the entire
declaration block is enclosed in `/- ... -/` (`...MatrixCertificate.lean:535-558`).
Those names are therefore not exported by that owner.  The actual
`pcWord_mul_pcWord` theorem is owned by `G2TwoPCConcreteCollector.lean:1461`.
This is not a mathematical failure of the latter theorem, but it invalidates
claims that the matrix-certificate file itself supplied the multiplication
bridge.

## Duplicate PC-coordinate carriers

The repository contains two distinct six-coordinate carriers:
`G2PCCollection.PCExp := Fin 6 → ZMod 2` and
`G2TwoPCNormalForm.PCExponent := Fin 6 → Bool`.  `G2PCCommutators` imports
the former, while the native subgroup/isomorphism owners use the latter.
Although they have the same finite cardinality, no operation-preserving
equivalence between these carriers is established in the inspected owners.
Therefore the older collection/commutator layer cannot be treated as the same
native PC normal-form API without a proved conversion preserving
`pcCombine` and word interpretation.

## Killing-form owner is a fabricated Gram matrix, not a derived Killing form

`G2KillingCartanMatrix.lean` documents `killingMatrix` as
`Tr(ad_X ∘ ad_Y) = 4 • Tr(Xᵀ * Y)`, but the definition at
`...KillingCartanMatrix.lean:157-162` is simply a hand-built block-diagonal
matrix whose blocks are `[[4,-2],[-2,4]]`.  No `ad` representation, trace
calculation, Lie basis, or equality to the Killing form is defined in that
owner.  The proved theorem is only nondegeneracy of this explicit matrix.
Consequently the earlier claim of a proved nondegenerate `𝔤₂` Killing form is
unsupported.  It is additionally suspect as a model for split `𝔤₂(2)`, whose
real form is not established by this positive-definite block calculation.

## Current certified boundary

```text
selected native rows and quotient witnesses       proved
189-row witness payload                            data only
all-row carrier alignment                          unproved
complete hcell                                     unproved
quotient equivalence                               conditional
Bruhat covering                                   conditional
stabilizer equality                               conditional
global Schubert/quantum theory                    unproved
global spectral convergence                       conditional
```

## Current audit conclusion

The corridor is not one completed proof with isolated missing lemmas.  It is
a collection of native calculations, finite exported data, generic theorem
schemas, and conditional assembly interfaces.  The repeatedly overstated
claims were caused by promoting one layer to the next without proving the
carrier-alignment square.

The strongest presently verified boundaries are: native PC-word recovery and
injectivity/cardinality 64; selected flag rows and quotient witnesses; the
63-point native action; incidence-table cardinality 189; concrete root-index
bookkeeping; and the explicitly scoped generic quotient/BN₂/recovery lemmas.
The unproved boundaries remain: all-row flag/certificate soundness, quotient
surjectivity/equivalence, concrete Bruhat coverage, ambient group order,
stabilizer equality/transitivity, finite-to-real Weyl/adjoint intertwining,
full positive-root subgroup equality, and global spectral/quantum conclusions.

Accordingly, no current file justifies the earlier headline that the G₂
Bruhat corridor, the 12096 group order, or the genuine 14-dimensional
adjoint character was finished.  Those statements are withdrawn unless and
until their named carrier-level bridges are proved.

This document is an audit record, not a proof owner.  No theorem is promoted
by this file.

## External literature and public-repository search gate

Requested scope: open-access literature on split octonions and the split real
form (G_{2(2)}), plus public GitHub/GitLab material specifically matching
those subjects.  On 2026-08-26 the required browser channel was unavailable:
`browser-harness --doctor` reported no running Chrome, no daemon, and zero
active browser connections.  Therefore no internet search result is recorded
as inspected evidence, and no claim of an exhaustive arXiv, journal, GitHub,
or GitLab search is made.

The only public-repository check performed in this session was the permitted
Git remote probe for `https://github.com/GPWilmot/geoalg.git`; it resolved
`main` to commit `642992d43f16ce291ca56595b99bd6e6b12b0fc2`.  This is commit
identity evidence only, not source-content evidence.  A source audit requires
the browser channel or an explicitly authorized clone/fetch workflow.

Local repository evidence is not external literature.  The local tree contains
split-octonion/Zorn and (G_2) owners, GAP/Sage scripts, and the finite/native
carrier distinctions documented above.  These files cannot be cited as
independent mathematical precedent, and external papers cannot certify their
Lean carrier alignments, witness soundness, or theorem hypotheses.

Status of the requested external-search task: **blocked at the browser access
gate; no literature or GitHub/GitLab conclusions promoted**.

## Fresh local audit: newly staged certificate owners are not proofs

The current worktree contains several staged files which must not be described
as constructive certificate derivations.  In
`G2CellFactorizationCertificate.lean`, `CellFactorizationCertificate` has a
field

```lean
sound : ∀ k i, i ∈ orbitCells k →
  flagRepresentative i = collect (...) * weylNF (...) * collect (...)
```

The exported theorem `factorization_of_mem` merely projects this field.  The
file does not construct or verify the field from `leftWitness`/
`rightWitness`, so it is an assumption-bearing interface, not certificate
soundness.

`G2FlagFactorizationNormalizedData.lean` has the same issue under another
name.  Its theorem `sound` requires `hraw`, where `hraw` is already the full
desired row factorization (with an orientation bit).  The definitions
`toCellFactorizationCertificate` and `factorization_of_data` only transport
that hypothesis.  They do not derive orientation or matrix equality.

`G2Fin189OrbitMembership.lean` is consequently conditional: every result takes
an arbitrary `CellFactorizationCertificate C` and calls `C.sound`; it supplies
no 189-row witness proof.  Its covering theorem additionally requires an
external enumeration equality `henum`.

`G2FlagFactorizationConcreteCertificate.lean` proves exactly five rows plus
anchors.  The `verifiedRows` domain is `Fin 5`, and row `(4,18)` is explicitly
swapped before applying the pre-existing `row_4_18`.  This is honest partial
evidence, but it is not a normalized 189-row payload or a global soundness
theorem.

`G2FlagFactorizationAlignmentCertificate.lean` is stronger only in its
interface, not in its evidence: `base`, `step`, `separation`,
`residual_alignment`, and `residual_injective` are all structure fields.  Its
global conclusions are projections/assemblies from those supplied fields.

Therefore the current classification of these staged owners is:

```text
G2CellFactorizationCertificate             ORANGE: soundness hypothesis field
G2FlagFactorizationNormalizedData          ORANGE: hraw is desired conclusion
G2Fin189OrbitMembership                    YELLOW: conditional assembly only
G2FlagFactorizationConcreteCertificate     GREEN: five rows/anchors only
G2FlagFactorizationNormalizedRows          GREEN: five normalized rows only
G2FlagFactorizationAlignmentCertificate    ORANGE: multiple supplied obligations
```

No claim of internally derived 189-row certificate soundness is justified by
the current worktree.  This finding supersedes any earlier statement that
those files had closed the full certificate bridge.

The same gate was then run over the G₂ certificate and bridge glob.  It
reported 58 findings: 2 errors and 56 warnings.  The errors are the two
proof-only alignment carriers; the warnings include 15 proof-like structure
fields, 3 projection re-exports, and 35 trivial-surface declarations.  These
warnings are not themselves mathematical refutations, but their reported
locations are an objective index of where advertised “certificate” and
“bridge” names require source-level review.

## Fresh local audit: transported action is not the natural basis action

`G2BNBruhatFramework.lean` advertises an “admissible 7-basis torsor” and proves
`admissibleBasis7_isPretransitive`.  The `MulAction` used by that theorem is
defined in the framework by transport through
`admissibleBasis7Equiv`:

```lean
smul g v := admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm v)
```

Thus pretransitivity is a formal consequence of the regular left action on
`SplitOctF2Aut`; it is not a proof that the native pointwise action of an
automorphism on the seven basis vectors is transitive on admissible bases.
The same repository defines a separate `admissibleBasis7Action` by pointwise
application, but the inspected framework does not prove that this natural
action equals the transported action.  Therefore the torsor/pretransitivity
language is an overclaim for the intended geometric action.  The valid result
is only: the *transported* action is pretransitive.

This matters because any order or orbit conclusion transferred through the
transported action cannot be used as evidence for native flag transitivity
without the missing equivariance square.

## Fresh local audit: cardinality equivalence is not carrier alignment

`G2NativeIntrinsicFlagBridge.lean` defines
`nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189` using
`Fintype.equivOfCardEq`.  Its only input is the numerical hypothesis that the
intrinsic sigma carrier has cardinality 189.  This constructs a noncanonical
finite-type equivalence; it does not identify `NativeFlag` with the intrinsic
flag sigma, preserve incidence, preserve the group action, or map the base
flag to the base flag.  The corresponding surjectivity theorem is therefore
only surjectivity of that arbitrary cardinality equivalence.

`G2NativeIntrinsicLineFiberBridge.lean` has the analogous boundary.  It uses
`Fintype.equivOfCardEq` after proving both carriers have cardinality 3.  It
does not construct a native-line/incidence-line map or prove equivariance.
Moreover its own imported finding
`not_three_distinct_named_parabolic_lines` rules out treating the three named
parabolic lines as three distinct witnesses.  Hence these files cannot activate
native flag transitivity or stabilizer equality.

Classification:

```text
nativeFlagCardinalityEquivIntrinsicFlagSigmaOfCard189  ORANGE
nativeLineCardinalityEquivBaseIntrinsicLine            ORANGE
```

The valid content is numerical finite-cardinality transport only; the missing
content is an explicit structure-preserving equivalence.

## Fresh local audit: `flagCells` partition is not Bruhat coverage

`G2FlagOrbitPartitionCertificate.lean` defines

```lean
orbitCells := flagCells
orbitEnum := quotientRepresentative
```

and proves partition, cardinality, and disjointness facts for the finite
index sets `flagCells`.  Those facts establish only a partition of `Fin 189`.
They do not prove that `flagCells k` is the inverse image of a native quotient
Bruhat cell, that `orbitEnum` is injective or surjective, or that the action
maps the base representative into the claimed cell.  The anchor theorem is
also checked by finite matrix reduction only for the twelve selected anchors.

Consequently `orbitCells_partition` must not be promoted to concrete Bruhat
coverage.  The missing bridge remains a carrier-level theorem relating the
index partition and the native quotient/action.

Classification: `orbitCells_partition`, `flagCells_card`, and
`flagCells_pairwise_disjoint` are **GREEN as finite-index facts**, but any use
of them as native orbit/Bruhat classification is **ORANGE**.

## Fresh local audit: `12096` is arithmetic, not the native group order

The files `G2TwoBruhatCounting.lean`, `G2BruhatCellDecomposition.lean`, and
`G2CyclotomicPoincareFactorization.lean` prove numerical identities for
hand-defined length lists, Poincare polynomials, and order formulas.  For
example, `g2_two_structural_order_eq_12096` has conclusion

```lean
borelOrder 2 * poincarePolynomialG2 2 = 12096
```

and does not mention `SplitOctF2Aut`.  Likewise
`bruhatCellSizes_sum_eq_12096` sums a constructed list.  These are valid
arithmetic statements, not a derivation of
`Nat.card SplitOctF2Aut = 12096`.

The native order statements inspected elsewhere require the premise
`h_enum : Fintype.card SplitOctF2Aut = 12096`, or derive only the lower bound
`12096 ≤ Nat.card SplitOctF2Aut`.  The missing upper bound/equality is still
the native carrier classification.  Any headline asserting that the order
was proved from the arithmetic Bruhat polynomial is therefore false.

Classification: polynomial/order-formula identities **GREEN**; native
automorphism-group order **UNPROVED/ORANGE**.

## Fresh local audit: the concrete Weyl proof is finite enumeration

`G2TwoConcreteWeylGroup.lean` does prove an exact cardinality 12 for its
concrete Weyl subgroup, but the proof is not a structural Coxeter/Bruhat
classification.  `concreteWeylElement_injective` splits both `Fin 12`
indices; multiplication and inverse closure split all index pairs; and the
resulting equalities are discharged by `decide` on the finite octonion
carrier.  This is legitimate kernel-checked finite computation, but it must
be reported as enumeration, not as a non-enumerative Weyl proof.  It also
concerns the selected native subgroup generated by listed representatives; no
independent abstract-⁠to⁠native Weyl equivalence is established there.

## Fresh local audit: “root subgroup” is a two-point definition

`G2RootSubgroup.lean` defines `rootSubgroup α` by the carrier

```lean
{g | g = 1 ∨ g = rootAut α}
```

and proves its Boolean parametrization.  This is a valid two-element subgroup
for the defined `rootAut`, but the inspected code does not identify it with a
root subgroup constructed from a Chevalley group scheme, the standard
split-octonion (G_2) root datum, or a native root space.  The later native
root-system files inherit this definition and prove parameter transport and
ordered-product image facts, while explicitly not proving equality of the
ordered image with the full positive-root subgroup.

Thus phrases such as “Chevalley root subgroup” or “the positive-root
unipotent radical” are not justified by these declarations alone.  The valid
status is a finite, explicitly defined subgroup system with selected
conjugation/additivity lemmas; the standard mathematical identification is
missing.

## Fresh local audit: project-level completion documents contradict owner files

`COMPLETION_STATUS.md` declares “ALL STEPS COMPLETE”, a closed theoretical
loop, and a rigorously verified derivation.  Its own table also reports Lean
completion percentages below 100% and pending Macaulay2/formalization work.
More importantly, the G₂ owner files inspected above explicitly state that
the 12096 enumeration, native carrier identification, and several geometric
bridges remain open.  The completion document therefore cannot be used as
verification evidence; it is a stale/promotional status document and should be
marked non-authoritative or corrected.

`CAPSTONE.md` similarly claims a “fully closed, kernel-checked” pipeline and
zero proof debt, while the current repository contains conditional owners and
the audit ledger records unresolved semantic bridges.  Even if a repository
wide build or `sorry` count were zero, those claims would not establish the
missing native identifications.  These documents are **RED as completion
claims**, though some individual mathematical statements inside them may be
useful as informal roadmap text.

## Fresh local audit: baseline versus staged worktree

At the time of this pass, `HEAD` is `b2564caa6` while the worktree contains
36 staged/added or modified files and additional untracked files.  The staged
set includes new certificate, stabilizer, flag, root, and exceptional owners;
it is not the committed baseline and has not been established as a coherent
build or remote state.  In particular, the presence of a staged owner is not
evidence that its declarations are published, compiled in the active target,
or semantically validated.

The current worktree also has unrelated/independent modifications to
`reports/theory_audit.md`; this audit does not inspect or overwrite that file.
Any status statement must therefore distinguish:

```text
HEAD/remote baseline        committed provenance
staged additions             local proposed changes
untracked additions          local, unreviewed changes
```

Earlier messages that described staged branches or owners as “live remote” or
“kernel-verified” without a recorded successful command against the exact
current checkout were provenance overclaims.  The audit treats those claims as
unverified until source, toolchain, command output, and commit identity all
match.

## Fresh local audit: CAS “complete proof” is not a Lean proof

The scripts `verify_g2_bn_bruhat_complete.py`, `verify_concrete_bn_bruhat.py`,
and `verify_g2_root_bruhat_cas.py` print “COMPLETE CAS PROOF” after constructing
finite Python/NumPy sets and checking assertions.  They enumerate the 64
Boolean products, 12 Weyl matrices, and the double-coset products.  This is
useful independent computational evidence, but it is not a proof term checked
by the Lean kernel and it does not establish that the Python matrices,
exported rows, and Lean `SplitOctF2Aut` representatives are definitionally or
equivariantly the same carrier.  The scripts therefore cannot discharge the
missing Lean certificate, quotient, or native order theorems.

Classification: **external computational evidence only**; the phrase
“complete proof” is a misleading promotion when used for the Lean corridor.

## Fresh local audit: OctonionsAndG2.nb is compact, not split (G_2)

Source inspected: `/home/goutev/Downloads/collection_for_formalization/OctonionsAndG2.nb` (47,591 bytes, 1,595 lines; Mathematica 4.0 notebook).  This is an external computational notebook, not a Lean owner and not a kernel proof.

The carrier is the ordinary real octonion multiplication table.  It declares `e0` as the unit, `e1,...,e7` as imaginary basis elements, every imaginary square as `-e0`, and the displayed products have coefficients/signs such as `e1 ∘ e2 = e3`, `e2 ∘ e3 = e1`, and `e6 ∘ e7 = -e1`.  No split signature, split norm, Zorn multiplication, or characteristic-two carrier occurs in the inspected definitions.

The notebook explicitly identifies the homogeneous space as (S^6 = G_2/SU(3)) and decomposes the compact Lie algebra as (mathfrak g_2=mathfrak{su}(3)oplusmathfrak m), with dimensions 8 and 6.  Therefore it is evidence about the compact real form (G_2), not about the split real form (G_{2(2)}), and not about the finite group (G_2(2)).

Its derivation formula is the standard pair-generated expression
`Der[x,y][a] := Kom[Kom[x,y],a] - 3 ((x∘y)∘a - x∘(y∘a))`.  The notebook tests the Leibniz identity on the finite basis using Mathematica `Outer`, `Simplify`, and Boolean outputs.  It then uses `NullSpace` and flattened 7-by-7 matrices to find 14 independent derivations and prints commutator relations.  These are computational checks/results, not formal proofs, and they do not establish a Lean equivalence with the repository's Zorn or canonical derivation carriers.

The notebook's 14-dimensional derivation calculation is mathematically relevant as a compact-octonion reference, but it cannot certify any of the following repository claims: split-octonion multiplication, (G_{2(2)}) automorphism structure, finite (G_2(2)) order, native `SplitOctF2Aut`, Weyl/Bruhat carriers, or real split Weyl root-space transport.  A theorem importing this notebook would require an explicit carrier map preserving multiplication, derivations, and the relevant real form; no such map is present in the notebook.

The notebook itself warns that its programming style is not exemplary and presents a Mathematica-aided research workflow.  Accordingly the correct classification is `EXTERNAL COMPUTATIONAL REFERENCE / COMPACT CARRIER`, not Lean-certified evidence.  Its only listed reference is a Baez octonion webpage; it does not contain an arXiv or journal literature survey.

This closes the provenance question for this source: it does not explain or validate the repository's split-(G_2) certificate data, and it cannot be used to repair `leftWitness/rightWitness` or any Bruhat certificate without a new, explicit split-carrier derivation.

## Fresh local audit: staged alignment certificate is an assumption package

Current staged source `G2FactorizationAlignmentCertificate.lean` defines `FactorizationAlignmentCertificate` with fields named `base`, `step`, `separation`, `residual_alignment`, and `residual_injective`. Their types are already the desired concrete factorization, predecessor recursion, cell separation, residual alignment, and quotient injectivity statements. `ConcreteFactorizationAlignmentCertificate` repeats the same obligations with a different step type.

The exported theorems `generic_factorization` and `concrete_factorization` invoke `flagRepresentative_factorization_of_predecessor_certificate` on `C.base` and `C.step`; they do not derive either field. Likewise `generic_alignment` consumes `C.separation` and `C.residual_alignment`, and `concrete_quotientRepresentative_injective` consumes `C.residual_injective`. `toGeneric` merely repackages the supplied fields.

Therefore a term of either certificate structure is a proof of the missing bridges supplied by the caller, not a certificate-data object from which those bridges are internally constructed. The downstream theorem `concrete_factorization_alignment` is conditional on such a term and on `hsurj`; it does not establish factorization, alignment, injectivity, or surjectivity. Classification: `ORANGE` as a conditional interface; `RED` if documented or reported as an internally derived concrete 189-row certificate.

## Fresh local audit: completion documents contradict the formal owners

`COMPLETION_STATUS.md:4` says `ALL STEPS COMPLETE (Architecture Fully Verified)`, while the same document reports Lean as only `80% complete`, leaves Macaulay2 work pending, and claims a closed first-principles split-octonion/TKK derivation. This is not a status report supported by the current G₂ owner graph.

`CAPSTONE.md:3-9` claims a fully closed, kernel-checked pipeline and `0` proof debt across the repository. The current owner audit contradicts that claim: multiple G₂ theorems are conditional on supplied premises, the concrete 189-row factorization is absent, and the semantic-vacuity gate has findings. The headline must therefore be classified `RED`; it cannot be used as evidence against the owner-level audit.

`G2FiniteChevalleyGroupBridge.lean:122-135` defines `g2TwoOrder := 12096` and proves factorization of that definition by `rfl`. Those declarations do not prove `Nat.card SplitOctF2Aut = 12096`. `G2BruhatCellDecomposition.lean` explicitly documents that its 12096 sum is an abstract numerical weight, not a concrete cell-cardinality or coverage theorem. Treating either as the native finite-group order is a semantic overclaim.

## Audit correction: finite order ledger owners are honestly conditional

`G2TwoAutomorphismOrderLedger.lean` explicitly labels its numerals as GAP/Atlas order data and states that it does not construct a carrier or prove an isomorphism/classification theorem. `G2TwoFiniteChevalleyGroup.lean` likewise states that the native `SplitOctF2Aut` cardinality remains a separate enumeration theorem and proves only a theorem conditional on `h_enum : Fintype.card SplitOctF2Aut = 12096`. These are `GREEN` as ledger/conditional interfaces. The overclaim occurs only when summaries erase `h_enum` or treat the ledger numeral as a native cardinality proof.

## Fresh local audit: quadratic compatibility is not split-octonion compatibility

`G2QuadraticCompatibility.lean` calls its carrier a “Non-Degenerate Split Quadratic Form” and defines `bilinearForm u v` as the seven-coordinate sum `Σ uᵢ vᵢ`, with `quadForm x = Σ xᵢ²`, over an arbitrary `[CommRing R]`. Its nondegeneracy lemma is only the coordinate test against `basisVec`; it does not establish a split composition norm, a Zorn multiplication, or an isometry to the repository's split-octonion carrier.

The file separately defines an ad hoc Fano `crossProd` and `dicksonTrilinear` by coordinate formulas. `IsG2Automorphism` is merely the conjunction of preservation predicates for those two definitions. The theorems `g2_preserves_quadratic` and `g2_crossProd_equivariant` are valid conditional consequences for an arbitrary function satisfying that predicate and having a supplied left-inverse; they do not identify the predicate with `SplitOctF2Aut`, prove a native automorphism action, or prove the finite group order. Calling this a concrete (G_2(2)) compatibility theorem without the missing carrier map is a semantic overclaim.

This owner must be classified `ORANGE`: useful coordinate identities, but no split-octonion/G₂ carrier bridge.

## Fresh local audit: Fano/Hamming action is a separate formula, not native action

`G2FanoHammingBridge.lean` labels `g2UnipotentAction` as a “Non-Abelian G₂(2) Unipotent Action”, but the definition is an explicit triangular Boolean/XOR formula on `BinaryVector7`. The file proves zero-action, last-coordinate preservation, additivity, and Hamming/Fano identities. It does not define a map from `PCExponent` or `pcWord` into `SplitOctF2Aut`, prove that the formula is induced by native automorphism composition, or prove preservation of the split-Zorn multiplication/incidence structure. Consequently the non-abelian/native (G_2(2)) interpretation is unproved; the formal content is a separate Boolean linear-action model.

## Fresh local audit: native counterexamples invalidate proposed shortcuts

`G2CrossProductCarrierAudit.lean` contains a kernel-checked counterexample
`octCross_pc1_not_equivariant`: the older coordinate operation `octCross` is
not equivariant under the native generator `pc1Aut` on the displayed test
points. This is a positive obstruction, not an absent proof. Therefore the
older cross-product carrier cannot be used as the native 63-point incidence
or flag-action carrier.

Independently, `G2RootAutPC3Conjugation.lean` proves
`not_c_conj_pc3Aut_eq_pc1Aut` by a matrix-entry contradiction. Any narrative
that treats this proposed conjugation relation as an available Weyl-generator
identity is directly false for the current native matrices.

`G2RootSubgroupConjugation.lean` proves a genuine conjugation equivalence only
for the locally defined subgroup `rootSubgroup α = {1, rootAut α}`. The
definition is a two-element subgroup and is not identified with a generated
Chevalley root subgroup or with a residual intersection. Thus the displayed
conjugation identity is valid for this small native definition, but its header's
“canonical Chevalley relation” wording must not be promoted to a full
root-subgroup system theorem.

## Fresh local audit: cardinality headers overstate concrete geometry

`G2BruhatCardinalities.lean` uses the label “Exact Cardinalities of Bruhat and Schubert Cells for G₂(2)” and its comments call `full_flag_coset_sum_189` a full flag-variety/coset conclusion. The declarations shown in the file are sums of a hand-defined `bruhatCellSize` over `Fin 12`; they do not quantify over subsets of `SplitOctF2Aut`, prove a cell partition, or identify the quotient with a native flag carrier. The numerical identities are valid at their stated arithmetic level, but the header and comments promote them to concrete geometry without the required bridges.

`G2CASFactorizationCarrier.lean` describes `leftFactorWord` and `rightFactorWord` as retained CAS factors and proves only that `collect` lands in `unipotentSubgroup`. It contains no theorem aligning the product with `flagRepresentative` for all valid `(k,i)`. Thus “exactly retained” is data provenance, not factorization correctness.

`G2NativePointStabilizerLineFiber.lean` has a theorem named `nativePointStabilizer_lineFiber_surjective`, but its quantified map is the existing `intrinsicLineMapEquiv` for an arbitrary automorphism and the parameter `_hg` is unused. It does not prove that `nativePointStabilizer` acts transitively on the three lines through the base point. The name is therefore semantically misleading if read as the missing fiber-transitivity theorem.

## Fresh local audit: exact row count is five, not 189

Direct source inspection gives only five exact group-factorization row theorems in `G2FlagFactorizationRows.lean`: `row_0_0`, `row_1_24`, `row_4_6`, `row_4_18`, and `row_1_45`. The `(4,18)` theorem has the reversed product `right * Weyl * left`; it is not an instance of the uniform raw-table orientation. The same file has only two residual matrix-existence statements, for rows `(1,73)` and `(1,178)`.

`G2FlagCellQuotientWitness.lean` upgrades the four rows in cell 1 and the anchor rows to quotient witnesses. It does not prove `hcell` for cells 2 through 11, and it does not establish a 189-row certificate. Consequently any claim that this owner closes full orbit coverage or Bruhat covering is false on the current source.

## Fresh local audit: transport bridges are conditional and correctly scoped

`G2FlagCellFactorizationBridge.lean` is a valid transport lemma: from explicit hypotheses `hb₁`, `hb₂`, and `hfac`, it proves concrete Bruhat-cell membership and quotient left-scaling. It does not supply `hfac`; it is not evidence for the CAS factorization itself.

`G2ConcreteBruhatOrbitCertificate.covering_eq_univ` is likewise a valid assembly theorem, but its hypotheses include an equivalence `enum : Fin 189 ≃ CarrierQuotient`, a complete cellwise `hcell`, and the partition identity. Its `ambient_order` corollary derives the native order only after that quotient equivalence is supplied. Calling this a completed cover or order proof reverses the dependency direction.

`G2ConcreteBruhatExhaustion.concreteBruhatCovering_eq_univ` is also conditional: it requires `ConcreteBN2Transition` and a closure-top hypothesis for the unipotent subgroup together with the two generators. The theorem proves the consequence of those inputs; it does not prove the transition law or the closure-top fact. The repository therefore has multiple valid exhaustion interfaces, but no unconditional concrete exhaustion theorem.

## Audit correction: the real-form capstone owner is honestly scoped

Inspection of `InfoGeometry/Lie/SplitG2RealFormCapstone.lean` and `G2TwoRealSplitClassification.lean` shows an important non-finding. The real-form owner explicitly limits its conclusions to the 14-dimensional derivation model, the 12-root index/cardinality, native root-index bijectivity, and the one-parameter flow law. Its module comment expressly says that no global Lie-group identification is claimed without a separate development. These owner statements are `GREEN` at that scope.

The overclaim is in external summaries that describe this limited conjunction as a completed full split-(G_2) representation/Weyl capstone. The source owner itself should not be accused of asserting those absent results. This correction is recorded to keep the audit evidence-based rather than adversarial.

## Fresh local audit: Bryant–Wilmot file proves only orthogonal skewness

`G2BryantWilmotCliffordBridge.lean` documents a 14-parameter `𝔤₂` basis “leaving the associative calibration 3-form Φ invariant”, but its actual exported theorems prove only `bryantWilmotMatrix_skew` and preservation of the explicitly defined Euclidean bilinear form. No `Φ` is defined in the file, and no calibration-form invariance, octonion derivation identity, Lie-bracket closure, or equivalence with the repository's canonical/Zorn derivation carrier is proved. The honest scope is a 14-parameter subspace of `𝔰𝔬(7)` with metric preservation; the `𝔤₂`/Clifford bridge in the header is an unsupported semantic promotion.

## Fresh external audit: STA Octonionic Illustration is not a proof source

The page [Space-Time-Algebra (STA) Octonionic Illustration](https://theoryofeverything.org/theToE/2024/09/23/space-time-algebra-sta-octonionic-illustration/) was inspected on 2026-08-26. It links to Lasenby (2022), but the page itself is an illustration/blog post, not a formal proof or a peer-reviewed construction of the repository's carriers.

The page states that it displays an STA octonion representation and an octonion/STA multiplication table, then claims “7 sets of split octonions” for each of 480 parent octonions, sign-mask constructions, E8 vertex indexing, and 7-by-7 derivation nullspaces. It does not define a Zorn algebra, a split quadratic composition norm, a finite field carrier, `SplitOctF2Aut`, or an explicit equivalence preserving multiplication and derivations. The page therefore cannot validate the Lean split-Zorn or finite G₂ corridor.

It also describes 14 “null vectors” as defining the dimension of (G_2) and combines the derivation discussion with E8/Pascal/sign-mask indexing. Those assertions are presentation-level claims on the page; no theorem establishes that the listed nullspaces are the Lie algebra of the split real form or the finite automorphism group. In particular, a 7-by-7 nullspace computation is not by itself a proof of a group isomorphism, Weyl action, Bruhat decomposition, or certificate alignment.

The page's use of “split octonions” is consequently not evidence that the compact notebook `OctonionsAndG2.nb`, the repository's split-Zorn carrier, and the page's STA/sign-mask tables are the same algebra. An explicit carrier-level multiplication-preserving map would be required before any cross-source theorem could be stated. Classification: `EXTERNAL ILLUSTRATION / UNVERIFIED CARRIER CLAIM`.

## Fresh local audit: staged split-Cayley addition

The current worktree contains staged additions
`lean/InfoGeometry/Algebra/SplitCayleyF2.lean` and
`scripts/verify_split_cayley_f2.py`.  They are not part of `HEAD`, are not
included in the committed baseline, and were not published as remote owners.
The Lean theorem `norm_mul` is proved by
`native_decide` over the finite carrier, while the Python companion performs
an explicit finite product loop.  This can be valid finite verification, but
it is not a structural derivation from the cited literature and it does not
establish any equivalence with the existing `SplitOctF2`/`SplitOctF2Aut`
carriers.  Status: **STAGED / NOT PROMOTABLE AS BASELINE**.

## Fresh local audit: generic `FiniteAut` is not the concrete G₂(2) group

`G2FiniteChevalleyGroupBridge.lean` defines a generic `FiniteAut O` for an
arbitrary ring `O` and then introduces `g2TwoOrder := 12096` as a natural
number.  Its order theorems are `rfl`/arithmetic identities about those
constants; no `O := SplitOctF2`, no equivalence with `SplitOctF2Aut`, and no
cardinality theorem for the generic `FiniteAut` is supplied.  The filename and
heading therefore overstate the result: this is an abstract automorphism
structure plus an external order ledger, not a formal identification
`G₂(2) = Aut(SplitOctF2)`.

## Fresh local audit: generic BN-pair “master theorems” are not G₂ instances

`G2BNPair.lean` proves `doubleCoset_eq_iff`, unique-cell, and cardinality
theorems for a parameterized `TitsSystem`/`FiniteBruhatPartition`.  The
required cell-disjointness, cell-cover, kernel, and related laws are fields of
those structures.  `G2TwoBruhatClassification.lean` supplies concrete-looking
definitions and arithmetic lists, but no complete structure instance proving
all those fields for `SplitOctF2Aut`.  Therefore the generic “MASTER THEOREM”
names do not constitute a concrete BN-pair or Bruhat classification of the
native group.

## Machine evidence: semantic-vacuity gate on staged owners

The repository's own `tools/quality/semantic_vacuity_gate.py` was run on the
current staged certificate files.  On `G2CellFactorizationCertificate.lean`
it reported two findings: a `carrier_witness_name` warning for
`CellFactorizationCertificate`, and a `proof_like_field_type` warning for its
`sound` field.  On `G2FlagFactorizationNormalizedData.lean` together with
`G2FactorizationAlignmentCertificate.lean` it reported 16 findings, including
two errors (`pure_proof_carrier`) for the alignment structures and ten
`proof_like_field_type` warnings for their obligation fields.

This machine evidence does not replace the source audit; it independently
confirms that these structures are proof/proxy packages rather than derived
certificate data.  Their declarations may be mathematically useful as
conditional interfaces, but they are not evidence that the underlying
factorization, separation, or residual-injectivity obligations were proved.

## Fresh local audit: the finite-Chevalley bridge cannot instantiate on the octonion carrier

`G2FiniteChevalleyGroupBridge.lean` declares

```lean
structure FiniteAut (O : Type*) [Ring O] where ...
```

and all of its algebraic assumptions are the associative `Ring` interface.
The repository's `SplitOctF2` is a nonassociative Zorn carrier; no `Ring
SplitOctF2` instance is provided (and installing one would change the
mathematics).  Consequently this owner cannot be instantiated directly with
the split-octonion carrier.  This is a hard type-level obstruction in addition
to the missing cardinality/equivalence proof.  The heading “G₂(2) =
Aut(𝕆_s(𝔽₂))” is therefore not merely conditional; the displayed `FiniteAut`
structure is the wrong algebraic interface for that instantiation.

## Fresh local audit: staged `SL3DualActionF2` is an action scaffold, not a Zorn automorphism

The untracked file `lean/InfoGeometry/Algebra/SL3DualActionF2.lean` defines
`SL3DualPair`, `rowAction`, `dualAction`, and a componentwise `zornAction`.
Its fields `right_inverse` and `left_inverse` are supplied as structure data;
the file proves neither that the selected concrete matrices satisfy those
fields nor that `zornAction` preserves `Cayley.mul`, `Cayley.one`, or
`Cayley.norm`.  The four readback lemmas only identify coordinate functions
for the chosen cyclic and shear matrices.  In particular, the documented
inverse-transpose convention is not yet a theorem, and no
`SL3DualPair -> Automorphism` bridge exists.  It is therefore an untracked
action scaffold, not evidence for an `SL₃` subgroup of native split-Cayley
automorphisms.

## Fresh local audit: quotient injectivity remains a conditional assembly theorem

`G2QuotientRepresentativeInjectivity.lean` contains a valid assembly theorem,
but `quotientRepresentativeEquiv` requires all three inputs `hcell`, `halign`,
and `hsurj`.  Its order corollary accepts an already supplied equivalence and
then invokes `ambient_order`.  The predecessor and PC-separation theorems in
the same file likewise take their factorization/separation data as hypotheses.
Thus this owner does not prove quotient injectivity, quotient surjectivity, a
`Fin 189` quotient equivalence, or the native order on its own.  Promoting the
theorem name to “189-point quotient closure” would erase the actual proof
obligations.

## Fresh local audit: symbolic BN2 owners assume the hard local laws

`G2SymbolicBN2.lean` and `G2IndexTwoRankOneBN2.lean` do prove valid generic
group-theoretic implications, but their structures contain the substantive
BN2 content as fields.  `ReflectionBN2Spec` assumes `toPC_surj` together with
both branch factorization identities; `LeviRootDecomposition` assumes the
factorization of every `b ∈ B`, complement invariance, and the rank-one Levi
law; `bn2_of_index2_split` additionally assumes the index-two split for the
particular element.  No concrete `SplitOctF2Aut` instance is constructed from
these interfaces in the inspected owners.  Therefore “complete BN2 proof” and
“without finite case analysis” describe a conditional reduction, not a native
G₂ BN2 theorem.  The missing obligations are mathematical inputs, not merely
Lean tactic work.
## Fresh local audit: `G2TwoPCMatrixCertificate` advertises a theorem that is commented out

The module header of `G2TwoPCMatrixCertificate.lean` says that it establishes
the complete carrier product identity.  At lines 535--555, however, the
declared theorem `pcWord_mul_eq_pcCombine` and the advertised matrix product
corollary are inside a block comment.  The live theorem `autMatrix_pcWord`
proves only the image of one PC word, plus three matrix-entry readbacks.  It
does not export the global multiplication identity used by a normal-form
argument.  Consequently the header's “complete carrier product identity” is
not a theorem in the current environment; downstream users must not cite this
file as having proved arbitrary PC-word multiplication.
## Fresh local audit: `G2PCCollection` is an abstract exponent evaluator

`G2PCCollection.lean` defines `PCExp := Fin 6 → ZMod 2`, lists and the
recursive functions `mulGen`, `collectWord`, and `normalizeWord`.  Its live
theorems establish identities of exponent vectors and words.  The file does
not import or mention `SplitOctF2Aut`, `pcWord`, `autMatrix`, or a map from
its `PCExp` word semantics to the native automorphism carrier.  Thus its
“complete Polycyclic Collection Algorithm” is not, by itself, a proof of
native PC-word multiplication or a native normal form.  Any claim that this
owner closes the automorphism-group normal-form bridge requires a separate
carrier-preservation and evaluation theorem.
## Fresh local audit: `G2GAPCosetHomomorphismBridge` contains no GAP permutation map

`G2GAPCosetHomomorphismBridge.lean` defines `actionHom` by conjugating the
canonical left-translation action on `G ⧸ H` through an assumed equivalence
`enum : Fin n ≃ G ⧸ H`.  Its homomorphism and intertwining proofs are valid
for that internally defined action.  No GAP permutation array, generator
comparison, or theorem identifying an exported permutation with `actionHom`
appears in the file.  The signatures also assume `enum` and, where needed,
`h_enum : enum i = QuotientGroup.mk (reps i)`.  Therefore the heading
“GAP Action Homomorphism” is a misdescription of a generic quotient-action
construction; it does not certify a GAP/native action correspondence.
## Fresh local audit: `flagVarietyCosetCount_eq_189` is a list identity, not a quotient theorem

In `G2TwoBruhatClassification.lean`, `WeylG2` is the parameter type
`ZMod 6 × Bool`, `weylLengthsList` is a literal list, and
`inversionSubgroupSizes` is its mapped list.  The theorem
`flagVarietyCosetCount_eq_189` is `rfl` for the sum of that list.  It does not
mention a quotient, `SplitOctF2Aut`, `sylowTwoSubgroup`, or a native flag
carrier.  Likewise `bruhatCellWeights_sum_eq_12096` is `rfl` for a second
hand-defined list.  These are correct arithmetic identities, but the comments
calling them the flag variety/cell cardinalities are semantic promotions unless
the missing quotient and cell parametrization theorems are supplied.
## Machine evidence: full Zorn semantic-vacuity scan

The repository gate was run on `lean/InfoGeometry/Algebra/Zorn` with
`semantic_vacuity_gate.py --top 200`.  It reported `semantic_vacuity: 289`
with `error: 2` and `warning: 287`.  The two errors are
`FactorizationAlignmentCertificate` and
`ConcreteFactorizationAlignmentCertificate`, both classified as
`pure_proof_carrier`; the scan also reported 70 `proof_like_field_type`
findings, 11 direct aliases, 5 carrier-witness names, and 197 trivial-surface
findings.  The command exited with status 1.  This is a screening result, not
proof that every warning is a defect, but it independently confirms that the
repository contains many proof packages and arithmetic/projection surfaces
that require semantic review before promotion.
## Fresh local audit: `simpleRootSubgroup` and `rootSubgroup` are different carriers

`G2TwoExplicitGenerators.lean` defines `simpleRootSubgroup` as the closure of
two automorphisms and proves `Fintype.card simpleRootSubgroup = 8` via an
eight-word normal form.  The separate `G2RootSubgroup` owner defines
`rootSubgroup α` literally as `{1, rootAut α}` and proves its cardinality is
2.  No theorem identifies these subgroups.  Treating the former as a single
Chevalley root subgroup, or using its 8-element equivalence as the root-space
coordinate, is therefore a carrier error, not a harmless naming choice.
## Fresh local audit: `nativeRootWeight_cycle_compat` does not identify the Weyl-transformed root

In `G2NativeWeylCartanRestrictionEquiv.lean`, both
`nativeRootWeight_cycle_compat` and `nativeRootWeight_reflection_compat` are
proved by `rfl`.  Their right-hand sides retain the same index `i` and merely
precompose the canonical weight with the inverse transported Cartan
equivalence.  Neither theorem states, or proves, an equality with
`nativeRootWeight (rootIndexOf (cAction r))` or the corresponding reflection
index.  They are definitional transport identities, not the missing dual Weyl
action compatibility.  Treating these names as the requested root-action
bridge is therefore an overclaim.
## Fresh local audit: orientation “normalization” is not derived

`G2FlagFactorizationOrientation.lean` defines `normalizedLeftFactorWord` and
`normalizedRightFactorWord` by swapping the two raw words according to a
caller-supplied `reversed : Bool`.  Its soundness theorem requires
`hsound`, whose proposition is already the desired exact factorization in the
selected orientation.  `G2FlagFactorizationNormalizedData.Data` stores only
the Boolean orientation table; `sound` and `toCellFactorizationCertificate`
still require the full global `hraw` factorization proposition.  Thus this
layer does not derive orientation metadata, validate a row, or construct a
certificate from CAS data.  It is a correct reindexing wrapper, but calling it
“normalization” without a proved orientation table and row soundness is a
semantic overclaim.
## Fresh local audit: `G2CartanSymmetricSpaceIdentification` is definitional/parametric

The file header advertises a kernel-verified identification of the split real
`G₂` Cartan decomposition with a symmetric space, moment-map, Gibbs, Massieu,
and Tomita structures.  Source inspection shows a narrower result.  The live
theorems establish the Cartan finrank (`2`), total derivation dimension (`14`),
and the root-space sum dimension (`12`).  `momentMap_cartanProjection` and
`souriauMassieu_gibbsLogPartition` are definitional (`rfl`) identities;
`gibbsKernel_cartanCharacter` delegates to an existing equality; and
`tomitaModularHamiltonian_eq_cartanMoment` is conditional on an arbitrary
`CartanMomentRepresentation` and an existing bridge.

No theorem in this owner proves the advertised symmetric-space identification,
symplectic moment-map properties, an analytic Gibbs/log-partition theorem, or a
Tomita–Takesaki modular construction.  The truthful scope is repackaging of
existing definitions plus dimension/equality lemmas.  It must not be promoted
as the geometric/physical identification without independent native
intertwining and structural theorems.
## Fresh local audit: factorization alignment certificates do not derive factorization

The current `G2FactorizationAlignmentCertificate.lean` contains the desired
exact factorization as the `base` field of both
`FactorizationAlignmentCertificate` and
`ConcreteFactorizationAlignmentCertificate`.  Its theorems
`generic_factorization` and `concrete_factorization` merely project that
field, and therefore do not construct or verify any certificate row.  The
`step`, `separation`, and residual fields do not repair this: the theorem
already assumes the exact group equality for every base case.

This is not a proved concrete 189-row factorization owner.  It is a conditional
interface whose main conclusion is an input hypothesis.  The name
`ConcreteFactorizationAlignmentCertificate` must not be used as evidence that
the native representatives have been aligned with the exported words.

## Fresh local audit: `G2Fin189OrbitMembership` remains conditional assembly

`G2Fin189OrbitMembership.lean` derives its quotient witness from
`C.normalizedLeftFactorWord`, `C.normalizedRightFactorWord`, and
`factorization_of_mem C k i hi`.  Since `CellFactorizationCertificate.sound`
is itself a structure field, this owner supplies no independent matrix
readback, orientation proof, or 189-row witness derivation.  Its covering
theorem additionally requires an external enumeration equality `henum`.
The file is therefore a valid conditional transport layer, not a closed
`Fin 189` orbit certificate or a proof of Bruhat coverage.
## Fresh local audit: normalized-data owner still assumes raw soundness

`G2FlagFactorizationNormalizedData.lean` does not derive orientation metadata.
Its `Data.reversed` field is arbitrary, and theorem `sound` requires
`hraw`, whose proposition is already the exact row factorization in one of
the two orientations.  The constructors `toCellFactorizationCertificate`
and `factorization_of_data` therefore repackage an assumed theorem; they do
not validate CAS words against `flagRepresentative`.

The companion `G2FlagFactorizationNormalizedRows.lean` is honest but partial:
it contains only five proved rows, namely the four listed ordinary rows and
the swapped `(4,18)` row.  Its `row_*_data_sound` theorems project those
existing row theorems.  It is not a normalized 189-row certificate.

## Fresh local audit: finite word-table facts are not representative alignment

`G2FlagWordCertificateEval.lean` defines `flagRepresentative` by evaluating
the existing `flagRepWords` table and proves membership in the generated
subgroup.  Its recursive lemmas require an equality identifying a word with a
cons/predecessor form.  The file's partition, cell-cardinality, and
pairwise-disjointness results are computations on the declared `flagCells`
table; they do not connect those cells to the native Bruhat representatives or
prove the missing factorization alignment.
## Fresh local audit: finite-cardinality equivalences are not geometric bridges

`G2Fin189Certificate.lean` gives an equivalence between
`Σ w, Fin (weylLength w) → Bool` and `Fin 189` by delegating to
`canonicalBinaryFlagIndexEquiv`.  This is a combinatorial index equivalence;
the file explicitly contains no quotient-orbit membership proof.  It must not
be cited as an equivalence between the native quotient, native flags, and the
declared 189-element carrier.

`G2NativeIntrinsicFlagBridge.lean` and
`G2NativeIntrinsicLineFiberBridge.lean` use `Fintype.equivOfCardEq`.  These
produce arbitrary finite-type equivalences from cardinality equalities; they
do not preserve the group action, incidence, fibers, or the native point/line
maps.  The line owner also proves that the named parabolic trio is not three
distinct lines, so the earlier interpretation as explicit three-line
representatives is false.

## Fresh local audit: stabilizer equality remains fully conditional

`G2NativeFlagStabilizerCardinality.lean` proves stabilizer equality only from
the supplied hypotheses `|SplitOctF2Aut| = 12096`, flag cardinality `189`, and
surjectivity of the action on `baseIntrinsicFlag`.  It is a correct
orbit--stabilizer assembly theorem, but it does not prove any of those three
inputs.  Therefore it is not evidence that the native stabilizer has been
identified with `unipotentSubgroup` in the current development.
## Correction and provenance: PC multiplication owner versus GAP data

The earlier audit statement needs a precise qualification.  The theorem
`pcWord_mul_pcWord` is live and proved in
`G2TwoPCConcreteCollector.lean` by the native single-generator collection
lemmas.  However, the corresponding named theorem and matrix corollary in
`G2TwoPCMatrixCertificate.lean` remain inside a block comment.  The live
`G2TwoPCMatrixProductBridge` imports and uses the collector theorem directly;
it does not make the commented theorem live.

This native PC multiplication result is independent of the GAP flag witness
payload.  No GAP-generated flag row has thereby been validated.  The GAP
payload remains untrusted data until a Lean theorem evaluates its supplied
words against the actual `flagRepresentative` carrier and proves the required
matrix equality.  No such full 189-row proof was found in this audit.
## Fresh local audit: admissible-basis “torsor” is tautological, not an independent classification

`G2TwoBasisRigidity.lean` does contain a genuine equivalence
`admissibleBasis7Equiv`, but its admissible subtype is defined by requiring the
extended map to preserve the native multiplication and unit.  The inverse is
then constructed directly from that same map.  The transported action and
“simply transitive torsor” theorem are consequently valid reparameterizations
of the already-given automorphism carrier.

They do not independently enumerate admissible bases, prove the order
`12096`, identify a geometric flag carrier, or establish a BN/Bruhat
classification.  Calling this theorem a structural replacement for the
classification is an overclaim: it is an exact tautological parameterization
of automorphism images.
## Fresh local audit: orbit partition and Weyl labels are declared tables

`G2FlagOrbitPartitionCertificate.lean` defines `orbitCells` as the existing
`flagCells` table and `orbitWeyl` by a sign/reversal conditional on
`flagWeyl`.  The partition theorem and anchor-membership theorem therefore
establish properties of those declared finite tables.  The anchor readback is
checked against the native matrices, which is genuine for the twelve anchors,
but it does not prove that the full table is the native Bruhat orbit partition
or that the `orbitWeyl` convention is induced by a native Weyl action.

`G2QuotientRepresentativeCoverage.lean` correctly keeps the missing coverage
as hypotheses such as `QuotientRepresentativeCover` or a family `hmat`.  The
resulting quotient witnesses are valid conditional transport lemmas; they do
not constitute a derived certificate family.
## Fresh local audit: the 189 representative carrier is a generated word table

`G2FlagWordCertificate.lean` begins with the explicit disclaimer that it was
generated from a GAP ExtRep audit and that propositions are intentionally not
asserted.  It defines `flagRepWords` and `flagCells` as literal finite tables.
`G2FlagWordCertificateEval.lean` then defines the native
`flagRepresentative` by evaluating those words and proves only generated-
subgroup membership.  Its partition and cardinality theorems compute the
declared tables; they do not prove that the rows are quotient representatives
for the native group or that the cells are native Bruhat orbits.

Consequently every claim that the table itself is a kernel-verified 189-point
quotient, flag orbit, or Bruhat certificate is an overclaim unless it also
supplies the missing carrier-alignment, injectivity, and coverage theorems.
## Fresh local audit: the `64 × 189 = 12096` counting owners are formal arithmetic

`G2TwoPCSubgroupClosure.lean` genuinely proves that the native range of the
six-bit `pcWord` map is a subgroup of cardinality `64`.  It does not prove
that this subgroup is a Borel subgroup of a Chevalley group or that the native
ambient automorphism group has order `12096`; the Sylow conclusion explicitly
requires the ambient-cardinality hypothesis.

By contrast, `G2BruhatCardinalities.lean` and `G2TwoBruhatCounting.lean`
define length lists, cell-size functions, and abstract `borelOrder`/
`chevalleyG2OrderFormula` functions, then prove numeral identities by
`decide`, `ring`, `norm_num`, or `rfl`.  Those identities do not establish
native Bruhat cells, a BN-pair, a Borel subgroup, or an equality
`Nat.card SplitOctF2Aut = 12096`.  Their “master theorem” wording is therefore
semantic overclaiming of arithmetic scaffolding.
## Fresh local audit: concrete cell equality is local, not Bruhat decomposition

`G2FinitePCBruhatCell.lean` proves the honest set equality between the
finite PC-word double-product set and the already-defined
`concreteBruhatCell`.  This is a useful native carrier bridge, but it does
not prove that the twelve chosen Weyl representatives exhaust the ambient
group or that the cells are disjoint.

`G2BruhatCellIntersectionCard.lean` gives a conditional double-coset
cardinality identity and the identity-cell cardinality.  It requires finite
instances and derives no intermediate-cell sizes or global covering.  The
later exhaustion owner still requires `ConcreteBN2Transition` and a closure-
top generation hypothesis.  Any summary treating these local results as a
completed Bruhat decomposition is therefore false.
## Fresh local audit: parabolic/hexagon geometry is a finite model, not native `G₂(2)` identification

`G2PeirceParabolicStabilizer.lean` proves finite facts about explicitly
defined `ProjectiveLineF2`, `LinesThroughPoint`, and the exported incidence
data.  The three-line exhaustion and `189 = 63 · 3` calculation are genuine
for those declared carriers.  The parabolic coset/cardinality results require
surjectivity, distinctness, stabilizer, and preservation hypotheses; they do
not derive those hypotheses from `SplitOctF2Aut`.

Thus phrases such as “certified generalized hexagon of `G₂(2)`” or “maximal
parabolic subgroup” overstate the current formal result unless an explicit
equivalence between the incidence model/coset carrier and the native group
action is supplied.
## Fresh local audit: generator alignment is not BN2 transition

`G2CASGeneratorAlignment.lean` does contain genuine native matrix proofs for
the six CAS generator words and should be retained as a GREEN generator
readback owner.  This proves only those explicit generator equalities.

`G2ConcreteGeneratorInfrastructure.lean` proves closure consequences such as
unipotent left multiplication preserving the declared Bruhat union.  Its
simple-reflection transition is explicitly packaged as the proposition
`ConcreteBN2Transition`; the exhaustion theorem requires that proposition and
a separate closure-top generation hypothesis.  The generator alignment
theorems do not imply either obligation.  Any narrative saying that CAS
generator alignment has already established the concrete BN2/Bruhat lift is
therefore false.
## Scope correction: the 63-point transitivity owner is genuine at its stated carrier

The earlier broad skepticism must not be applied here indiscriminately.
`G2CASNativePointEnumeration.lean` proves isotropy/nonzeroness and injectivity
of the explicit `casPoint` table by native computation, then obtains its
surjectivity from the independently proved native carrier cardinality.  The
generator intertwining lemmas connect the exported permutations to
`octImAction`, and `native_point_orbit_cover` constructs a word witness for
every native isotropic point.

Thus `octImPointPerm_base_surjective` is a genuine 63-point native-action
theorem, albeit certificate/table-based.  It does not imply 189-flag
transitivity, and must not be described as doing so.
## Consolidated current status of the audited corridor

### GREEN: native results actually established

The current source genuinely establishes the split-octonion/Zorn operations
and derivation definitions, native automorphism actions and faithful matrix
readback, the six-bit `pcWord` multiplication/inverse/normal form and native
unipotent subgroup cardinality `64`, the native 63-point isotropic carrier and
its transitive action, selected anchor/row readbacks, and the finite abstract
Weyl/Poincaré arithmetic.  These results are scope-limited and should remain
available.

### YELLOW: correct only under explicit hypotheses

The following are assembly interfaces rather than completed classifications:
stabilizer equality from a flag census/transitivity or full-peel certificate;
parabolic stabilizer equality from rigidity and cardinality hypotheses; native
quotient equivalence from injectivity/surjectivity hypotheses; concrete Bruhat
exhaustion from `ConcreteBN2Transition` and closure-top generation; and all
factorization-certificate structures whose `sound`/`base` fields are supplied
by the caller.

### ORANGE: finite/table or cardinality surrogates

The 189 word/cell tables, abstract Weyl length sums, arbitrary
`Fintype.equivOfCardEq` bridges, transported admissible-basis action, and
selected GAP rows are useful data or interfaces but do not by themselves
identify native quotient flags, native Bruhat cells, or native Weyl actions.

### RED: claims contradicted or unsupported by current source

The full 189-row exact factorization claim; the promotion of the five-row
factorization owner to a global certificate; generic
`BruhatResidualExponent p ≃ residualSubgroup p` under the current residual
definition (refuted at `(2,true)` by cardinalities `8` versus `32`); the
unconditional native `G₂(2)` order `12096`; full BN/Bruhat coverage and flag
transitivity; and the advertised real 14-dimensional Weyl-adjoint character
are not established.  Some proposed versions are directly false, rather than
merely awaiting a proof.
## Fresh local audit: `G2BNBruhatFramework` has local BN-style lemmas, not a BN-pair

The native framework proves genuine local facts: the PC range is a 64-element
subgroup, selected concrete Weyl representatives are in their declared
double-coset sets, the identity cell is the PC subgroup, and the intersection
with the declared concrete normalizer is trivial.  It also proves only a lower
bound of `64` for each concrete cell.

The file does not provide a concrete BN-pair instance, a proof that the
declared normalizer has exactly the intended Weyl quotient, intermediate cell
cardinalities, or ambient coverage.  Its “Weyl Element Unipotent
Classification” and “Tits System Kernel Property” names describe local
intersection/readback statements, not the full BN/Bruhat axioms.  The
framework header's classification language is consequently stronger than the
proved native content.

## Fresh local audit: repository-level completion documents overclaim semantic closure

The narrative status documents make claims that are not supported by the current
theorem owners. `README.md:12` says that the theorems prove a reversal of the
traditional physical hierarchy with zero axioms and zero `sorry`s;
`README.md:133-139` calls the result speculation-free, complete, and
“unassailable”; and `README.md:281-288` calls the repository a mathematically
closed foundation and says it is 100% verified. These statements are broader
than the source-level results audited above: conditional interfaces, generated
data tables, arithmetic identities, and explicit missing G2 bridges remain.

`CAPSTONE.md:3` describes a fully closed kernel-checked pipeline across split
octonions, BdG, modular thermodynamics, Cuntz algebras, error correction, and
QGT. Its verification matrix at `CAPSTONE.md:9-13` and final certification at
`CAPSTONE.md:187-196` assert complete compilation, zero semantic findings, a
clean main branch, and permanent closure. Those assertions do not establish
the semantic bridges they name; in particular they do not establish the native
G2 quotient, full Bruhat coverage, real Weyl transport, or the physical
interpretations claimed elsewhere. The current worktree is also not clean, and
the local semantic-vacuity audit reported findings, so these status lines are
stale or unverifiable as current release evidence.

`COMPLETION_STATUS.md:4` declares all steps complete, while
`COMPLETION_STATUS.md:8-18` reports multi-engine completion and
`COMPLETION_STATUS.md:20-33` presents phenomenological predictions as
validated. Its “14 critical theorems” table (`COMPLETION_STATUS.md:35-56`)
assigns physical meanings to theorem names without proving the corresponding
experimental or physical claims; `COMPLETION_STATUS.md:75-77` even calls the
result the first rigorously verified derivation of nuclear structure. No audited
Lean statement in this corridor proves that conclusion.

Classification: **RED — repository-level semantic promotion**. A build count,
absence of `sorryAx`, or successful checking of individual propositions proves
only those propositions from their dependencies. It does not certify the
theory-level narrative, physical predictions, or missing native bridges. These
documents should be treated as historical/narrative material until their claims
are rewritten with theorem-level scope and reproducible current-state evidence.

## Fresh local audit: symbolic BN2 is an interface theorem, not a concrete BN2 proof

`G2SymbolicBN2.lean:48-60` defines `ReflectionBN2Spec` with `toPC_mem_B`,
`toPC_surj`, and both branch equations as fields. The main result
`symbolic_bn2_pointwise` (`:71-93`) is therefore a valid deduction from a
certificate supplied by the caller, but the file does not construct such a
certificate for the native `SplitOctF2Aut`, its unipotent subgroup, or its two
concrete Weyl generators. The header's “complete `(B,N)` axiom” wording is
thus an interface specification, not a completed native BN2 theorem.

`G2GroupOrderReduction.lean:35` says that all proofs are complete and contain
no unproved placeholders. The actual order theorem at `:65-69` is explicitly
conditional on quotient cardinality `hq = 189`; the following equivalence
version is conditional on an explicit `Fin 189 ≃ quotient` (`:71-75`). The
file proves a reduction, not `Nat.card SplitOctF2Aut = 12096` unconditionally.
Its completion sentence is therefore an overstatement of the module's scope.

Classification: **RED/YELLOW**. The Lean implications are valid at their
stated hypotheses, but the surrounding “complete”/“axiom” language promotes
uninstantiated certificates and conditional reductions to concrete native
classification results.

## Fresh local audit: big-cell “certificates” are polynomial data plus a missing carrier law

`G2BigCellPolynomialWitnesses.lean:7-15` calls the polynomial maps CAS-certified
witnesses, but the file only defines maps in `PCExp := Fin 6 → ZMod 2`.  The
actual group statement is packaged as `HasBigCellFactorization` at `:117-123`.
The purported main results `s1_big_cell_reduction` and
`s2_big_cell_reduction` (`:125-156`) require the complete factorization law
as hypotheses `h_carrier`; they merely return those same hypotheses with the
explicit polynomial maps.  No native `SplitOctF2Aut` carrier, PC embedding,
matrix readback, or concrete Weyl generator is instantiated here.

Thus the polynomial formulas may be useful exported data, but they are not
verified Chevalley/BN2 identities. Classification: **ORANGE** for the data
layer and **YELLOW** for the conditional implications. The words
“Certified”, “MAIN THEOREM”, and “CAS-certified commutator matrix identity”
overstate what this file itself proves.

## Fresh local audit: `rootSubgroup` is a declared two-element model, not a classified native root subgroup

`G2RootSubgroup.lean:15-33` defines `rootSubgroup α` literally by the carrier
`{g | g = 1 ∨ g = rootAut α}`. Its closure follows from the supplied
involution theorem for `rootAut α`. `G2RootSubgroupBaseEquiv.lean:147-181`
then proves that `Bool → rootSubgroup α` is an equivalence because every
element satisfies that defining disjunction.

Thus `G2NativeRootSubgroupSystem` is coherent for this declared two-element
model, including transport under the declared concrete automorphisms. It does
not prove that this subgroup is the corresponding Chevalley root subgroup of a
native BN-pair, nor that the native residual intersection is generated by it.
Calling it a native root-subgroup classification would be a semantic
promotion beyond the statement. Classification: **ORANGE** for the
model/interface, **RED** for any downstream identification with the full
Chevalley/Bruhat root-subgroup structure.

## Fresh local audit: older multi-system reports also promote local formalization to physical verification

`docs/ATTENTION_IS_QUANTUM_FLUID.md:5-17` claims a rigorously verified complete
causal chain and identifies attention with quantum-fluid flow; its closing
status (`:372-374`) says “COMPLETE” and ready for arXiv submission.  The
document itself does not provide a single Lean theorem establishing that
semantic identification.  A zero-hole theorem about a stated algebraic model
would not establish the asserted claim about Llama-4 or physical fluid flow.

`docs/NAVIER_STOKES_LEGENDRE_8_SYSTEM_VERIFICATION.md:1-6` and `:321-340`
similarly call the synthesis fully verified and publication-ready while
reporting only zero `sorry` in a main theorem.  That metric does not imply
verification across eight systems, nor the physical conclusions listed at
`:325-329`; the report supplies no theorem-level cross-system equivalences for
those claims.  These are **RED documentation-level semantic promotions**.
They should not be used as evidence that the corresponding mathematical or
physical theories have been formalized.

## Fresh local audit: “Grand Identity” reports contradict their own scope section

`docs/GRAND_IDENTITY_DE_RHAM_MODULAR.md:1-5` labels
`d(ln Q) = dS_Boltz = H_modular` “VERIFIED” by Python, SymPy, and Lean. The
same document later states at `:252-265` that the current packet proves only a
bounded scalar decomposition and a conditional derivative consequence, and
explicitly says that the listed information, thermodynamic, topological,
modular, and geometric objects are not all identified in one proved theorem
surface. Nevertheless `:283-305` promotes the identity to a “fundamental
truth”, grand unification, and completed formal verification. This is an
internal contradiction. Classification: **RED**.

`docs/GRAND_IDENTITY_8_SYSTEM_VERIFICATION.md:1-14` declares an eight-system
verification, but its own conclusion (`:192-204`) limits the result to a local
Boltzmann/Von-Neumann packet and explicitly records that no global
de Rham/modular capstone or finished divergence-free/symplectic theorem exists.
The correct status is the latter local packet, not “COMPLETE”. Classification:
**RED**.

## Fresh local audit: Viazovska/Kitaev synthesis maps unrelated local lemmas to major external theorems

`docs/VIAZOVSKA_KITAEV_CLIFFORD_SYNTHESIS.md:1-14` states that Viazovska
sphere-packing theory, Clifford roots, and Kitaev chains are “fully mapped and
kernel-verified”, then associates local theorem names with the E8 lattice,
Leech lattice, Golay code, modular forms, and zeta partitions. The document's
own verified index (`:52-61`) lists local metric, counting, anticommutation,
and colimit declarations, but supplies no proved equivalences to the cited
external structures. Its global status (`:65-69`) again treats build counts and
“0 sorries, 0 custom axioms” as verification of the synthesis. These local
facts do not prove Viazovska's theorem, the Leech/Golay identifications, a
Kitaev topological invariant, or the asserted infinite Clifford colimit.
Classification: **RED** documentation-level semantic promotion.

## Fresh local audit: Bruhat counting owner is arithmetic, and a native root-action proposal is refuted

`G2TwoBruhatCounting.lean:83-100` proves equalities between explicitly defined
functions `borelOrder`, `poincarePolynomialG2`, and
`chevalleyG2OrderFormula`.  At `:102-109`, `bruhatCellSizes` is a list made from
the supplied length list and `bruhatCellSizes_sum_eq_12096` is `rfl`.  The
“verified in GAP” comment does not supply a Lean identification of those list
entries with native double cosets, so the master theorem is arithmetic, not a
native Bruhat cell decomposition.

The opposite direction is also concrete evidence against one earlier proposed
bridge: `G2RootAutPCConjugation.lean:29-49` proves that conjugating the
singleton PC word at coordinate `2` by `c` is *not* the singleton at coordinate
`0`.  Any root/PC Weyl alignment using that equation is therefore false under
the current coordinate conventions and must not be used as a compatibility
lemma. Classification: counting claims **RED** when promoted to native order;
the failed conjugation equation is a **GREEN obstruction** that correctly
blocks the invalid alignment.

## Fresh local audit: cyclotomic arithmetic is mislabeled as a Chevalley group order

`G2CyclotomicPoincareFactorization.lean:27-43` defines
`poincarePolyZ` by an explicit polynomial literal and proves its factorization
by `ring`.  Evaluation at `2` is consequently a valid arithmetic identity
(`:45-64`).  The theorem named `g2two_chevalley_order_from_cyclotomic`
(`:66-71`) proves only `2^6 * 189 = 12096`; it has no variable for a group,
no native automorphism carrier, and no cardinality statement about
`SplitOctF2Aut`.

The same repository's more cautious `G2ChevalleyPoincareCombinatorics.lean`
explicitly records this boundary at `:16-19`. Thus the cyclotomic file's
“Full G₂(2) Chevalley Order Factorization” title is a semantic overclaim:
the formal theorem is arithmetic, not a group-order theorem. Classification:
**RED**.

## Fresh local audit: symbolic BN2 modules move the missing proof into premises

`G2SymbolicBN2Assembly.lean:40-52` puts the essential mathematical work into
`LeviRootDecomposition`: factorization of every `b ∈ B`, conjugation of the
complement, the rank-one Levi relation, and `s² = 1` are all fields.  The
theorem `symbolic_bn2_step` (`:58-92`) is a correct generic group calculation,
but it cannot establish those fields for the native G₂ carrier.  Likewise,
`G2IndexTwoRankOneBN2.lean:40-52` assumes the index-two split, conjugation
closure, and Levi identity before proving its corollary.  The advertised
replacement of concrete verification by “structural” proof is therefore only
valid after importing precisely the missing concrete structure. Classification:
**YELLOW** as generic lemmas, **RED** when presented as completed native BN2.

## Fresh local audit: the incidence cardinality proof is finite enumeration, not structural derivation

`G2HexagonIncidence.lean:57-75` presents the parabolic incidence certificate as
an abstract structural layer, but `parabolicLinePoints_card` (`:62-64`) and
`parabolicPointDegree` (`:69-72`) are proved by
`fin_cases ... <;> native_decide` over all 63 line/point indices. This is a
legitimate kernel-checked computation of the supplied finite table, but it is
not the advertised symmetry/fibration proof and does not establish that the
table is the orbit/incidence structure of native `SplitOctF2Aut`. The resulting
`189` flag count is consequently a table-cardinality result, not native flag
transitivity or quotient identification. Classification: **YELLOW** for the
finite certificate, **RED** when promoted to a structural native geometry
proof.

## Fresh local audit: promotional capstone documents contradict the repository proof policy

`docs/REPOSITORY_PROOF_POLICY.md:3-4` says that global realization claims
require explicit data and proofs. Its hard boundary at `:8-10` forbids a
completed coadjoint-orbit claim for `G₂(2)` without proved `Ad`, `Ad*`, cocycle,
and dual-map data, while `:25-28` forbids hiding missing proofs behind wrapper
certificates or vacuous packets. In contrast, `CAPSTONE.md:3` and `:194-196`
claim a fully closed pipeline and permanent certification, and
`README.md:281-288` claims a mathematically closed foundation. The audited G₂
owners still lack exactly the native realization and bridge data named by the
policy. This is an internal policy/documentation contradiction. Classification:
**RED**.

## Fresh local audit: `G2QuadraticCompatibility` is a generic coordinate lemma, not a G₂(2) automorphism theorem

`G2QuadraticCompatibility.lean:17-18` quantifies over an arbitrary
`CommRing R`, while `quadForm`, `bilinearForm`, and the Fano cross product are
defined directly on the coordinate type `Fin 7 → R` (`:23-35`).  Its
`IsG2Automorphism` predicate (`:183-197`) is only preservation of the chosen
coordinate bilinear form and trilinear form; it does not package a native
octonion algebra, linear-map structure, invertibility as an equivalence, or the
finite group `G₂(2)`.  The theorem `g2_crossProd_equivariant` (`:217-249`)
additionally takes an arbitrary left inverse as an explicit hypothesis.

The coordinate identities may be valid under these hypotheses, but the title
and “G₂(2) compatibility” language do not establish an identification with
the split-octonion automorphism carrier. Classification: **GREEN** for the
coordinate identities, **RED** if read as a native `G₂(2)` theorem.

## Fresh local audit: the older honesty report is stale and narrower than the current findings

`reports/honesty_audit.md:10-33` reports one banner-level misrepresentation and
one truthful “zero sorry” banner. That report is explicitly scoped to
`lean/InfoGeometry` (`:3`) and predates the current G₂ audit. It must not be
read as a repository-wide semantic clearance: the current G₂ source contains
multiple owner/header promotions, conditional contracts, and refuted bridges
documented above, while the completion documents add further RED claims.
Classification: **STALE/INCOMPLETE audit**, not evidence that only one
semantic misrepresentation exists.

## Fresh local audit: `G2TwoBruhatClassification` BN2-named lemmas are only cell-membership tautologies

The file header correctly disclaims global classification at
`G2TwoBruhatClassification.lean:14-20` and `:48-49`. However the declarations
named “Axiom BN2 Generator Compatibility” at `:547-557` prove only
`s * b ∈ concreteBruhatCell s` and `t * b ∈ concreteBruhatCell t`, by choosing
the factors `1` and `b`. They do not prove the BN2 inclusion
`s B s ⊆ B ∪ B s B`, do not conjugate `B`, and do not establish a concrete
BN-pair. The misleading theorem labels/comments are a semantic overpromotion
even though the underlying membership lemmas are correct. Classification:
**ORANGE**.

## Fresh local audit: arithmetic survey tables assert bridge theorems without identifying their carriers

`docs/SURVEY_ARITHMETIC_BRIDGE.md:3-15` reports `8/9` key files building and
then states as a “Bridge theorem” that a primon-gas C*-algebra is isomorphic to
a stabilized Fib(n) boundary algebra. The table records build status and
claimed connections, not a cited Lean theorem establishing that C*-algebra
isomorphism. The same issue occurs at `:17-35`, where Cantor Dirac spectra,
Berry–Keating/zeta claims, and a critical-line/golden-ratio correspondence are
promoted from file descriptions to bridge theorems without a common carrier or
proved analytic identification. The document even reports a pre-existing
build failure at `:3`. Classification: **RED** documentation-level promotion;
build status is not evidence for the listed cross-domain equivalences.

## Fresh local audit: spinor and Rosetta-Stone documents contradict their own formalization status

`docs/SpinorRep_COMPLETE_FOUNDATION.md:1-16` simultaneously labels the
foundation “MATHEMATICALLY COMPLETE” and says the Lean formalization is only
approximately 50% complete. `docs/SpinorRep_FINAL_STATUS.md:1-17` similarly
calls the theory complete while explicitly reporting two `sorry`s; its closing
status still says “PROVEN” with roughly 25 lines remaining. These are mutually
incompatible completion claims.

`docs/THE_ROSETTA_STONE.md:1-17` claims strict formal isomorphisms and a
computational proof that black-hole horizons are topologically equivalent to
Class-DIII boundaries. Later, however, the same document says stronger physical
claims remain open, then its “Final Capstone” section again claims that
Tomita–Takesaki cancellation, K-theory classification, and the infinite
hyperfinite continuum limit have been rigorously discharged. No cited local
lemma, finite computation, or colimit declaration by itself proves those
cross-domain physical equivalences. Classification: **RED** documentation-level
semantic promotion and internal status contradiction.

## Fresh local audit: `SPINOR_REP_CROSS_SYSTEM.md` contradicts its own system table

`docs/SPINOR_REP_CROSS_SYSTEM.md:1-5` declares a “COMPLETE FORMALIZATION
ACROSS 8 SYSTEMS” with “NO SORRIES, NO AXIOMS”, but its table at `:13-22`
marks Coq, Isabelle/HOL, and GAlgebra as **Pending/TODO**. The document later
labels all eight systems as verified (`:47`) and assigns cross-system
injectivity/dimension results to them, although the listed Lean source is only
one implementation and no cross-system equivalence theorem is supplied. The
Lean file's existence does not repair the contradiction between “all eight
complete” and three explicitly pending systems. Classification: **RED**.

## Fresh local audit: `OPEN_DEBT_PROBLEMS.md` is materially stale and falsely exhaustive

`docs/OPEN_DEBT_PROBLEMS.md:1-7` claims a clean build and “exactly 2 open gaps”
across `lean/InfoGeometry/`, while asserting that major sectors are fully
closed. This is contradicted by the current checkout: the G₂ audit above
records many unresolved native bridges, and the repository's current lexical
inventory contains far more than two `sorry`/`admit`/`axiom` occurrences
(with comments/tooling requiring separate classification). The document's
“only remaining open sorry declarations” claim at `:25-37` therefore cannot be
current repository evidence. Its anti-wrapper policy at `:41-45` is sound in
principle, but does not repair the stale inventory. Classification: **RED** for
the exhaustive-status claim; **GREEN** for the stated policy principle.

## Fresh local audit: spinor status files contradict each other about completion

`docs/SPINOR_REBUILT_FROM_SCRATCH.md:1-25` declares a complete eight-system
rebuild with no sorries or axioms, while `docs/SpinorRepresentation_STATUS.md:1-29`
declares the same theory only partially formalized and lists the Kronecker,
recursive, block-embedding, and final injectivity proofs as pending. The latter
describes only the `Cl(1,1)` component as complete. The “complete” status
therefore cannot be reconciled with the explicit pending obligations.
Classification: **RED** documentation/status contradiction; the local
`Cl(1,1)` result must be scoped separately from the unproved full tower.

## Fresh local audit: the second attention report conflates independent checks with one physical theorem

`docs/ATTENTION_QUANTUM_FLUID_8_SYSTEM_VERIFICATION.md:1-22` labels the
“Attention = Quantum Fluid Flow” mapping fully verified across eight systems.
Its listed checks are heterogeneous local facts: log-sum-exp derivatives,
matrix traces, Clifford reversal, Weyl-algebra commutators, and skew-adjoint
trace calculations. They are not cross-system equivalence proofs and do not
establish that an attention mechanism is a KMS state or a physical
divergence-free quantum fluid. The report's own “simplification” says the final
fluid consequence requires only skew-adjointness (`:4-6`), which further shows
that it is a generic implication rather than a validated physical identity.
Classification: **RED** for the global title/status; the individual local
algebraic checks remain separately auditable.

## Fresh local audit: Fibonacci anyon report contradicts its own Lean verification count

`docs/FIBONACCI_ANYON_REPORT.md:13-21` claims a complete formal verification
using five Lean theorem files and six SymPy witnesses. Its verification table
later records a qualification that a braid relation requires a specific CFT
conformal-block basis (`:175`), while the summary at `:209-214` reports only
two Lean-verified theorems versus seven SymPy-verified entries. Nevertheless
`:230-233` calls the full Fibonacci anyon algebraic structure completely
formally verified. The report therefore conflates symbolic witnesses,
knowledge-base entries, and Lean proofs, and promotes a partially verified
local packet to the full anyon/CFT theory. Classification: **RED**.

## Fresh local audit: release notes claim end-to-end completion while recording blocked builds and proof holes

`docs/UNIFICATION_RELEASE_NOTES_2026-06-05.md:5-12` says the milestone
completes an end-to-end operator–spinor unification story. Its verification
section (`:45-55`) simultaneously records that `Canonical.All` is blocked by
multiple failures and explicitly names remaining `sorry` placeholders in
`Arithmetic.PrimeSpinorSquareRootBoost`, among other unresolved modules. Clean
builds of two individual owners cannot support the end-to-end completion claim.
Classification: **RED** release-status contradiction.

## Fresh local audit: paper draft promotes theorem-shaped text to completed formalization

`docs/PAPER_DRAFT_GRAND_IDENTITY.md:17-21` claims a proved de Rham class,
modular Hamiltonian flow, and a derived first law, and claims cross-validation
against eight systems.  The contribution list at `:33-37` calls the
formalization complete.  The draft's later verification table at `:199-203`
and checklist at `:286` repeat the no-`sorry`/eight-system/completion claims.
The file is a paper draft and code listing/verification-output placeholder; it
does not provide a kernel-checked bridge from a Boltzmann differential to de
Rham cohomology or to modular flow, nor evidence for the claimed Coq,
Isabelle, Macaulay2, or GAlgebra validations.  The theorem-shaped snippets at
`:132-187` are not, by themselves, evidence that those declarations exist and
compile in the repository.  Classification: **RED** documentation/provenance
overclaim.

## Fresh local audit: generic quadratic lemma is labelled as a concrete G₂(2) theorem

`lean/InfoGeometry/Algebra/Zorn/G2QuadraticCompatibility.lean:181-204`
introduces `IsG2Automorphism` for an arbitrary `R` and arbitrary functions
`(Fin 7 → R) → (Fin 7 → R)`.  The proof of `g2_preserves_quadratic` uses only
the supplied `PreservesBilinear` component.  It does not use octonion
multiplication, the split-octonion carrier, or a native `SplitOctF2Aut`
embedding.  The heading/comment calls this “G₂(2) Automorphism Group
Invariance” and says “Every G₂(2) automorphism”, but the formal theorem is a
generic implication for an ad hoc predicate.  No theorem in this file
identifies that predicate with the native finite automorphism group.
Classification: **ORANGE** generic lemma presented with a stronger concrete
semantic label.

## Fresh local audit: Levi/BN2 owner supplies the decomposition as data, not derives it

`lean/InfoGeometry/Algebra/Zorn/LeviRootDecompositionBN2.lean:7-23` describes a
coordinate-free BN2 deduction and says all proofs are complete.  Its central
`LeviDecompositionData` structure (starting at `:45`) stores
`simple_le_borel`, `complement_le_borel`, and `borel_factorization` as fields.
Thus the advertised Levi decomposition and factorization are assumptions of a
package; the file does not construct them for the native G₂(2) groups.  Any
downstream theorem instantiated with such a package proves a conditional
schema, not the concrete BN2 axiom.  Classification: **ORANGE** conditional
interface overclaimed as a completed structural derivation.

## Fresh local audit: formal Chevalley/Poincaré file is an arithmetic model, not a group-order proof

`lean/InfoGeometry/Algebra/Zorn/G2ChevalleyPoincareCombinatorics.lean:35-64`
defines an inductive six-element root-label type and the numerical functions
`formalUnipotentOrder` and `formalBorelOrder`.  Lines `:86-139` similarly
define a twelve-constructor Weyl-label type and evaluate finite sums and
polynomials by `decide`.  The theorem `formal_bruhat_order_at_two` proves an
identity for these definitions, while `lie_algebra_g2_formula_at_two` proves a
separate arithmetic identity.  There is no native group, root subgroup,
field structure, or Bruhat-cell decomposition connecting the two expressions.
Consequently `bruhat_sum_eq_chevalley_formula` is numerical agreement of two
closed formulas, not a proof of the order of native `G₂(2)`.
Classification: **ORANGE** combinatorial arithmetic promoted to Lie/group
theory.

## Fresh local audit: “exactly 2 open gaps” is contradicted by the current tree

`docs/OPEN_DEBT_PROBLEMS.md:1-8` claims a clean build and exactly two open
`sorry` declarations across `lean/InfoGeometry/`, and presents several large
sectors as 100% proved.  That scope statement is not compatible with the
current checkout: the G₂ audit has found numerous conditional owners and
semantic gaps, while the document itself only inventories literal `sorry`
tokens.  A zero/low `sorry` count cannot establish native carrier alignment,
surjectivity, quotient equivalence, or theorem semantic fidelity.  The phrase
“exhaustive deep-search audit” therefore overstates what its metric checks.
Classification: **RED** audit-scope overclaim.

## Fresh local audit: multi-system verification reports verify projections, not
the advertised theories

`docs/ATTENTION_QUANTUM_FLUID_8_SYSTEM_VERIFICATION.md:1-25` and
`docs/NAVIER_STOKES_LEGENDRE_MULTI_SYSTEM_VERIFICATION.md:1-25` label their
packages “FULLY VERIFIED” across multiple systems.  Their tables list local
symbolic scripts, sketches, and individual Lean files, but do not exhibit a
single common formal statement or equivalence connecting those systems to the
claimed quantum-fluid/Navier–Stokes theories.  The listed checks establish
component calculations such as derivatives, traces, or algebraic identities;
they do not prove the cross-domain synthesis asserted by the headings.
Classification: **ORANGE/RED** cross-system validation overclaim.

## Fresh local audit: staged alignment “certificates” are proof packages, not
derived certificate data

`lean/InfoGeometry/Algebra/Zorn/G2FactorizationAlignmentCertificate.lean:28-49`
defines `FactorizationAlignmentCertificate` and
`ConcreteFactorizationAlignmentCertificate` with `base`, `step`, separation,
residual-alignment, and residual-injectivity as fields.  The theorems
`generic_factorization` and `concrete_factorization` (`:91-107`) merely project
those fields through the generic recursion.  No constructor for either
certificate is supplied in the file.  Likewise,
`G2FlagFactorizationOrientation.lean:97-113` constructs an orientation package
only from an assumed `hsound` theorem.  Therefore these owners do not derive
the missing 189-row alignment; they package it as an input.  Calling such a
package a completed “certificate” without a separately verified constructor
would move the trust boundary, not close it.
Classification: **RED** proof-like structure field / missing-constructor
overclaim.

## Fresh local audit: fiber “surjectivity” is not fiber-orbit transitivity

`lean/InfoGeometry/Algebra/Zorn/G2NativePointStabilizerLineFiber.lean:49-64`
proves that, for a fixed `g : nativePointStabilizer`, the map sending every
native line `L` to `g • L` is surjective.  This follows from the previously
constructed equivalence `nativeLineFiberMap g nativeBasePoint`; it says that a
single automorphism permutes the fiber.  It does **not** prove that the orbit
map `g ↦ g • lineZero`, with `g` varying over the point stabilizer, is
surjective.  The latter is the missing three-line stabilizer transitivity
theorem needed for flag transitivity.  The witness-based theorem at
`:104-125` correctly remains conditional on `hcover`, `hzero`, `hinfinity`,
and `hthird`.  Classification: **RED** naming/semantic inflation if the
former theorem is used as stabilizer orbit transitivity.

## Fresh local audit: `G2GroupOrderReduction` closes only a conditional arithmetic reduction

`lean/InfoGeometry/Algebra/Zorn/G2GroupOrderReduction.lean:7-32` correctly
states that the ambient-order theorem is reduced to the missing quotient
cardinality.  The exported theorem
`nat_card_eq_of_quotient_189` at `:62-69` requires
`Nat.card (SplitOctF2Aut ⧸ sylowTwoSubgroup) = 189`, and
`nat_card_eq_of_equiv_189` at `:72-86` requires an explicit equivalence.
Therefore the file does not prove `Nat.card SplitOctF2Aut = 12096`; it proves
that result conditionally.  Its header nevertheless says “All proofs are
complete” without preserving this distinction in the module-level status.
Classification: **YELLOW** conditional reduction liable to be reported as a
closed group-order theorem.

## Fresh local audit: symbolic BN2 is a reusable specification, not a native BN2 proof

`lean/InfoGeometry/Algebra/Zorn/G2SymbolicBN2.lean:7-19` says it proves the
complete BN2 axiom for G₂(2).  The actual main theorem
`symbolic_bn2_pointwise` at `:80-105` takes a
`ReflectionBN2Spec`; that structure stores `toPC_mem_B`, `toPC_surj`, and both
branch equations as fields (`:43-72`).  No concrete `ReflectionBN2Spec` for
the native `SplitOctF2Aut`/Borel pair is constructed in this file.  The result
is therefore a generic conditional schema, not a native BN2 proof.
Classification: **ORANGE** interface promoted by its header to a concrete
completion.

## Fresh local audit: fiber map surjectivity is not stabilizer-orbit transitivity

`lean/InfoGeometry/Algebra/Zorn/G2NativePointStabilizerLineFiber.lean:49-64`
proves that, for a fixed `g : nativePointStabilizer`, the map sending every
native line `L` to `g • L` is surjective.  This follows from the equivalence
`nativeLineFiberMap g nativeBasePoint`; it says that one automorphism permutes
the fiber.  It does not prove that the orbit map `g ↦ g • lineZero`, with `g`
varying over the point stabilizer, is surjective.  That latter three-line
stabilizer transitivity theorem is still missing.  The witness theorem at
`:104-125` correctly remains conditional on `hcover`, `hzero`, `hinfinity`,
and `hthird`.  Classification: **RED** if the former permutation theorem is
presented as flag/fiber orbit transitivity.

## Fresh local audit: quotient–flag equivalence owner requires the missing
transitivity theorem

`lean/InfoGeometry/Algebra/Zorn/G2QuotientFlagEquiv.lean:19-31` defines
`quotientFlagEquiv` only from
`h_surj : Function.Surjective (fun g : G => g • x)`.  The underlying generic
owner at `G2StructuralFlagQuotient.lean:18-31` is the standard orbit–stabilizer
construction and likewise assumes surjectivity; its concrete action,
transitivity, and stabilizer identification are explicitly described as
remaining obligations at `:8-11`.  Thus the name “G2 Flag Equivalence” does
not establish a native G₂(2) quotient/flag equivalence.  Classification:
**YELLOW** generic theorem, **RED** if promoted as the missing concrete
189-flag quotient bridge.

## Fresh local audit: native ordered root products stop at an image, not the
positive-root subgroup

`lean/InfoGeometry/Algebra/Zorn/G2NativeOrderedRootProduct.lean:7-31` and
`G2NativePositiveRootSubgroupSystem.lean:72-126` prove injectivity of the
six-bit ordered product, membership in `positiveRootSubgroup`, and that its
range has cardinality 64.  The module comments explicitly decline to prove
range equality.  The `System` structure in the latter file stores the
individual root axioms but has no product-generation or surjectivity field.
Thus the statements establish a 64-element native image contained in the
declared subgroup, not a classification of that subgroup or a Chevalley
root-product parametrization.  Classification: **GREEN** for the stated
image results, **RED** for any downstream claim of subgroup equality.

## Fresh local audit: Peirce parabolic order and stabilizer equality remain
conditional

`lean/InfoGeometry/Algebra/Zorn/G2PeirceParabolicStabilizer.lean:7-19`
describes a parabolic subgroup of order 192 and a completed stabilizer
identification.  The actual equality theorem at `:104-110` requires the
unproved-in-this-file rigidity hypothesis
`h_peirce_rigidity`; the cardinality theorem at `:117-128` additionally
requires `h_parabolic_card : Nat.card (...) = 192`, as well as the frame-fixing
hypotheses.  The later fiber theorem at `:437-444` requires a transitivity
hypothesis.  These are valid conditional interfaces, but no native proof of
the rigidity, order, or parabolic fiber transitivity is supplied here.
Classification: **ORANGE** conditional parabolic package reported by its
module header as a completed concrete stabilizer/order theorem.

## Fresh local audit: Bruhat peeling is conditional on the missing local
peeling axiom

`lean/InfoGeometry/Algebra/Zorn/BruhatPeelingTransport.lean:7-25` advertises
general double-coset decomposition without brute force.  Its definitions and
theorems are generic over a group and a subgroup; the induction consumes a
`HasPeelingStep` hypothesis for the relevant generators.  The file does not
derive that hypothesis from the native G₂(2) multiplication or prove the
required concrete BN pair.  Thus its structural induction is valid as an
abstract transport theorem but cannot certify the native Bruhat corridor by
itself.  Classification: **YELLOW/ORANGE** conditional infrastructure whose
scope must not be reported as concrete Bruhat completion.

## Current G₂ corridor status snapshot (non-final)

```text
GREEN   native PC multiplication/recovery; 63-point action; selected row
        matrix readbacks; longest residual equivalence; stated image
        injectivity/cardinality lemmas
YELLOW  order reductions, fiber/cardinality transports, abstract finite
        equivalences, generic Bruhat peeling
ORANGE  arithmetic Chevalley/Poincaré models; generic BN2/Levi specs;
        quadratic invariance with concrete G₂(2) labels; conditional
        parabolic packages
RED     full 189-row factorization; global orientation normalization;
        quotient coverage/equivalence; flag transitivity; native BN pair;
        intermediate residual exponent equivalences; native subgroup
        classifications inferred from image cardinalities
```

This is an evidence index, not a completion claim.  The remaining audit work
is to reconcile every public completion/status document and every downstream
import that promotes a YELLOW/ORANGE/RED owner, then run the relevant narrow
Lean checks without modifying dirty user files.

## Fresh automated audit: semantic-vacuity gate quantifies the staged risk

Running `python3 tools/quality/semantic_vacuity_gate.py
lean/InfoGeometry/Algebra/Zorn --top 120` on the current checkout reported
`semantic_vacuity: 289`, with `error: 2` and `warning: 287`.  The two errors
are `FactorizationAlignmentCertificate` and
`ConcreteFactorizationAlignmentCertificate`, both classified as
`pure_proof_carrier`.  The same run reports 70 `proof_like_field_type`
warnings, including the factorization certificate fields and the generic
root-system/BN interfaces.  This tool is diagnostic rather than a proof of
falsehood, but it independently confirms that several staged “certificate”
owners contain obligations as fields rather than derived native data.
Classification: **RED** for those two proof-carrier owners; the remaining
warnings require owner-by-owner semantic review.

## Fresh local audit: `G2FiniteChevalleyGroupBridge` is not a split-octonion
automorphism theorem

`lean/InfoGeometry/Algebra/Zorn/G2FiniteChevalleyGroupBridge.lean:10-21`
labels the module as `G₂(2) = Aut(𝕆_s(𝔽₂))`, but its only carrier is
`FiniteAut O` for an arbitrary `[Ring O]` (`:32-40`).  The structure records
preservation of `1`, `*`, and `+`; it contains no split-octonion multiplication
or native `SplitOctF2Aut` map.  Its “exact order” theorems at `:121-147` are
identities for constants defined as `12096`, `6048`, and `5616`, including
`rfl` proofs.  They do not compute the cardinality of `FiniteAut O` or the
native automorphism carrier.  Since split octonions are nonassociative, the
generic `[Ring O]` interface is not the stated octonion carrier.
Classification: **RED** concrete-group/order overclaim.

## Fresh local audit: full-looking GAP payload has subgroup-membership proofs,
not row soundness proofs

`lean/InfoGeometry/Algebra/Zorn/G2GAPFlagWitnessData.lean:5-18` honestly says
that `gapLeftWitness` and `gapRightWitness` are data only.  The definitions
contain the exported pattern rows and a `(_, _) => []` default; a direct count
of the pattern branches gives 190 branches including that default in each
table.  The only theorems at `:403-412` prove that `collect` of either table
entry lies in `unipotentSubgroup`.  There is no theorem here proving that the
payload factors `flagRepresentative i`, no orientation readback, and no
quotient equality.  Thus the payload may be complete as exported data, but it
is not a completed Lean certificate; promoting its presence or subgroup
membership lemmas to 189-row soundness is unsupported.  Classification:
**YELLOW** data layer, **RED** if advertised as verified row alignment.

## Fresh local audit: Rosetta Stone document contradicts its own limitation section

`docs/THE_ROSETTA_STONE.md:93-109` correctly states that the repository does
not prove a full Bloch-bundle theorem, insulator classification, edge-mode
theorem, or global spacetime duality.  The same document then declares at
`:113-121` that closure debt is discharged, claims a complete topological
theorem, asserts a hyperfinite-II₁/continuum renormalization formalization,
and concludes that the information paradox is resolved.  The listed owners
are finite projective or categorical packets and do not supply those global
physical equivalences.  This is an internal documentation contradiction,
not merely an omitted caveat.  Classification: **RED** capstone overclaim.

## Explicit self-correction: claims previously overpromoted in this thread

The earlier conversational status reports incorrectly promoted several
conditional or partial interfaces to completed results.  The corrections are:

```text
“full 189-row certificate”       → GAP payload plus selected readbacks only
“global U·W·U factorization”     → absent; row (4,18) has reversed order
“Bruhat coverage/equivalence”    → conditional on hcell/enum/surjectivity
“flag transitivity”              → point action exists; line-orbit step is open
“stabilizer equality”            → native U ≤ Stab only; equality is conditional
“generic residual equivalence”   → false at (2,true): 8 versus 32
“native BN pair”                 → generic/specification interfaces only
“|SplitOctF2Aut| = 12096”       → arithmetic identity or conditional reduction
“full real adjoint character”    → finite permutation character/partial transport
“zero-debt/full verification”   → contradicted by open-debt and vacuity evidence
```

These are corrections to the assistant's prior claims, not claims that Lean
accepted false propositions.  Lean checked narrower statements; the failure
was semantic reporting and provenance discipline.
