# G₂ semantic audit addendum — 2026-08-26

This addendum records verified findings from the current checkout.  It does
not promote names, comments, CAS payloads, or conditional interfaces into
mathematical results.

## Direct findings

| Owner | Evidence | Classification |
|---|---|---|
| `G2FlagCellWitnessCertificate.lean` | `leftWitness` and `rightWitness` are definitions of 189-row data; the file states that carrier alignment with `flagRepresentative` is missing. | ORANGE: data only |
| `G2FlagCellWitnessSoundness.lean` | Exact matrix/readback rows exist only for `(0,0)`, `(1,24)`, and `(4,6)`. | YELLOW: selected rows |
| `G2FlagCellQuotientWitness.lean` | Concrete quotient witnesses exist for selected rows `(1,45)`, `(1,73)`, `(1,178)`, `(4,18)`, plus `hcell_one` and anchors. | YELLOW: partial coverage |
| `G2CellFactorizationCertificate.lean` | `sound` is a structure field whose type is the desired factorization theorem. | ORANGE: assumed proof authority |
| `G2FactorizationAlignmentCertificate.lean` | `base`, `step`, `separation`, `residual_alignment`, and `residual_injective` are all fields; the semantic vacuity gate reports 16 findings, including two `pure_proof_carrier` errors. | RED: proxy/proof package |
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
exported declarations.  The active owner proves matrix readbacks and selected
entries, but not the advertised complete carrier multiplication identity.

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

## Correction to this audit

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
