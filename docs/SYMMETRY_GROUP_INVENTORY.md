# Symmetry and Group Inventory

This inventory covers current Lean sources under `lean/`, inspected non-Lean
mathematical sources, and searched external Lean source trees under
`external_refs/`. A file-name scan is useful
for navigation but does not establish a group construction. The entries below
identify source owners whose declarations define a group, group action,
presentation, representation, or symmetry law. The list is a source map; a
module name alone is not a claim that every statement in it has been
kernel-checked. The root-pinned `GeometricReflectionOperators` owner and its
exponent-three noncommuting-pair theorem passed the focused locked build on
2026-10-29.

The classification is operator-first: scalar or commutative parameter models
are not promoted as separate symmetry families. Where a family has a genuine
noncommutative operator realization, the inventory names that carrier and its
proved action/automorphism laws, and records any missing representation or
intertwining theorem explicitly.

**Mandatory operator-carrier requirement.** Scalar subgroups, diagonal matrix
families, commutative parameter groups, and bare coordinate permutation models
do not satisfy a requested symmetry realization when the intended object is a
noncommutative operator group. The deliverable must include the actual
endomorphism-unit, Clifford, Fock, root-operator, or algebra-automorphism
carrier and a proved action there. A coordinate model may supply inputs or
readouts, but it does not count as a completed replacement. Existing
coordinate-only results identified below are migration debt, not completed
operator realizations. Any unported exceptional family is an open gap; it must
not be filled by a scalar or commutative proxy.

The tracked checkout contains 26,158 Lean source files under `lean/` by
`git ls-files` (recounted 2026-10-30). A normal visible `rg --files` scan sees
26,047 of those Lean sources, so the earlier visible-only counts are superseded
here. A tracked-source declaration-name scan finds 1,391 group/action/symmetry/
aut/iso/transform candidates across 960 files. A tracked-source carrier scan
finds 5,142 matching lines across 1,154 files containing `Subgroup`,
`GroupHom`, `MonoidHom`, `MulAction`, `MulEquiv`, `Equiv.Perm`,
`LieSubalgebra`, `WeylGroup`, `RootSystem`, or `Representation`. The broader
group-structure scan finds 1,366 files containing group/action carriers and
operations. These are high-recall navigation candidates rather than a
semantic theorem count: they include helper lemmas and assumptions, and can
miss unconventional names. The owner-family table below maps the main
mathematical families; a complete declaration-by-declaration semantic
classification remains to be done.

The current root import closure was rechecked on 2026-10-30: the locked
`InfoGeometry.All` build passed (28,248 jobs, exit code 0), including both
Cantor and exceptional CFSG umbrellas and the new root-height descent port.
`InfoGeometry.Audit` reported zero
declarations depending on `sorryAx` and 303 generated explicit axiom
constants, so this is import/build evidence rather than a claim that the full
repository is axiom-clean or that every candidate row is kernel-audited.

The tracked-source scans use `git grep` so hidden but tracked Lean sources are
included. The reproducible candidate scans use these patterns:

```bash
git grep -n -P '^\s*(?:@[[:alnum:]_. ]+\s*)*(?:noncomputable\s+)?(?:def|abbrev|structure|class)\s+[A-Za-z0-9_.]*(?:Group|Symmetry|Action|Aut|Iso|Transform)\b' -- lean
git grep -n -P '\b(Subgroup|GroupHom|MonoidHom|MulAction|MulEquiv|Equiv\.Perm|LieSubalgebra|WeylGroup|RootSystem|Representation)\b' -- lean
git grep -l -P '(^|\s)(Group|GroupWithZero|AddGroup|LieGroup|LieAlgebra|LieSubalgebra|MulAction|SMul)\b|\b(Subgroup|GroupHom|MulEquiv|Equiv\.Perm|WeylGroup|RootSystem)\b' -- lean
```

The focused carrier scan currently finds 491 same-line declaration candidates
and has 72 indexed continuation-line candidates. Its regex can match a carrier
in a parameter type as well as in a result type, so these are navigation hits,
not a count of actual group-valued declarations. The candidate index is stored in
[SYMMETRY_GROUP_CARRIER_DECLARATIONS.txt](SYMMETRY_GROUP_CARRIER_DECLARATIONS.txt)
and has 562 rows across 339 owner files.
Some continuation-line entries annotate the carrier so readers can distinguish
group-valued declarations from maps and actions. This remains a candidate
index: inferred instances and aliases can be missed, while generic subgroups,
maps, actions, and Lie subalgebras are not necessarily distinct global symmetry
groups. Recreate the same-line portion with:

```bash
rg -n --glob '*.lean' '^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+[A-Za-z0-9_]+\s*[^\n]*:\s*(?:Subgroup|LieSubalgebra|Equiv\.Perm|MulAction|MulEquiv|Group|LieGroup)' lean
```

Every one of the 339 indexed owner files is now cited by exact repository
relative path in this inventory. This is path citation coverage, not a
declaration-by-declaration semantic audit. Multiple rows from an owner remain
separate declarations, not separate global symmetry families. The index is
navigation evidence, not evidence that every indexed declaration is a distinct
symmetry group. The
43-owner result-type filter for `Matrix`,
`Module.End`, `CliffordAlgebra`, or `LieSubalgebra`. The 43 owners are now
cited in the operator/Lie review above; their downstream consumers and any
induced global groups still require declaration-level tracing. This result is
distinct from the separately reported 34-file source-index filter.

These outputs are broad candidate sets: they include lemmas and assumptions,
and can miss groups with unconventional names or implicit carriers. The current
source tree, not the DAG index, is the scan basis.

### Classification of the additional indexed owners

The following source owners were added by the multiline-result scan or by the
expanded carrier index. Their declarations were read in the Lean sources; the
classifications describe the declaration's carrier, not a claim that every
dependent theorem has been rebuilt in this pass.

| Role | Owner files and source-level classification |
|---|---|
| Genuine subgroup or group action | `InfoGeometry/Canonical/Cl11SplitQuaternionMobiusBridge.lean`: split-null conjugation stabilizer in `GL₂(ℝ)`; `Canonical/NonAbelianDihedralSymmetry12.lean`: order-12 dihedral action on chiral Zorn algebra automorphisms and its generated subgroup; `Clifford/Cl55WittNativeCartanDieudonne.lean`: subgroup generated by native quadratic reflections; `Exceptional/CFSGPort/J1GeneratorOrders.lean`: private subgroups generated by the two J₁ seed units; `Algebra/Zorn/G2ImaginaryOctImBridge.lean` and `Algebra/Zorn/G2NativeFullFlagAction.lean`: permutation actions of the split-octonion automorphism group on points and flags; `Cantor/SimpleCantorOperatorGroup.lean`: faithful operator-unit image of the simple Cantor permutation group on the endomorphisms of the function module (an operator representation, not the Clifford Markov channel); `Categorical/LogJordanBraidGroupInfRepresentation.lean`: finite-stage readback subgroup of a braid group; `EmergentVacuum/KreinMetricStabilizer.lean`: metric and special-metric stabilizers in a general-linear group; `ProjectiveFoundation/RealProjectiveDescent.lean`: action of a center quotient through a permutation representation; `Omega/Folding/BinFoldGaugeDecomposition.lean`: fiber-preserving permutation subtype, with an actual subgroup and faithful operator-unit image added in `Omega/Folding/BinFoldGaugeOperator.lean`; `Omega/RatioResultant/RatioFieldFullSymmetric.lean`: faithful root-label permutation operators in the endomorphism-unit group, with adjacent transpositions proved noncommuting; this is not identified with a field Galois group. |
| Actual permutation representations or actions, not additional named groups | `Exceptional/G2ArtinKleinBridge.lean`: Klein-group representation on G₂ root labels and conjugation action; `Exceptional/G2CyclotomicCoordinateActionBridge.lean`: transported root permutations and dihedral coordinate action; `Lie/CanonicalZornG2RootStarAction.lean`: Weyl-group action on the finite root carrier; `Topology/KleinBottleCliffordGlide.lean`: presented Klein-group action on the cover–Clifford carrier; `Twistor/Cl55CelestialDeckPhaseMonodromy.lean`: sign/monodromy representations; `Categorical/SylvesterBraidRepresentation.lean`: braid-group representations by permutations of phased states; `Omega/OperatorAlgebra/FoldLiftGlobalSignFactorization.lean`: induced visible/hidden fiber permutation signs; `Omega/Zeta/XiTerminalZmLeyangPerronP3InertiaPointStabilizer.lean`: explicit S₄ permutations used as generators. |
| Lie algebras or infinitesimal stabilizers, not global groups by themselves | `Algebra/SplitAlbertInnerTraceSpan.lean`: trace-zero derivation Lie subalgebra; `Algebra/TrilinearStabilizer.lean`: infinitesimal stabilizer of a trilinear form; `Canonical/CanonicalZornPhaseBridge.lean`: phase-preserving and polarized-phase derivation Lie subalgebras; `Canonical/SplitOctonionJordanStructure.lean`: structure-action Lie subalgebra in endomorphisms; `Canonical/SplitOctonionSymplecticLieAlgebra.lean`: symplectic Lie subalgebra; `Canonical/SplitOctonionTKK55.lean`: hyperbolic-skew Lie subalgebra; `Canonical/SuperUnified.lean`: bosonic structure Lie algebra; `Exceptional/FreudenthalChargeLinear.lean`: symplectic-operator Lie subalgebra; `Exceptional/TrialityContactCantor.lean`: fixed Lie subalgebra; `Krein/DoubledSpace.lean` and `Krein/Metric.lean`: infinitesimal Krein/neutral isometry Lie subalgebras; `Lie/GenericSplitOrthogonalBlocks.lean`: split-orthogonal Lie subalgebra; `Lie/SplitOctonionAxialCartanErlangen.lean`: axial-Cartan derivation Lie subalgebra; `Lie/SplitOctonionDerivationWittBlockRealization.lean`: transported derivation Lie subalgebra; `Lie/SplitOctonionWittSkewEndomorphismSubalgebra.lean`: neutral-Witt skew endomorphisms. |
| Carrier maps or predicates, not independent symmetry groups | `Categorical/LogJordanBraidGroupInfRepresentation.lean` also contains the braid homomorphism feeding the readback subgroup; `Omega/RatioResultant/RatioFieldFullSymmetric.lean` also contains irreducibility/completeness predicates; `Omega/OperatorAlgebra/FoldLiftGlobalSignFactorization.lean` contains sign readouts; these are recorded at the actual target carrier and not counted again as groups. |

The companion `Exceptional/CFSGPort/CurtisTitsRankOneBruhat.lean` now proves
two-cell Bruhat coverage for every element of each rank-one operator subgroup,
using positive/negative-root generation and proved Weyl multiplication laws.
The public CFSG umbrella passes its locked build (8,969 jobs, 2026-10-30).
This closes local rank-one coverage, not the higher-rank exceptional-family
simplicity proofs. The theorem and its concrete operator instance have only
the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies.

`Exceptional/CFSGPort/CurtisTitsRankOne.lean` now records the simple-root
rank-one subgroup and simple-root torus as subgroups of units in
`Module.End K (RootModule τ K)`. The local `OperatorRankOneRels` realization
and the positive/negative root-operator torus conjugation laws are kernel-
checked on that noncommutative carrier. This is rank-one exceptional Lie
symmetry data; it does not establish the Bruhat two-cell decomposition or
simplicity of any finite exceptional group. The focused owner target
`InfoGeometry.Exceptional.CFSGPort.CurtisTitsRankOne` passed its locked build
on 2026-10-30 (8,948 jobs).

`InfoGeometry/Canonical/AQLInstanceMigration.lean` previously called a
three-field record of a group name, dimension, and containing-group string
`SymmetryGroup`. It had no group operations or action, so it was renamed to
`SymmetryGroupMetadata`; `su3_color_metadata` remains schema data and is not
counted as an SU(3) carrier or an SU(3) subgroup of G₂. The related
`Algebra/Zorn/G2TrifactorSU3.lean` source explicitly says its finite projector
results do not identify an OP-stabilizer with SU(3). That operator-group
identification remains a separate proof gap.

The non-Lean AQL source has the same distinction. In
`tools/infra/aql/aql_functorial_bridge.py`, `SymmetryGroupMetadata` stores a
name, dimension, and description in the `symmetry_groups` collection; it has
no multiplication, inverse, membership law, or action implementation. The
schema in `tools/infra/aql/su3_color_gauge_schema.aql` likewise types its
entities and query as `SymmetryGroupMetadata`. Its `stabilizes` field and the
four Mersenne-to-E₈/Spin(8)-triality mapping records are descriptive claims,
not executable group actions or Lean proofs. These metadata records are not
counted as additional symmetry groups; the corresponding Lean operator,
automorphism, and root-system owners are inventoried separately.

`InfoGeometry/Probability/HomologicalProbability.lean` also had a nominal
`FiveGradedSymmetryGroup` that accepted arbitrary multiplication, identity,
and action functions without group or action laws, and represented its
structure subgroup as a set. It now requires an actual `Group Sym`, a
`MulAction Sym X`, and a `Subgroup Sym`. Its `AffineClosure` interface also
uses typeclass group actions on the open and compactified carriers. This
repairs the generic carrier contract; the owner still supplies no concrete
noncommutative operator-group instance, so it is not counted as an instantiated
symmetry family.

`InfoGeometry/Topology/WallpaperSymmetry.lean` now realizes the concrete
`pg` glide and transverse translation as units in the endomorphism algebra of
real lattice functions. The representation of lattice permutations is proved
faithful, and the two generators are proved noncommuting in their generated
operator subgroup. The generic `WallpaperGroupPG` record remains relation
data; the operator-group result uses the concrete maps `G` and `T_y`. The
owner and `InfoGeometry.Topology.All` both pass locked Lean/Lake checks
(9,582 Lake jobs for the umbrella).

`Cantor/SimpleCantorOperatorGroup.lean` faithfully represents the simple
Cantor permutation group by units in the endomorphism algebra of real-valued
functions and now proves an explicit noncommuting pair: the finite-prefix
associator and first-coordinate flip. The resulting operator group meets the
noncommutativity criterion. Its connection to the requested Clifford/Fock
operator realization remains open.
`Cantor/SimpleCantorFiniteModeBridge.lean` now places every two-coordinate
first-bit prefix transposition in that same simple Cantor permutation group,
using the OAI finite-table group and Cantor-pairing transport. This connects
the *form* of finite transpositions to elements of the simple Cantor group,
but does not yet embed `Equiv.Perm (Fin n)` or identify its action with the
finite-mode Clifford/Fock action. The indices of the Cantor coordinate swaps
are `ℕ`, and the owner proves membership one swap at a time; it does not define
the needed homomorphism from a finite mode-permutation group. The owner is
imported by `InfoGeometry.Cantor.All`, whose locked Lake build passed on
2026-10-30 (9,001 jobs). A permutation-carrier homomorphism and an intertwiner
between the resulting operator representations remain unproved.
`Cantor/SimpleCantorOperatorGroup.lean` now lifts each such transposition
through the faithful simple-group representation to a unit in the actual
endomorphism-operator image and states its inverse-reindexing action on
Cantor-word functions. The owner passed a locked build on 2026-10-30 (8,931
jobs). This operator lift is on the real-valued Cantor-function module; it
does not identify that representation with the finite Fock Clifford action.
`RootSystem/D4CantorWeylAction.lean` now gives the D₄ Weyl group an operator-unit
representation on real-valued Cantor-word states and identifies its operator
image subgroup. The representation is faithful, and adjacent simple
reflections are proved noncommuting first on the D₄ lattice and then in the
operator image. The owner passes a locked Lean check. The separate exceptional
root operator realization acts on functions over the root-coordinate lattice;
these carriers must not be conflated. `Cantor/CantorRandomWalk.lean` supplies
Cantor bit-sequence and coordinate-flip data, not by itself a Markov operator
or a symmetry-group realization. The finite-mode construction in
`Clifford/ClNNPermutationSymmetry.lean` provides genuine Clifford-algebra
automorphisms, Fock symmetries by conjugation on `Module.End`, and weighted
channels on that noncommutative operator algebra. A kernel-checked theorem
realizes every finite bistochastic matrix on the represented primal creation
operator family via inverse-reindexed Birkhoff weights. The matrix remains a
coefficient readout, while the channel carrier is the Fock endomorphism
algebra. `Cantor/CliffordMarkovOperators.lean` now also proves
`fockPermutation_conj_cantorMode` and `randomFockAverage_cantorMode`: the finite
Fock symmetry closure permutes the represented Cantor Clifford operators by
conjugation, and the Birkhoff channel acts by their weighted permuted sum. The
remaining bridge is from the infinite Cantor random walk or simple Cantor
group to the finite-stage Fock carrier and its direct-limit inclusions. Until
that bridge is proved, the Cantor-wide Clifford/Markov symmetry realization
remains open.
The subsystem umbrellas `InfoGeometry.RootSystem.All` and
`InfoGeometry.Cantor.All`, including the exceptional root-lattice operator
noncommutativity, D₄ Cantor-word operator representation, and finite-mode
Clifford Markov owners, both pass the locked Lake build (9,030 jobs).

### Operator/Lie carrier review

The top-level result declarations in the previously uncited operator/Lie
candidate paths were checked by their owner declarations. Two define actual
subgroup actions on noncommutative carriers: `TwistorInternalSymmetry` gives
`kinematicStabilizer ≤ Equiv.Perm (Packet ι)`, and
`SplitOctonionEllStabilizer` gives `realZornEllStabilizer` as a subgroup of
real Zorn composition automorphisms. The latter file also defines ordered
chiral-pair and quaternionic-slice stabilizers.

Most remaining indexed declarations return `LieSubalgebra` inside actual
endomorphism, matrix, or Clifford algebras. They describe infinitesimal
symmetries and commutator closure, not global groups by themselves. The
reviewed carriers include split orthogonal/O(5,5), canonical Zorn derivations
and Peirce stabilizers, H3(Zorn) derivations and cubic stabilizers,
Clifford-CAR quadratic sectors, split-Clifford orthogonal closures, the G2
spinor operator carrier, and affine Kac-Moody finite-mode closure. Ideal
restriction, KKS restriction, TKK SU(2)/SU(3) predicates, and retained Lie
closure are support or predicate declarations. Diagonal triality and
hyperbolic-diagonal O(5,5) owners are explicitly excluded from the
symmetry-group count.

The reviewed owner files are `InfoGeometry/Orthogonal/O55WittRootRepresentation.lean`,
`InfoGeometry/Orthogonal/O55RealWittForm.lean`,
`InfoGeometry/Orthogonal/O55ContactLie.lean`,
`InfoGeometry/Lie/CanonicalZornPeirceStabilizer.lean`,
`InfoGeometry/Core/SymmetricLie.lean`,
`InfoGeometry/Lie/SO55MatrixLieSubalgebra.lean`,
`InfoGeometry/Lie/ZornPeirceDerivationStabilizer.lean`,
`InfoGeometry/Lie/CanonicalZornDerivation.lean`,
`InfoGeometry/Lie/SplitOctonionEllStabilizer.lean`,
`InfoGeometry/Lie/CanonicalZornIdealWeightDecomposition.lean`,
`InfoGeometry/Twistor/TwistorInternalSymmetry.lean`,
`InfoGeometry/Clifford/Cl55OperatorLieSubalgebra.lean`,
`InfoGeometry/OperatorAlgebra/OperatorDefectCompletion.lean`,
`InfoGeometry/Clifford/CliffordLieAlgebra.lean`,
`InfoGeometry/Exceptional/DiagonalCompositionTriality.lean`,
`InfoGeometry/OperatorAlgebra/CliffordCARQuadraticClosure.lean`,
`InfoGeometry/Algebra/H3ZornInfinitesimalReconstruction.lean`,
`InfoGeometry/External/Auto/TKK_StandardModel.lean`,
`InfoGeometry/Algebra/SplitAlbertStructureOperators.lean`,
`InfoGeometry/Algebra/NonAssocDerivation.lean`,
`InfoGeometry/Algebra/F4Derivations.lean`,
`InfoGeometry/Algebra/BaezF4H3Zorn.lean`,
`InfoGeometry/Algebra/SpecialUnitary.lean`,
`InfoGeometry/Algebra/SplitMetricLieAlgebra.lean`,
`InfoGeometry/Algebra/H3ZornCubicOperatorGeometry.lean`,
`InfoGeometry/Algebra/Clifford55GaugeSubalgebraBridge.lean`,
`InfoGeometry/Algebra/Zorn/CanonicalDerivationBridge.lean`,
`InfoGeometry/Canonical/SO55RestrictedBivectorEquiv.lean`,
`InfoGeometry/Canonical/G2Cl55ChiralHodgeEquivarianceBridge.lean`,
`InfoGeometry/Canonical/Cl55WittOrthogonalHierarchy.lean`,
`InfoGeometry/Canonical/CanonicalZornG2SimpleRootSL2Bridge.lean`,
`InfoGeometry/Canonical/SouriauKKSLeafRestriction.lean`,
`InfoGeometry/Canonical/HyperbolicDiagonalO55.lean`,
`InfoGeometry/Canonical/Cl55WittFullLieClosure.lean`,
`InfoGeometry/Canonical/LorentzSelfDualLieAlgebra.lean`,
`InfoGeometry/Canonical/SpinorialCore/BilinearDerivations.lean`,
`InfoGeometry/Canonical/PionChiralGoldstoneNative.lean`,
`InfoGeometry/Canonical/AffineKacMoodyColimitBracket.lean`,
`InfoGeometry/Canonical/G2H3ZornEntrywiseEmbedding.lean`,
`InfoGeometry/Canonical/SL2FiveGradingExample.lean`,
`InfoGeometry/Canonical/CanonicalZornG2SL3TriFactorBridge.lean`,
`InfoGeometry/Canonical/O55OrthogonalLieCarrier.lean`, and
`InfoGeometry/Canonical/Cl55WittLieSubalgebra.lean`.

The additional Clifford carrier owners refine the Pin/orthogonal row above.
They define one shared `realSplitPin55` subgroup in `Cl55ˣ`, its sign kernel,
the native orthogonal group on the actual Witt space, generated reflection
subgroups and determinant-sign subgroups, and the image of the corrected
split-Pin action. `Clifford55.lean` exposes Mathlib's Lipschitz group in the
same Clifford-unit carrier. `TodorovInternalSpace.lean` defines linear
centralizers and stabilizers on its spinor space. The S₃ and generation-label
owners provide induced actions, not extra Clifford symmetry groups. Sources:
`InfoGeometry/Clifford/Cl55RealSplitPinKernelExact.lean`,
`InfoGeometry/Clifford/Cl44S3Family.lean`,
`InfoGeometry/Clifford/Cl55WittPinKernel.lean`,
`InfoGeometry/Clifford/Cl55RealSplitPin.lean`,
`InfoGeometry/Clifford/Cl55WittReflectionSubgroup.lean`,
`InfoGeometry/Clifford/Cl44GenerationRotation.lean`,
`InfoGeometry/Clifford/TodorovInternalSpace.lean`,
`InfoGeometry/Clifford/Cl55WittNegativeVectorPin.lean`,
`InfoGeometry/Clifford/Cl55RealSplitPinImage.lean`,
`InfoGeometry/Clifford/Cl55WittReflectionWordDeterminant.lean`,
`InfoGeometry/Clifford/Cl55WittReflectionGeneratedSubgroup.lean`,
`InfoGeometry/Clifford/Clifford55.lean`,
`InfoGeometry/Clifford/Cl44S3CopyModel.lean`,
`InfoGeometry/Clifford/Cl55RealSplitPinReflectionImage.lean`,
`InfoGeometry/Clifford/Cl55WittOrthogonalDeterminantSign.lean`, and
`InfoGeometry/Clifford/Cl55SpinorChirality.lean`.

The additional Omega carrier-index owners were also separated by carrier
type. `fiberPermutationSubgroup` and `q6PointStabilizer` are actual subgroups
of finite permutation groups; `s4HurwitzRepresentativeMonodromy` is the
concrete S₄ subgroup generated by its named permutations. The POM moment,
tensor, orbit, and boundary files mainly define permutation actions or
relabelings of data, rather than new groups. The `squareUnitsSubgroup571`
owner is a subgroup of units of the commutative ring `ZMod 571`; it is an
arithmetic candidate and is not used as a substitute for any noncommutative
operator symmetry. Generic quotient and invariant predicates parameterized
by `CommGroup` are recorded as such, not promoted to operator-group results.
The audited source paths are `Omega/POM/FractranCommutativeVsAlgorithmicExternalization.lean`,
`Omega/POM/ToggleScanLCMTensorization.lean`,
`Omega/POM/MomqPermutationSymmetry.lean`, `Omega/POM/S3OrbitDecomposition.lean`,
`Omega/GroupUnification/BdryS3ToS2BreakingByGeoAxis.lean`,
`Omega/GroupUnification/Foldbin6GeoStabilizerZ2.lean`,
`Omega/GroupUnification/Window6Delta34GeneratesSquares.lean`,
`Omega/Zeta/XiTerminalZmLeyangMonodromyS4.lean`,
`Omega/Zeta/XiTerminalZmPuiseuxInfty4cycle.lean`,
`Omega/CircleDimension/S4HurwitzConjugacySingleOrbit.lean`,
`Omega/Zeta/XiTerminalZmS3RootRecoveryCoordinateAutomorphisms.lean`,
`Omega/SyncKernelWeighted/RealInput40BFKTheory.lean`,
`Omega/EA/FoldGroupoidZ2x2SectorByOrientation.lean`,
`Omega/POM/BlockConsistencyRateBlockReduction.lean`,
`Omega/GU/BdryZ2JumpUniqueness.lean`, `Omega/Folding/BinFoldGaugeSign.lean`,
`Omega/GU/TerminalWindow6Q6RootFieldPrimitiveNonsolvable.lean`,
`Omega/Conclusion/SoftcoreKroneckerSympowerDecomposition.lean`,
`Omega/OperatorAlgebra/FoldEquivalenceAutSemidir.lean`,
`Omega/GU/GroupJGPrimeRegisterPhaseBohrDense.lean`,
`Omega/GU/FibTailP23S3ActionOnOrbitQuotient.lean`,
`Omega/GU/GroupJGEllipticTwoScaleMahlerMultiplicative.lean`,
`Omega/GU/Window6Z2Z3ToZ6Readout.lean`,
`Omega/Conclusion/PrimitiveMinimalCarrierQuotient.lean`,
`Omega/POM/MomentSymmetricPower.lean`,
`Omega/Conclusion/ArtinDeterminantMinimalVisibleQuotient.lean`,
`Omega/Conclusion/Window6CanonicalMicrostateBoundaryCharacterCollapse.lean`,
`Omega/Conclusion/MonoidalJumpA2TorsionClassification.lean`,
`Omega/Conclusion/PrimeAdjunctionExactMultiplicativeBudget.lean`,
`Omega/Conclusion/LocalizedAnomalyPairwiseSkeletonDeterminesSpectrum.lean`, and
`Omega/Conclusion/LeyangOffdiagonalTranspositionQuotient.lean`.

The broad candidate index currently contains 11,612 `path:line:source`
entries across 3,395 files in
[SYMMETRY_GROUP_CANDIDATES.txt](SYMMETRY_GROUP_CANDIDATES.txt), regenerated
against the current Lean source tree. A separate, narrower union scan using
only the carrier and named-declaration patterns reports 7,334 entries. This
is a distinct query scope, not a competing count for the broader scan. Its
reproducible command is:

```bash
rg -n --glob '*.lean' '\b(Subgroup|GroupHom|MonoidHom|MulAction|MulEquiv|Equiv\.Perm|LieSubalgebra|WeylGroup|RootSystem|Representation)\b|^\s*(?:@[[:alnum:]_. ]+\s*)?(?:noncomputable\s+)?(?:def|abbrev|structure|class)\s+[[:alnum:]_.]*(Group|Symmetry|Action|Aut|Iso|Transform)' lean
```
It is a high-recall review index, not a list of distinct groups: many rows
are uses, lemmas, generic representation statements, or assumptions.
The exact command used to produce it was:

```bash
rg -n --glob '*.lean' '\b(Group|GroupWithZero|AddGroup|LieGroup|LieAlgebra|LieSubalgebra|MulAction|SMul|Subgroup|GroupHom|MonoidHom|MulEquiv|Equiv\.Perm|WeylGroup|RootSystem|Representation|MulAut|AddAut)\b|^\s*(?:@[[:alnum:]_. ]+\s*)?(?:noncomputable\s+)?(?:def|abbrev|structure|class)\s+[[:alnum:]_.]*(Group|Symmetry|Action|Aut|Iso|Transform)' lean
```
The saved candidate snapshot trims trailing whitespace from copied source
lines; this normalization does not change the entry or file counts.

## Repo-owned group and symmetry families

### Supplemental Lake library under `proofs/`

The first candidate index above was generated from `lean/`; it did not cover
the separately configured root Lake library `proofs` (`lakefile.lean` declares
`lean_lib proofs` with `srcDir := ".."` and `.submodules `proofs`). A second
source scan finds 1,078 Lean files in `proofs/` and 36 same-line group,
permutation-action, or Lie-subalgebra declaration candidates in 28 owner
files. These are repo-owned formal sources, but are not thereby imported by
the `InfoGeometry` or `InfoGeometry.All` entrypoints. Their proof status must
be checked in their own owners/build targets.

The reviewed concrete carriers add the following families to the whole-repo
map:

| `proofs/` owners | Source-level group or symmetry carrier |
|---|---|
| `Clifford55.lean`, `RealPin55Core.lean`, `RealPin55Kernel.lean`, `GATL_CliffordGroup.lean` | The Clifford Lipschitz subgroup in `Cl55ˣ`; Mathlib's `pinGroup Q55` and `spinGroup Q55`; and the separately defined `FullPin55`, generated by normalized vectors with quadratic value `+1` or `-1`. The latter preserves the split-signature Pin carrier that the Mathlib `pinGroup` convention alone does not represent. These are actual subgroups of units of a noncommutative Clifford algebra. |
| `RealOrthogonalGroup55.lean`, `RealPin55QuadraticRepresentation.lean`, `RealO55CartanDieudonne.lean`, `RealPin55ReflectionGenerators.lean` | Split orthogonal subgroups in matrix/general-linear carriers and reflection-generated subgroups acting on the real quadratic space. The boundary action in `RealO55ProjectiveBoundaryAction.lean` is a permutation representation of this operator group. |
| `CanonicalZornIntegralSpinSubgroup.lean`, `CanonicalZornRealSpinTrialityClosure.lean`, `CanonicalZornSpinRelatedFiber.lean` | Integral Spin subgroup, real-locus Spin subgroup, and a Spin/triality subgroup in the product carrier. These are source declarations in `proofs/`; they are separate from the kernel-checked root `InfoGeometry` operator carriers unless an explicit transport/import theorem connects them. |
| `WallpaperSemidirectProduct.lean` | The generic semidirect-product group `T ⋊[φ] P`, its translation subgroup, and the normality/kernel facts. This is a group construction parameterized by actual groups, rather than a concrete wallpaper classification. |
| `A2WeylFin3Action.lean`, `A2InsideD5RootSubsystem.lean`, `HexIndexA2RootIntertwiner.lean`, `WeylSU3ColorSymmetry.lean` | A₂/Weyl permutation subgroup and actions on root labels or matrix data. These are finite permutation/readout carriers, not replacements for the noncommutative Clifford and root-operator realizations elsewhere. |
| `KleinPresentedGroup.lean`, `ProjectiveSheetV4.lean` | A relator normal subgroup in a free group and a central-sign subgroup in the projective-sheet extension. These are presentation/extension carriers; the normal subgroup by itself is not the quotient group. |
| `D5IsotropicDiagonalLieEquiv.lean`, `D5DiagonalComplexification.lean`, `SO55HyperbolicDiagonalLieEquiv.lean`, `SplitOctonionTKK55LieEquivalence.lean`, `SplitOctonionTrialityCore.lean` | Lie subalgebras and infinitesimal symmetry carriers. They are not counted as separate global symmetry groups without an integrated group/action declaration. |

The remaining syntax hits in the 36-row scan are maps or parameterized
permutation operations rather than independently defined group carriers.
The scan does not promote any of these declarations to a verified theorem
without checking the exact owner. The all-repository `rg --files -g '*.lean'`
scan reports 30,809 paths, but that raw total also includes `archive/`,
`artifacts/`, `agent_memory_recovery*/`, `tmp/`, scratch, and generated/recovery
trees. Those historical or generated surfaces are indexed separately and do
not count as current source owners under the deep-search protocol.

The remaining maintained Lean directories `tools/`, `tests/`, `scripts/`,
`lib/`, and `pure_math_lib/` contain 112 Lean files. The same result-type
declaration scan finds no group, permutation, or Lie-subalgebra definitions in
those directories; the only carrier-token hit in that set is the test module
importing and `#check`ing three Coxeter/Bragg declarations. This keeps the
supplemental map scoped to source declarations rather than incidental import
names.

A second alias-oriented source pass, needed because these types do not spell
`Subgroup` in their result type, found these additional group carriers in
`proofs/`:

| Owners | Alias carrier and relation |
|---|---|
| `BraidProject/BraidGroup.lean`, `B3PresentedGroup.lean` | Finite braid groups `braid_group n`, the infinite presented braid group `braid_group_inf`, and the presented three-strand group `B3`. Their generators and braid relations are defined in the source. |
| `KleinAffineDeckGroup.lean`, `KleinFundamentalGroup.lean`, `KleinPresentedGroup.lean` | The integral semidirect product `AffineKleinGroup := (Multiplicative ℤ) ⋊ (Multiplicative ℤ)` with parity inversion action; the algebraically presented Klein group; and `KleinPiOne`, the topological fundamental group. `KleinFundamentalGroup` proves group equivalences from the fundamental group to the affine and presented carriers. |
| `ProjectiveUnitary6.lean` | `U6 := Matrix.unitaryGroup (Fin 6) ℂ`, its center, and the central quotient `PU6`. |
| `BostConnesKMS.lean` | `AutOInfty := CuntzAlg_O_infty ≃ₐ[ℂ] CuntzAlg_O_infty`, the algebra-automorphism group of the locally defined Cuntz algebra carrier. |
| `LorentzChiralCuntzBridge.lean`, `ProjectiveMobiusMatrix.lean`, `YangBaxterZornBridge.lean` | Matrix special/general linear groups `SL₂(ℂ)`, `SL₂(ℤ)`, `SL₂(ℤ/2ℤ)`, and `GL₈(ℂ)`, used as carriers for their listed actions/bridges. |
| `ProjectiveSheetV4.lean`, `D4Equivariance.lean` | `DihedralGroup 4`, its `DihedralGroup 2` model (the Klein four group), and a separate `DihedralGroup 4` alias. These are finite abstract group carriers. |
| `CanonicalZornSpinRelatedFiber.lean`, `Spin44TrialityBridge.lean` | Aliases of Mathlib spin groups for the stated quadratic forms; `DiracGL` is the general-linear group of the complex Dirac-spinor module. |
| `A2WeylFin3Action.lean`, `SplitOctonionBraidSU3.lean` | `WeylA2` and `SU3ColorWeylModel` are finite permutation groups on their declared carriers. |
| `NuclearWallpaperSpectraClassification.lean` | A wallpaper-group alias to the projective wallpaper gauge carrier defined in the referenced owner. |

These alias findings are source declarations, not proof-status claims for each
owner. They expand the supplementary path map beyond the 36 result-type
candidate lines. The alias pass is still lexical/manual; compiler-level
declaration typing is needed before claiming the semantic census is complete.

| Family | Groups and actions represented in the source | Representative owner modules |
|---|---|---|
| Generic transformation groups | `Group` acting on a `Fintype` via `MulAction`; defines `invariant_under` and `is_transitive`, then proves `uniform_of_transformation_group` | `InfoGeometry/TransformationGroups.lean` |
| Omega finite/permutation groups | `FoldGaugeFiberGroup n := Equiv.Perm (Fin n)`; `FoldGaugeAut` records automorphism data; S₄/A₄/V₄ and Galois Sₙ appear in separate typed data/assumption structures. `RealInput40P7DiscriminantBranchS17.lean` records coefficient and modular degree data only, not an S₁₇ Galois theorem. `SyncHatdeltaGaloisS6Generic.lean` proves that its concrete six-cycle and transposition generate a subgroup equal to S₆; generic Galois and monodromy identifications were removed because no generic splitting-field action or specialization transport is constructed there. | `Omega/OperatorAlgebra/FoldGaugeGroupStructure.lean`; `Omega/GroupUnification/TerminalWindow6FoldGaugeAutOutStructure.lean`; `Omega/CircleDimension/S4EvenSubgroupFreeActionUnramifiedA4Lift.lean`; `Omega/SyncKernelWeighted/RealInput40P7Branch10GaloisS10.lean`; `Omega/SyncKernelWeighted/RealInput40P7DiscriminantBranchS17.lean`; `Omega/Zeta/SyncHatdeltaGaloisS6Generic.lean` |
| Fibonacci path-toggle operator group | `pathToggleGenerator` now toggles a vertex in a path-independent set when insertion/removal preserves independence, represents that involution as a permutation of the actual state carrier, and generates `pathToggleOperatorClosure`. The owner proves the generators are involutions and adjacent generators do not commute by evaluating both products on the empty state. `togglePathGroup` is this generated subgroup, not the full permutation group of all states. The former identity-generator proxy and unsupported full-symmetric/Coxeter conclusions were removed; the general Coxeter relation proof remains open. | `Omega/Combinatorics/FibonacciCube.lean`; `Omega/POM/ToggleCoxeterRelationsPath.lean`; `Omega/POM/ToggleGroupPathFullSymmetric.lean` |
| Root-lattice Weyl actions | **All exceptional tags:** `ExceptionalRootLatticeWeyl.lean` defines the integral root-coordinate lattice and the concrete subgroup generated by simple reflections uniformly for G₂, F₄, D₄, E₆, E₇, and E₈, with a source-level proof that it preserves the root predicate. It gives a faithful action on Boolean configurations, reindexes each countably infinite lattice configuration space to `CantorWord`, and defines an injective permutation representation and its image subgroup in `Equiv.Perm CantorWord`. `ExceptionalRootOperatorWeyl.lean` maps these symmetries to invertible operators on real-valued root-lattice functions, proves that the operator-unit representation is injective, and defines the resulting operator-unit subgroup. `ExceptionalRootWeylNoncommutativity.lean` now selects adjacent simple-root pairs for all six Cartan tags, proves their concrete lattice reflections do not commute from the nonzero Cartan entry, and transfers each witness to the operator-unit subgroup. Thus the Weyl realization has an explicit noncommuting operator pair uniformly; no scalar or diagonal carrier stands in for these Weyl operators. **E₈:** `Canonical/E8RootDecomposition.lean` separately enumerates the 240 roots and defines `e8WeylGroup` as the permutation subgroup generated by all root reflections; no identification with the generic exceptional lattice subgroup is stated in that owner. **F₄:** `Canonical/DualQuaternionF4WeylBridge.lean` has an abstract four-generator datum satisfying F₄ Coxeter relations. It does not construct those generators from dual quaternions or identify them with canonical root reflections; the old Weyl-named theorem is retained only as a compatibility alias; the corrected theorem name states equality with the closure of the same four declared generators. **D₄:** a separate integral lattice owner defines `d4WeylGroup` and proves preservation of roots and norm. Its abstract Coxeter group has a source-level faithful permutation representation on signed reflections via `Coxeter.permRep_inj`; the D₄ configuration owner likewise packages its action into permutations, and `D4CantorWeylAction.lean` transports that action to `CantorWord`. The D₄ configuration action, Cantor-word transport, and abstract-to-concrete Coxeter surjection now pass the locked build; the bridge does not prove injectivity or an isomorphism. The Weyl images and the Brin–Thompson simple subgroup share the Cantor permutation carrier, but no inclusion or identification is proved. A source-level bridge maps the abstract D₄ Coxeter group onto the concrete lattice subgroup; injectivity and an isomorphism are not established. **G₂:** additional concrete order-12 Weyl models act on roots and rank-two Cartan data, with bridges to the dihedral group. **Generic exceptional Chevalley port:** certified integer-coordinate root sets for all six tags and representatives `weylElt` acting by the corresponding reflection on root vectors inside the adjoint group. A uniform Coxeter identification for all six root-lattice Weyl subgroups remains open. No uniform root-lattice Weyl construction for all classical types was found in the inspected owners. | `InfoGeometry/RootSystem/ExceptionalRootLatticeWeyl.lean`; `InfoGeometry/RootSystem/ExceptionalRootOperatorWeyl.lean`; `InfoGeometry/RootSystem/ExceptionalRootWeylNoncommutativity.lean`; `InfoGeometry/RootSystem/D4RootLattice.lean`; `InfoGeometry/RootSystem/D4WeylGroup.lean`; `InfoGeometry/RootSystem/D4BitConfigurationAction.lean`; `InfoGeometry/RootSystem/D4CantorWeylAction.lean`; `InfoGeometry/RootSystem/D4CoxeterBridge.lean`; `InfoGeometry/Canonical/E8RootDecomposition.lean`; `InfoGeometry/Canonical/DualQuaternionF4WeylBridge.lean`; `InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylGroup.lean`; `InfoGeometry/Algebra/Zorn/G2WeylGroupCompletion.lean`; `InfoGeometry/Lie/CanonicalZornG2WeylGroupAction.lean`; `InfoGeometry/Exceptional/G2ArtinWeylBridge.lean`; `InfoGeometry/Exceptional/CFSGPort/ChevalleyRootInputs.lean`; `InfoGeometry/Exceptional/CFSGPort/ChevalleyWeyl.lean` |
| Prime-cutoff (A_1^P) Weyl encoding | `Canonical/FormalPrimeRootSystem.lean` stores prime labels as a finite set and `BooleanWeylGroup` elements as subsets; `Algebra/PrimeA1RootSystem.lean` likewise aliases Weyl elements to finite subsets. These encode the abstract abelian Weyl group of a product of (A_1) factors, but neither owner defines root vectors, reflection operators, or an operator-unit representation. The finite denominator/supertrace formulas are scalar combinatorics and do not supply that missing representation. Consequently these declarations are not counted as operator realizations; the operator-level replacement is outstanding. The correct (A_1^P) Weyl subgroup itself is abelian, so any noncommutative operator integration must preserve that fact and must not falsely claim noncommuting Weyl generators. | `InfoGeometry/Canonical/FormalPrimeRootSystem.lean`; `InfoGeometry/Algebra/PrimeA1RootSystem.lean`; `InfoGeometry/Arithmetic/MoebiusSignature.lean`; `InfoGeometry/Canonical/WeylSignum.lean` |
| Root-system, Coxeter, and diagram symmetries | D₄ triality gives an S₃ permutation action on its three noncentral discriminant classes and a separate Dynkin-diagram action on the lattice; G₂ Coxeter-plane and root-index models encode its dihedral Weyl symmetries. These are related to, but distinct from, the Weyl subgroup generated by root reflections. | `InfoGeometry/RootSystem/D4TrialityAction.lean`; `InfoGeometry/RootSystem/D4DynkinOuterReflectionCandidate.lean`; `InfoGeometry/RootSystem/G2CoxeterPlaneProjection.lean`; `InfoGeometry/Exceptional/G2ArtinWeylBridge.lean` |
| Abstract Coxeter and Weyl-group machinery (external source, root-imported) | `CoxeterPort/MatrixGroup.lean` adapts Mathlib's presented group of any `CoxeterMatrix` to the external `CoxeterGroup` class. `CoxeterPort/OperatorRepresentation.lean` transports the external faithful signed-reflection permutation representation to units of `Module.End ℝ (AbstractRootSet → ℝ)`. `CoxeterPort/GeometricReflectionOperators.lean` is a local, root-pinned-API-compatible port of the geometric simple-root reflection formulas: it defines the cosine Gram form, each simple reflection as an involutive linear equivalence, and the subgroup they generate inside endomorphism units. Its kernel-checked theorem `geometricReflectionOperatorGroup_exists_noncommuting_pair` proves that this actual subgroup contains a noncommuting pair whenever `M i j = 3`; `RootSystem/D4CoxeterBridge.lean` specializes it to the abstract D₄ Coxeter system with `d4GeometricReflectionOperatorGroup_exists_noncommuting_pair`, alongside the existing map onto the concrete lattice Weyl subgroup. `RootSystem/ExceptionalRootCoxeterBridge.lean` separately proves the braid law for an adjacent pair and the commuting law for an orthogonal pair on the actual D₄ root-coordinate lattice. These are genuine noncommutative root-operator results. The full Coxeter lift from that root-coordinate action, including all remaining pair relations and the resulting representation homomorphism, remains open. `Exceptional/CoxeterPort/G2CoxeterRepresentation.lean` adapts the repo's G₂ presentation. The external `Coxeter.GeometricRepresentation` remains excluded: its source does not compile against root-pinned Mathlib (nondegeneracy rewrites at lines 167 and 414); this local adapter ports only the simple-reflection operator layer. D₄ injectivity and uniform exceptional root-lattice Coxeter identifications remain open. | `external_refs/lean-coxeter/Coxeter.lean`; `external_refs/lean-coxeter/Coxeter/Basic.lean`; `external_refs/lean-coxeter/Coxeter/GeometricRepresentation.lean`; `external_refs/lean-coxeter/Coxeter/PermutationRepresentation.lean`; `external_refs/lean-coxeter/Coxeter/StrongExchange.lean`; `external_refs/lean-coxeter/Coxeter/Bruhat.lean`; `InfoGeometry/CoxeterPort/MatrixGroup.lean`; `InfoGeometry/CoxeterPort/OperatorRepresentation.lean`; `InfoGeometry/CoxeterPort/GeometricReflectionOperators.lean`; `InfoGeometry/Exceptional/CoxeterPort/G2CoxeterRepresentation.lean`; `InfoGeometry/RootSystem/D4CoxeterBridge.lean`; `InfoGeometry/RootSystem/ExceptionalRootCoxeterBridge.lean`; root wiring in `InfoGeometry.lean` and `InfoGeometry/All.lean` |

The external `lean-coxeter` checkout is pinned at commit
`857527a5ee35ddb64127654b821aabd99d2c178d`. Its `lean-toolchain` is
`leanprover/lean4:v4.34.1`, and its manifest pins Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the root dependency.
The root Lake file exposes selected Coxeter modules, and the local adapter
owners above import those modules directly. This establishes the dependency
and API boundary; it does not by itself verify the current umbrella build or
close the stated D₄ and exceptional Coxeter representation gaps.
| Cantor and fractal symmetries | The imported OAI results include simple groups built from twisted Brin/Thompson-style prefix-replacement actions on infinite Cantor cubes and a simple local group. `Cantor/SimpleCantorPermutationGroup.lean` source-defines a transport of the OAI twisted Brin--Thompson group on `ℕ → Stream' Bool` to a subgroup of permutations of the repo's `CantorWord := ℕ → Bool` by flattening the double index with Cantor pairing, transports its elementary cube bit flips into that subgroup, then applies the imported simplicity result. The adapter, including Cantor pairing transport and transfer of the imported simplicity theorem, now passes the locked build. This is a permutation group on the Cantor carrier; it is not presented as a topological homeomorphism group. No action connecting it to the D₄/G₂ Weyl groups has been proved. | `OAI/GroupTheory/BooneHigman/TwistedSimplicity.lean`; `OAI/GroupTheory/FiniteType/TwistedBrinSeparated.lean`; `InfoGeometry/Cantor/SimpleCantorPermutationGroup.lean`; `InfoGeometry/Cantor/CantorRandomWalk.lean`; `InfoGeometry/GrandUnification/CuntzCantorBoundary.lean`; `InfoGeometry/NCG/CuntzHoppingCantorLattice.lean` |
| Cantor bit flips and finite-mode Clifford operators | `Cantor/CantorRandomWalk.lean` proves that `flipBit i` is an involution that changes a binary sequence. Its former local `2 × 2` parabolic matrix step has been removed. `Cantor/CliffordMarkovOperators.lean` represents each normalized finite mode by an operator on the actual primal-sheet Fock module through the split Clifford representation, proves its square is the identity, and proves the cross-mode CAR. It also proves that the Fock permutation symmetry closure conjugates each Clifford mode operator to the permuted mode and that the Birkhoff Fock channel acts by the corresponding weighted operator sum. `Cantor/CliffordSymmetryGroup.lean` packages the mode operators as units, defines their generated subgroup in the Fock endomorphism units, transfers the cross-mode CAR to those unit generators, and proves distinct mode operators and units do not commute. Thus the finite-mode symmetry group is demonstrably noncommutative whenever at least two modes are present, and the finite Markov channel acts on these concrete operators through the permutation symmetry closure. `InfoGeometry.Cantor.All` passes the locked build with these results. A stochastic process on the infinite Cantor carrier, an infinite Cantor operator action, and a hom from the imported simple Cantor group remain unproved. | `InfoGeometry/Cantor/CantorRandomWalk.lean`; `InfoGeometry/Cantor/CliffordMarkovOperators.lean`; `InfoGeometry/Cantor/CliffordSymmetryGroup.lean`; `InfoGeometry/Cantor/SimpleCantorPermutationGroup.lean`; `InfoGeometry/Clifford/ClNNFockRepresentation.lean` |
| Finite Cuntz permutation and braid symmetries | `Algebra/CuntzBraidExpectationIntertwiner.lean` constructs a hom from `Equiv.Perm (Fin n)` to automorphisms of the finite Cuntz algebra, proves composition and expectation compatibility, and gives adjacent transpositions satisfying the Artin braid relation. These are genuine algebra automorphisms and provide another finite symmetry action; they are not yet identified with the split-Clifford permutation action or the infinite Cantor simple group. | `InfoGeometry/Algebra/CuntzBraidExpectationIntertwiner.lean` |
| Jones finite-state permutation representation | `Physics/JonesPermutationAction.lean` gives a hom from `Equiv.Perm (Fin 3)` (the S₃ symmetry) to permutations of eight states and a signed matrix representation into `GL8`. The module describes this as a finite-state representation, not an identification with Temperley--Lieb/Jones matrices. | `InfoGeometry/Physics/JonesPermutationAction.lean` |
| Canonical five-grade reversal symmetry | `CanonicalZornFiveGradeSymmetryClosure.lean` defines the subgroup generated by the existing involutive grade reversal on the full conformal-matrix carrier. It proves the subgroup preserves the native Lie bracket and linear structure, and packages each element as a Lie algebra equivalence. The owner proves each element is either identity or the reversal; it does not establish that the reversal is nonidentity. | `InfoGeometry/Canonical/CanonicalZornFiveGradeSymmetryClosure.lean`; `InfoGeometry/Canonical/CanonicalZornFiveGradeReversal.lean` |
| Six-state dihedral matrix group | `SixStateD6C2S3.lean` defines a monoid hom from the abstract dihedral group `D6` into units of the noncommutative six-state matrix algebra. Its range is the concrete subgroup, and `d6MatrixRangeEquiv` identifies the abstract `D6` carrier with that image; the owner also identifies the range with the closure of the two matrix generators. | `InfoGeometry/Canonical/SixStateD6C2S3.lean` |
| Split-octonion stabilizer symmetries | `Lie/SplitOctonionEllStabilizer.lean` defines Lie subalgebras stabilizing a split direction, an ordered chiral pair, and a quaternionic slice, plus corresponding subgroups of the real Zorn composition automorphism group. This gives concrete stabilizer symmetry carriers; the declarations do not classify these subgroups as named Lie groups or establish a global identification with G₂. | `InfoGeometry/Lie/SplitOctonionEllStabilizer.lean`; `InfoGeometry/Lie/CanonicalZornDerivation.lean` |
| Generic coset and incidence actions | `Architecture/CartanCosetManifold.lean` defines the left action of a group on quotient cosets and invariant metric data. `Algebra/Zorn/G2GAPCosetHomomorphismBridge.lean` turns a finite coset action into a permutation representation and proves equivariance of quotient projections; `G2FlagIncidenceAction.lean` packages incidence-preserving point permutations as flag permutations. These are action constructions, not by themselves new abstract group classifications. | `InfoGeometry/Architecture/CartanCosetManifold.lean`; `InfoGeometry/Algebra/Zorn/G2GAPCosetHomomorphismBridge.lean`; `InfoGeometry/Algebra/Zorn/G2FlagIncidenceAction.lean` |
| External OAI simple-group theorems imported at root | The repository's `OAI` Lake library points to `external_refs/openai-math/lean`. Both root entrypoints import the inspected theorem and support modules for Boone--Higman, twisted Brin, finite-type simple overgroups, finite-lattice simple groups, polygon alternating groups, and simple amenable groups. OAI proves `infinite_group_simple` for twisted Brin--Thompson when `X` is infinite, `localGroup_simple`, and `polygonAlternatingGroup_simple`. `SimpleAmenable.Main.main` exhibits an infinite finitely presented simple Følner-amenable group. The repo-owned `GroupTheory/SimpleAmenableWitness.lean` exposes the explicit stage-206 `polygonAlternatingGroup` carrier together with infinitude, finite presentation, simplicity, and Følner amenability; it also constructs its faithful image in units of `Module.End ℝ (TrackPoint a 206 → ℝ)`, proves that operator group simple, and proves an explicit existential noncommuting-pair result for the operator group. The repo-owned Cantor adapters separately transport twisted Brin simplicity to Cantor-word permutations and their faithful endomorphism-unit image. Boone--Higman and finite-type modules also give simple-overgroup existence results, some conditional on word-problem or geometric data. The current locked `InfoGeometry.All` build passed with 28,137 jobs on 2026-10-29. | `lakefile.lean`; `lean/InfoGeometry.lean`; `lean/InfoGeometry/All.lean`; `lean/InfoGeometry/GroupTheory/SimpleAmenableWitness.lean`; `lean/InfoGeometry/Cantor/SimpleCantorPermutationGroup.lean`; `lean/InfoGeometry/Cantor/SimpleCantorOperatorGroup.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/BooneHigman/Main.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/BooneHigman/TwistedSimplicity.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/FiniteType/TwistedBrinSeparated.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/FiniteLattice/CommonCore.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/FiniteLattice/RetainedCore.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/FiniteType/SourceEnlargement.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/SimpleAmenable/Main.lean`; `external_refs/openai-math/lean/OAI/GroupTheory/SimpleAmenable/PolygonGeometry/ShiftedSlots.lean` |

The exact OAI simple-group scan under `external_refs/openai-math/lean/OAI`
returns these 21 files, and both root entrypoints import the corresponding
module paths:

```text
GroupTheory/BooneHigman/Basic.lean
GroupTheory/BooneHigman/Main.lean
GroupTheory/BooneHigman/TwistedSimplicity.lean
GroupTheory/BooneHigman/WordProblem.lean
GroupTheory/FiniteLattice/CommonCore.lean
GroupTheory/FiniteLattice/CommonCoreAmbient.lean
GroupTheory/FiniteLattice/CommonCoreStatement.lean
GroupTheory/FiniteLattice/InnerAutomorphisms.lean
GroupTheory/FiniteLattice/NormalPreimage.lean
GroupTheory/FiniteLattice/RetainedCore.lean
GroupTheory/FiniteType/SourceEnlargement.lean
GroupTheory/FiniteType/StageGeometry.lean
GroupTheory/FiniteType/StageGeometryProperties.lean
GroupTheory/FiniteType/TwistedBrinSeparated.lean
GroupTheory/SimpleAmenable/Amenability/SubgroupTestReiter.lean
GroupTheory/SimpleAmenable/Configurations/PolygonFixedTrackProgress.lean
GroupTheory/SimpleAmenable/Main.lean
GroupTheory/SimpleAmenable/Model.lean
GroupTheory/SimpleAmenable/PolygonGeometry/ShiftedSlots.lean
GroupTheory/SimpleOvergroups/SourceProducer.lean
GroupTheory/SimpleOvergroups/SourceRingReduction.lean
```
| Birkhoff/Sinkhorn permutation mixtures and split-Clifford readouts | At each finite stage `Fin n`, `Canonical/SinkhornFoundation.lean` defines a router switch matrix, a `SinkhornCertificate` carrying positive diagonal scales and a proof that the scaled matrix is doubly stochastic, and invokes Mathlib's Birkhoff--von Neumann theorem to express that matrix as a convex combination of `Equiv.Perm (Fin n)` permutation matrices. `Canonical/GrandCanonicalExperts.lean` reuses those weights in `exists_modewiseClifford_rep_of_bistochastic`; its output is a weighted element of `CliffordAlgebra splitQ11` with a plus/minus split, not by itself a Fock action. `Clifford/ClNNPermutationSymmetry.lean` source-defines the finite mode-permutation isometry of the repo's symmetric split `Cl(n,n)` form, its induced Clifford algebra automorphisms and generated subgroup, a weighted linear average of those automorphisms, and induced exterior-Fock automorphisms with a creation-intertwining theorem. It also source-states that a doubly stochastic matrix has Birkhoff weights reconstructing the matrix while producing a unital Clifford average. Mathematically, the random Markov step is a convex mixture in the linear span of the permutation representation; in general it is neither a group element nor an algebra automorphism. “Markov group” therefore names the symmetry group acting on the Markov state space, not the stochastic operator itself. These declarations pass the successful root umbrella build. A Birkhoff-weighted average on the full Fock operator endomorphism algebra is now defined and checked. The kernel-checked `exists_randomPermutationCliffordAverage_primalMatrixAction` reindexes Birkhoff weights by permutation inversion and proves that every finite doubly-stochastic transition matrix acts exactly on primal generators inside the split Clifford algebra. `InfoGeometry.Clifford.ClNNPermutationSymmetry` and its `InfoGeometry.All` import surface both pass locked builds; the latter completed 28,091 jobs. Intertwining this Clifford-algebra action with the represented Fock endomorphism channel, including annihilation, and compatibility with the infinite Cantor simple group remain unproved. | `Canonical/SinkhornFoundation.lean`; `Canonical/GrandCanonicalExperts.lean`; `Routing/BirkhoffVonNeumann.lean`; `Clifford/ClNNPermutationSymmetry.lean`; `Clifford/ClNNFockRepresentation.lean`; `Clifford/ClNNFockColimitPrimalSheetBridge.lean`; `Cantor/SimpleCantorPermutationGroup.lean` |
| Orthogonal split-form symmetries and Clifford lifts | `Algebraic/CliffordSymmetryLift.lean` defines a `SplitQuadraticSymmetry n` as an isometry of the actual split quadratic form and lifts it via `CliffordAlgebra.equivOfIsometry` to a Clifford algebra equivalence. `Clifford/Cl55WittModePermutations.lean` constructs the concrete `S₅` mode-reindexing hom into the orthogonal group of the `Cl(5,5)` form and lifts it to Clifford algebra automorphisms; `Clifford/ClNNPermutationSymmetry.lean` defines the finite-stage mode-permutation subgroup and its linear average. The owner does not classify the full isometry group, identify it with a Pin/Spin group, or prove that an arbitrary Markov transition is such an isometry. The finite permutation average is linear and unital, while the individual symmetry lifts are algebra automorphisms; no multiplication-preservation theorem for the average is claimed. | `Algebraic/CliffordSymmetryLift.lean`; `Algebraic/SplitCliffordCarrier.lean`; `Clifford/Cl55WittModePermutations.lean`; `Clifford/ClNNPermutationSymmetry.lean`; `OperatorAlgebra/CliffordCAR.lean` |
| Noncommutative Clifford-CAR Lie symmetries | `OperatorAlgebra/CliffordCARQuadraticClosure.lean` proves that quadratic creation, annihilation, and number-operator sectors close under the ordinary commutator in the actual `Cl(n,n)` algebra, then packages these sectors as native `LieSubalgebra ℝ (Clnn n)` carriers. These are operator Lie algebras, not scalar-coordinate replacements or claims of a classified global Lie group. | `InfoGeometry/OperatorAlgebra/CliffordCARQuadraticClosure.lean`; `InfoGeometry/OperatorAlgebra/CliffordCAR.lean`; `InfoGeometry/Clifford/ClNNPermutationSymmetry.lean` |
| Split-octonion derivation and Clifford operator Lie symmetries | `Algebra/F4Derivations.lean` defines the Jordan derivations of the nonassociative `H3Zorn ℝ` algebra as a `LieSubalgebra ℝ (Module.End ℝ (H3Zorn ℝ))` and proves commutator closure; this supplies an operator Lie carrier related to the F₄ derivation construction, without proving a global F₄ group identification in that owner. `Algebra/SplitAlbertStructureOperators.lean` defines actual endomorphisms `D + Lₐ` on the same Albert/Jordan carrier and proves their commutator formula, keeping the derivation, inner-derivation, and multiplication-operator channels explicit. `Clifford/Cl55OperatorLieSubalgebra.lean` takes the Lie span of actual creation and annihilation operators inside `Cl55`, while `Clifford/CliffordLieAlgebra.lean` defines the `soNN` carrier inside the split Clifford algebra from bivector commutators. These source owners do not by themselves prove all corresponding global group integrations or equivalences with named Lie groups; the focused declarations are indexed source evidence and have not been kernel-checked in this audit. | `InfoGeometry/Algebra/F4Derivations.lean`; `InfoGeometry/Algebra/BaezF4H3Zorn.lean`; `InfoGeometry/Algebra/SplitAlbertStructureOperators.lean`; `InfoGeometry/Clifford/Cl55OperatorLieSubalgebra.lean`; `InfoGeometry/Clifford/CliffordLieAlgebra.lean` |
| Split-orthogonal operator Lie symmetries | `Orthogonal/O55ContactLie.lean` defines the endomorphisms skew for the actual split pairing on the 10-mode carrier and proves their commutator remains in a `LieSubalgebra`; `Lie/SO55MatrixLieSubalgebra.lean` and `Canonical/O55OrthogonalLieCarrier.lean` give matrix-operator realizations of the same split-orthogonal infinitesimal condition. These are noncommutative endomorphism/matrix Lie carriers, distinct from diagonal rescaling parameters, and the cited owners do not identify their global group integrations with one another. | `InfoGeometry/Orthogonal/O55ContactLie.lean`; `InfoGeometry/Orthogonal/O55RealWittForm.lean`; `InfoGeometry/Lie/SO55MatrixLieSubalgebra.lean`; `InfoGeometry/Canonical/O55OrthogonalLieCarrier.lean` |
| Infinitesimal exceptional symmetries | `canonicalZornDerivations : LieSubalgebra ℝ EndCZ` is the split-octonion derivation Lie algebra, with finrank 14; G₂ Weyl reflections act on rank-two Cartan data. The real derivation Lie algebra is present, while a global real automorphism-group equivalence is explicitly a separate open lane | `InfoGeometry/Lie/CanonicalZornDerivation.lean`; `InfoGeometry/Lie/CanonicalZornDerivationDimension.lean`; `InfoGeometry/Lie/RealSplitOctonionG2Classification.lean`; `InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariant.lean` |
| Exceptional Chevalley groups | Root generators and root subgroups for G₂, F₄, D₄, E₆, E₇, E₈; adjoint central quotients and diagram-twisted fixed subgroups for E₆ and D₄. `ExceptionalModelSimplicity.lean` ports conditional transport for untwisted models, twisted derived fixed-subgroup models (²E₆/³D₄), Ree/Tits relation models (²G₂/²F₄/Tits), and a Suzuki carrier acting by general linear operators on its four-dimensional module. The Suzuki operator group now has a kernel-checked noncommuting pair from a root operator and the antidiagonal Weyl operator. For every local exceptional Cartan tag, `ChevalleyNormalizerTriviality.lean` proves opposite-root normalizer triviality on the actual root module and extracts a noncommuting pair inside the full adjoint operator subgroup. The module also provides generic adjoint quasisimplicity transport from perfectness plus the central-or-total normal-subgroup dichotomy, and a uniform untwisted model-simplicity adapter from those fieldwise inputs. G₂ has a family-specific instance of this boundary using local perfectness and the newly ported normalizer field; the remaining Curtis–Tits/Bruhat structure and normal-subgroup dichotomy are still open. Family-specific quasisimplicity or simplicity results remain explicit hypotheses; this is local API coverage, not completion of the external family proofs | `InfoGeometry/Exceptional/CFSGPort/ChevalleyRootGroupsTriangular.lean`; `InfoGeometry/Exceptional/CFSGPort/ChevalleyNormalizerTriviality.lean`; `InfoGeometry/Exceptional/CFSGPort/ExceptionalCatalog.lean`; `InfoGeometry/Exceptional/CFSGPort/ExceptionalModelSimplicity.lean`; `InfoGeometry/Algebra/Zorn/G2FiniteChevalleyGroupBridge.lean`; `InfoGeometry/Algebra/Zorn/G2TwoFiniteChevalleyGroup.lean` |
| Split-octonion `G₂(2)` finite group, Weyl, and parabolic subgroups | `SplitOctF2Aut` is the native split-octonion automorphism group carrier. Its owners define a concrete subgroup generated by six PC generators and an exact 64-element `unipotentSubgroup`, prove the PC-exponent group isomorphism, and derive the Sylow-2 conclusion under the ambient cardinality hypothesis `Nat.card SplitOctF2Aut = 12096`. A separate concrete Weyl subgroup has 12 elements; `G2TwoBruhatClassification.lean` defines the two standard parabolic subgroups and their coset/Bruhat actions, while native point-stabilizer owners connect subgroup actions to the isotropic-point carrier. `G2CASNativePointAction.lean` records seven generator permutations on the 63-point carrier and proves each intertwines the CAS enumeration with the native split-octonion action. Other concrete subgroup declarations include root subgroups, their conjugates, the positive-root subgroup, residual and PC subgroups, and generator closures, all inside `SplitOctF2Aut`; the `G2*Bruhat*`, `G2*Residual*`, and `G2*Flag*` transport files mostly prove factorization, quotient, and incidence laws on these existing carriers rather than adding distinct ambient groups. `G2BNPair.lean` supplies a generic Tits-system/finite-Bruhat-partition interface used by concrete G₂ quotient-orbit owners; this entry does not claim that the generic structure is instantiated as a BN-pair on all of `SplitOctF2Aut`. `G2PeirceParabolicStabilizer.lean` separately declares generic stabilizer/parabolic and ℙ¹(𝔽₂)-fiber results under supplied action, rigidity, cardinality, and distinctness hypotheses; its statements should not be mistaken for a construction of the stabilizer inside `SplitOctF2Aut`. The 12096 order is recorded in a separate GAP/Atlas ledger and must not be read as a theorem from the group-structure adapter alone. These finite `G₂(2)` objects are distinct from the general finite-field adjoint Chevalley `G₂(q)` models in `CFSGPort`. | `InfoGeometry/OperatorAlgebra/G2TwoAutomorphismTheorem.lean`; `InfoGeometry/Algebra/Zorn/G2TwoFiniteChevalleyGroup.lean`; `InfoGeometry/Algebra/Zorn/G2TwoPCSubgroupClosure.lean`; `InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylGroup.lean`; `InfoGeometry/Algebra/Zorn/G2TwoBruhatClassification.lean`; `InfoGeometry/Algebra/Zorn/G2NativeOnePointStabilizer.lean`; `InfoGeometry/Algebra/Zorn/G2CASNativePointAction.lean`; `InfoGeometry/Algebra/Zorn/G2BNPair.lean`; `InfoGeometry/Algebra/Zorn/G2FlagAndParabolicQuotient.lean`; `InfoGeometry/Algebra/Zorn/G2PeirceParabolicStabilizer.lean`; `InfoGeometry/Algebra/Zorn/G2TwoAutomorphismOrderLedger.lean`; `InfoGeometry/Algebra/Zorn/G2RootSubgroup.lean`; `InfoGeometry/Algebra/Zorn/G2RootSubgroupConjugation.lean`; `InfoGeometry/Algebra/Zorn/G2SteinbergPositiveRoots.lean`; `InfoGeometry/Algebra/Zorn/G2BruhatResidual.lean`; `InfoGeometry/Algebra/Zorn/G2TwoPCSubgroupClosure.lean`; `InfoGeometry/Algebra/Zorn/G2TwoSylowSubgroup.lean`; `InfoGeometry/Algebra/Zorn/G2ConcreteGeneratorInfrastructure.lean`; `InfoGeometry/Algebra/Zorn/G2NativeRootProductImage.lean`; `InfoGeometry/Algebra/Zorn/G2NativeFlagStabilizerTransport.lean`; `InfoGeometry/Algebra/Zorn/G2NativeFlagStabilizerTransport.lean`; `InfoGeometry/Algebra/Zorn/G2TwoOuterGenerators.lean`; `InfoGeometry/Algebra/Zorn/G2TwoExplicitGenerators.lean`; `InfoGeometry/Algebra/Zorn/G2TwoPCSubgroupClosure.lean`; `InfoGeometry/Algebra/Zorn/G2CASGeneratorSubgroup.lean`; `InfoGeometry/Algebra/Zorn/G2CorrectedTComplementCard.lean`; `InfoGeometry/Algebra/Zorn/G2ConcreteBN2FirstConjugation.lean`; `InfoGeometry/Algebra/Zorn/G2ConcreteBN2CorrectSecondConjugation.lean`; `InfoGeometry/Algebra/Zorn/G2TwoPCSubgroupClosure.lean`; `InfoGeometry/Algebra/Zorn/G2TwoSylowPCAutomorphisms.lean`; `InfoGeometry/Algebra/Zorn/G2PeirceParabolicStabilizer.lean` |
| Exceptional Chevalley operator Borel groups | `ChevalleyBorelIntersection.lean` defines `operatorBorelSubgroup` in the actual unit group of endomorphisms of the Chevalley root module, generated by the root torus and positive unipotent operators. It proves the Borel intersects the negative unipotent subgroup trivially and the root torus intersects positive unipotents trivially. This is a concrete operator subgroup and structural intersection theorem, not a diagonal-matrix surrogate or an exceptional simplicity proof. | `InfoGeometry/Exceptional/CFSGPort/ChevalleyBorelIntersection.lean`; `InfoGeometry/Exceptional/CFSGPort/ChevalleyRootTorusSubgroup.lean`; `InfoGeometry/Exceptional/CFSGPort/ChevalleyRootGroupsTriangular.lean` |
| Classical linear and isometry groups | SL₂/SL₃ constructions and representations; an explicit `HessianOrthogonalGroup E` with `Group` instance for neutral-form isometries; symplectic, Lorentz, and unitary actions | `InfoGeometry/Algebra/SL3DualActionF2.lean`; `InfoGeometry/Krein/OrthogonalGroup.lean`; `InfoGeometry/Optics/LocalGaugeGroupAction.lean`; `InfoGeometry/Twistor/Pin55PurePinorMinusRepresentation.lean`; `InfoGeometry/Canonical/CanonicalZornSpinVectorAction.lean`; `InfoGeometry/Clifford/Cl55WittModePermutations.lean` |

The remaining indexed G₂ owner files add several distinct kinds of evidence and
are not counted as new ambient groups merely because their declarations
mention subgroups. `G2BNBruhatFramework.lean` embeds the dihedral Weyl group
into the native automorphism carrier; `G2TwoConcreteWeylG2.lean` and
`G2CoxeterGeneratingEquality.lean` define and compare concrete generated Weyl
subgroups; `G2ImaginaryPointPermutation.lean`,
`G2PointEnumRelabeling.lean`, and `G2CosetActionHomomorphism.lean` package
actions as permutations of finite point or coset carriers. The root-Weyl
character and normal-form files act on root carriers. `G2FlagWordEvaluator`
and `G2StructuralFlagQuotient` define generated subgroups or quotient
transports. In contrast, `G2SymbolicBN2`, `G2SymbolicBN2Assembly`,
`G2BN2InductivePeeling`, and `G2IndexTwoRankOneBN2` state generic laws under
supplied subgroup/representative hypotheses; those abstractions are not by
themselves a concrete BN-pair on `SplitOctF2Aut`. `G2GaloisCorrespondence`
defines the fixed-set/stabilizer connection for the native automorphism group,
not a field-extension Galois group. The cyclotomic signed-root bridge and
reduced-word owners provide root-permutation and normal-form representations.
These distinctions prevent generic hypotheses, permutation readouts, and
transport lemmas from being mistaken for additional exceptional Lie groups.

Additional owner paths inspected for this distinction:
`InfoGeometry/Algebra/Zorn/G2BN2InductivePeeling.lean`;
`InfoGeometry/Algebra/Zorn/G2BNBruhatFramework.lean`;
`InfoGeometry/Algebra/Zorn/G2BruhatResidualSimpleEquiv.lean`;
`InfoGeometry/Algebra/Zorn/G2CosetActionHomomorphism.lean`;
`InfoGeometry/Algebra/Zorn/G2CoxeterGeneratingEquality.lean`;
`InfoGeometry/Algebra/Zorn/G2CyclotomicSignedRootBridge.lean`;
`InfoGeometry/Algebra/Zorn/G2FlagWordEvaluator.lean`;
`InfoGeometry/Algebra/Zorn/G2GaloisCorrespondence.lean`;
`InfoGeometry/Algebra/Zorn/G2ImaginaryPointPermutation.lean`;
`InfoGeometry/Algebra/Zorn/G2IndexTwoRankOneBN2.lean`;
`InfoGeometry/Algebra/Zorn/G2PointEnumRelabeling.lean`;
`InfoGeometry/Algebra/Zorn/G2ReducedWords.lean`;
`InfoGeometry/Algebra/Zorn/G2RootWeylAdjointCharacter.lean`;
`InfoGeometry/Algebra/Zorn/G2RootWeylNormalForm.lean`;
`InfoGeometry/Algebra/Zorn/G2StructuralFlagQuotient.lean`;
`InfoGeometry/Algebra/Zorn/G2SymbolicBN2.lean`;
`InfoGeometry/Algebra/Zorn/G2SymbolicBN2Assembly.lean`;
`InfoGeometry/Algebra/Zorn/G2TwoConcreteWeylG2.lean`.
| Spin and Pin symmetries | Spin/Pin representations, lifts, subgroups, and Clifford actions | `InfoGeometry/Canonical/CanonicalZornIntegralSpinSubgroup.lean`; `InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean`; `InfoGeometry/Twistor/Cl55RealSplitPinNullFundamentalGroup.lean` |

Verification update (2026-10-29): `InfoGeometry.Cantor.All` passes the locked
Lake build with the new operator group, and
`python3 tools/infra/run_locked_lean.py --wait-for-build-lock
lean/InfoGeometry.lean` succeeds with the `InfoGeometry.Cantor.All` import.
The corresponding direct check of `lean/InfoGeometry/All.lean` is blocked by
the missing cached object for
`Omega.Zeta.XiLanglandsLeyangLocalDegenerationStratification`. The broader
locked Lake runs also fail in four existing `Omega.Zeta` modules; these
failures are recorded separately and do not negate the successful direct
elaboration of `InfoGeometry.lean`.

### Additional canonical carrier review

The indexed canonical owners add concrete carriers beyond the representative
rows above. `OrthogonalGroup55` is a subgroup of `GL₁₀(ℝ)` preserving the
native split form; `Pin55OrthogonalBridge` and
`Spin55NativeOrthogonalCentralKernel` define subgroups in Pin/Spin carriers;
`Physics/Pin55Formal.lean` also defines Mathlib's `pinGroup q55` and
`spinGroup q55` inside the noncommutative split `(5,5)` Clifford algebra;
Mathlib supplies their group structures, while this owner proves concrete
generator relations and explicitly does not claim its four displayed
elements form a subgroup;
`CanonicalZornSpinRelatedFiber` is a subgroup of the product of the Spin(44)
carrier and the triality-related-triples group; and
`SplitOctonionAutomorphismCore` defines linear equivalences preserving the
actual Zorn product. These are composition/operator groups. The A₂ Weyl
owners give permutation representations on root sets, while `GolayPermutationSubgroup`
defines the coordinate-permutation subgroup preserving the Golay predicate.
`KleinPresentedGroup` defines a presented group as a quotient, and the
cyclotomic Galois owner relates actual Galois subgroups to intermediate fields.

Other indexed declarations are action maps, stabilizers, or readouts of these
carriers. The Cayley parity and duality packets are finite commuting subgroups
of units in `Module.End ℝ Coord`; they are recorded as such and are not used as
models for the noncommutative operator, Clifford, Spin, or Lie groups. Likewise,
permutations of sectors, grades, weights, or finite labels are action data,
not extra Lie groups. The relevant owners are
`InfoGeometry/Canonical/ProjectiveUnitary6.lean`,
`InfoGeometry/Canonical/A2InsideD5RootSubsystem.lean`,
`InfoGeometry/Canonical/DrazinFierzBridge.lean`,
`InfoGeometry/Canonical/CanonicalZornSpinRelatedFiber.lean`,
`InfoGeometry/Canonical/EmergentFisherMetric.lean`,
`InfoGeometry/Canonical/PauliSignedPermutationSupergradedBridge.lean`,
`InfoGeometry/Canonical/SplitOctonionAutomorphismCore.lean`,
`InfoGeometry/Canonical/OperatorErlangenFixedPoints.lean`,
`InfoGeometry/Canonical/G2CuntzKriegerScalarSeparatedBridge.lean`,
`InfoGeometry/Canonical/FiniteFibonacciAnyonBraiding.lean`,
`InfoGeometry/Canonical/ZornOuterTrialityGroup.lean`,
`InfoGeometry/Canonical/Cyclotomic12GaloisCorrespondence.lean`,
`InfoGeometry/Canonical/GradeAutomorphismPerm.lean`,
`InfoGeometry/Canonical/SouriauThermodynamicCoadjointOrbitBridge.lean`,
`InfoGeometry/Canonical/CayleyParityUnitsBridge.lean`,
`InfoGeometry/Canonical/ZbwDarwinDemodulation.lean`,
`InfoGeometry/Canonical/OrthogonalGroup55.lean`,
`InfoGeometry/Canonical/CanonicalZornRealSpinTrialityClosure.lean`,
`InfoGeometry/Canonical/KleinBottleBoundaryActionPacket.lean`,
`InfoGeometry/Canonical/Pin55OrthogonalBridge.lean`,
`InfoGeometry/Canonical/OrientedPfaffianMatching.lean`,
`InfoGeometry/Canonical/OperatorErlangenGaloisConnection.lean`,
`InfoGeometry/Canonical/Orthogonal55Components.lean`,
`InfoGeometry/Canonical/Spin55NativeOrthogonalCentralKernel.lean`,
`InfoGeometry/Canonical/KKTConformalChiralContext.lean`,
`InfoGeometry/Canonical/Cl55WittPinConformalBoundaryBridge.lean`,
`InfoGeometry/Canonical/TrialitySpin8Permutations.lean`,
`InfoGeometry/Canonical/Cl55WittWeylReflections.lean`,
`InfoGeometry/Canonical/KleinPresentedGroup.lean`,
`InfoGeometry/Canonical/FiniteMajoranaBraiding.lean`,
`InfoGeometry/Canonical/D4StarObservableDirectLimitAction.lean`,
`InfoGeometry/Canonical/GolayPermutationSubgroup.lean`,
`InfoGeometry/Canonical/BraidedCubicCompressionBridge.lean`,
`InfoGeometry/Canonical/ParabolicNullQuotientCausalCone.lean`,
`InfoGeometry/Canonical/CyclicZornTrialityAction.lean`,
`InfoGeometry/Canonical/A2QutritWeylAdjoint.lean`,
`InfoGeometry/Canonical/KleinAffinePermutationActionBridge.lean`,
`InfoGeometry/Canonical/IntegralCyclotomicGroup.lean`,
`InfoGeometry/Canonical/CayleyDualitySectorPermutationBridge.lean`,
`InfoGeometry/Canonical/CoordinateTrialityLabelIntertwiner.lean`,
`InfoGeometry/Canonical/CuntzSuperBraidMoEBridge.lean`,
`InfoGeometry/Canonical/PauliJungTrialityD4Synthesis.lean`,
`InfoGeometry/Canonical/SE2SouriauCoadjointTopology.lean`,
`InfoGeometry/Canonical/SplitClifford55SpinOrthogonalImageQuotientBridge.lean`,
`InfoGeometry/Canonical/CayleyDualityUnitsBridge.lean`,
`InfoGeometry/Canonical/FiniteMajoranaProjectiveBraiding.lean`,
`InfoGeometry/Canonical/A2WeylPermutationAction.lean`, and
`InfoGeometry/Canonical/GATLClifford55Bridge.lean`.
| Permutation and finite groups | Explicit cyclicity predicate/lemmas; concrete CPT two-group laws; D₄ triality/Q₈ and braid-to-S₃ quotient bridges | `InfoGeometry/Algebra/CyclicGroup.lean`; `InfoGeometry/Canonical/DiscreteCPTGroup.lean`; `InfoGeometry/Topology/D4TrialityQ8Equivalence.lean`; `InfoGeometry/Categorical/BraidGroup3S3QuotientBridge.lean` |
| Braid, Artin, symmetric, and pure-braid groups | The repository has a `BraidGroup3` presentation equivalent to Mathlib's `braid_group 3`, a universal finite Artin-braid homomorphism `braid_group (m+1) →* Equiv.Perm (Fin (m+1))` sending generators to adjacent transpositions, and a proof that this map is surjective. `pureBraidSubgroup m` is defined as its kernel; the normal closure of generator squares is shown contained in the kernel, while equality with that closure is explicitly left open. This general quotient specializes to the B₃→S₃ shadow and connects braid groups to permutation symmetries, without identifying a separate geometric monodromy group unless a carrier-specific theorem does so. | `InfoGeometry/Categorical/BraidPermutationQuotient.lean`; `InfoGeometry/Categorical/FibonacciBraidGroup3.lean`; `InfoGeometry/Categorical/BraidGroup3PresentationBridge.lean`; `InfoGeometry/Categorical/UniversalArtinBraidRepresentation.lean`; `InfoGeometry/Topology/ArtinBraidS3Quotient.lean`; `InfoGeometry/Exceptional/G2ArtinPresentation.lean` |
| Finite permutation actions on configuration quotients | `Cl55CelestialUnorderedConfiguration.lean` defines a genuine `Equiv.Perm (Fin n)` reindexing action on ordered distinct celestial configurations, proves equivariance of its projective-null embedding, and constructs the unordered quotient by the exact finite-permutation orbit relation. The owner explicitly does not identify this quotient as a braid space, compute its fundamental group, or prove monodromy. | `InfoGeometry/Twistor/Cl55CelestialUnorderedConfiguration.lean`; `InfoGeometry/Twistor/ProjectiveNullUnorderedConfiguration.lean`; `InfoGeometry/Twistor/ProjectiveNullConfigurationFundamentalGroup.lean`; `InfoGeometry/Twistor/ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence.lean` |
| Triality and its noncommutative extensions | `CartanTrialityGroup := relatedTriples`, a subgroup of a product of three general linear groups; the order-three triality map preserves it. `V4SemidirectS3Bridge.lean` builds the explicit semidirect product `V4 ⋊ S3` and its conjugation action; `ZornOrientationTwistedS3.lean` gives an S₃ action respecting Zorn multiplication; coordinate triality transports the signed action among vector and spinor sectors. | `InfoGeometry/Canonical/CanonicalZornOuterTrialityGroup.lean`; `InfoGeometry/Canonical/V4SemidirectS3Bridge.lean`; `InfoGeometry/Canonical/ZornOrientationTwistedS3.lean`; `InfoGeometry/Canonical/CanonicalZornCoordinateOuterTrialityNaturality.lean`; `InfoGeometry/Exceptional/BartonSudberyTrialityAction.lean`; `InfoGeometry/Topology/D4TrialityQ8Equivalence.lean` |
| Noncommutative three-colour braid operators | `ThreeColorPolynomialYangBaxterBridge.lean` represents adjacent swaps by operators on the triple-colour matrix carrier and proves their Artin braid relation. The instantiated `colourSwapR` is a permutation operator satisfying its quadratic polynomial; the generic `ThreeColorPolynomialRData` takes its annihilating polynomial as input, so this owner does not yet prove a nontrivial Yang--Baxter operator solution. `JonesPermutationAction.rho` is an S₃ hom into `GL8`; its explicit noncommutativity theorem concerns two matrix units in `M₈(ℂ)`, not yet two elements in the image of `rho`, and the module does not identify `rho` with Temperley--Lieb matrices. The Cuntz owner separately has a genuine permutation hom into automorphisms of a noncommutative algebra and proves expectation compatibility. | `InfoGeometry/Canonical/ThreeColorPolynomialYangBaxterBridge.lean`; `InfoGeometry/Physics/JonesPermutationAction.lean`; `InfoGeometry/Algebra/CuntzBraidExpectationIntertwiner.lean` |
| Qutrit noncommutative Weyl and S₃ operators | `Canonical/A2QutritWeylTransport.lean` proves the `S₃` permutation-matrix hom law and conjugation action on the six `A₂` roots. `Quantum/QutritBraidIncidenceBridge.lean` represents qutrit label permutations by matrix operators, proves the adjacent-transposition Artin relation and conjugation transport of qutrit projectors, and records the generalized Pauli clock/shift commutation law. These are operator-level finite symmetries on the qutrit matrix carrier; the S₃ action, Weyl pair, and incidence transport statements are kept explicit. | `InfoGeometry/Canonical/A2QutritWeylTransport.lean`; `InfoGeometry/Quantum/QutritBraidIncidenceBridge.lean`; `InfoGeometry/Quantum/QutritPrimitiveWeyl.lean`; `InfoGeometry/Twistor/QutritPermutationAssociatedTwistorMonodromy.lean` |
| SU(3) color S₃/Weyl generator symmetries | `WeylSU3ColorSymmetry.lean` represents the adjacent transpositions by Mathlib permutation matrices and proves their braid relation and conjugation transport of supplied matrix-commutator identities. The owner explicitly does not prove root-pair transitivity or generate all Gell-Mann commutators from a seed, so it supplies generator-level Weyl symmetry rather than a completed root-orbit classification. | `InfoGeometry/Physics/WeylSU3ColorSymmetry.lean`; `InfoGeometry/Physics/ThreeColorSU3.lean`; `InfoGeometry/Physics/GellMannSU3.lean` |
| Groupoids and categorical automorphisms | A positive Artin action induces an autoequivalence of a fundamental groupoid; Omega's `FoldGroupoidAutChiSemidirectClassification` models the χ-preserving data using a sign-kernel subgroup of `Equiv.Perm (Fin m)` and `Bool`. The ternary Toeplitz--Cuntz boundary owner builds the S₃ action groupoid on an infinite word boundary and proves its source/target, inverse, and composition laws. | `InfoGeometry/Twistor/ProjectiveNullPositiveArtinFundamentalGroupoidEquivalence.lean`; `Omega/EA/FoldGroupoidAutChiSemidirectClassification.lean`; `InfoGeometry/Twistor/Cl55CelestialUnorderedFundamentalGroup.lean`; `InfoGeometry/Topology/ToeplitzCuntzThreeTrialityBoundaryGroupoidColimit.lean` |
| Galois and arithmetic symmetries | Galois group towers, permutation actions on roots, and arithmetic symmetry actions | `InfoGeometry/Arithmetic/PrimeCyclotomicGaloisGroupTower.lean`; `InfoGeometry/Arithmetic/RiemannZetaSymmetry.lean`; `InfoGeometry/Arithmetic/IdeleClassZetaSymmetry.lean` |
| Gauge and modular symmetries | `RightGaugeGroup` and local gauge actions; modular automorphism and CPT/chiral actions | `InfoGeometry/Optics/LocalGaugeGroupAction.lean`; `InfoGeometry/Optics/OperatorQGTGaugeModuli.lean`; `InfoGeometry/Categorical/ModularDoubledRealHopfFibration.lean`; `InfoGeometry/OperatorAlgebra/CPTSymmetryBranch.lean` |
| Möbius and projective linear symmetries | `Topology/MobiusProjectiveAction.lean` defines the quotient group `PGL2C`, a homomorphism into permutations of the Riemann sphere, its multiplication-compatible action, and a proof that this action is faithful. The related thermodynamic `sl₂` owner defines trace-zero generators, determinant-one matrix flows, and a one-parameter group law; that flow is not itself identified with the whole `PGL₂(ℂ)` group. | `InfoGeometry/Topology/MobiusProjectiveAction.lean`; `InfoGeometry/Topology/ThermodynamicSL2MobiusFlow.lean`; `InfoGeometry/Geometry/MobiusInfinitesimal.lean`; `Experimental/Sandbox/Mobius/EvalEquiv.lean` |
| Cyclic order-three homeomorphism actions and orbit spaces | `OrderThreeHomeomorphOrbitQuotient.lean` forms the orbit equivalence relation and quotient from a homeomorphism with cube equal to the identity; `OrderThreeInvariantMetricAction.lean` adds isometry and derives orbit-cost properties. This is a cyclic order-three action/quotient construction, not a classification of fixed points, orbifold structure, or a G₂ action. | `InfoGeometry/Topology/OrderThreeHomeomorphOrbitQuotient.lean`; `InfoGeometry/Topology/OrderThreeInvariantMetricAction.lean`; `InfoGeometry/Topology/OrderThreeOrbitCostDescent.lean` |
| Geometric deck and wallpaper groups | Klein bottle fundamental/deck groups and wallpaper symmetry actions. `KleinSixStateAssociatedBundle.lean` maps the free group on the presented generators to permutations of a bundle with a six-dimensional complex unitary operator fiber; under its pinning equation, it computes the relator as a central fiber operator. It does not yet show that the relator acts trivially, so it does not establish factorization through the Klein-bottle quotient group. | `Experimental/Sandbox/Topology/KleinBieberbachWeyl.lean`; `InfoGeometry/Canonical/KleinSixStateAssociatedBundle.lean`; `InfoGeometry/Topology/WallpaperSymmetry.lean`; `InfoGeometry/Topology/WallpaperRepresentations.lean` |

Additional group-theoretic carrier owners include `ConcreteSplitCartan.SplitCartanGroup`, a subgroup of units in the actual coefficient algebra; G₂'s Weyl subgroup and its linear Cartan image; point stabilizers inside the real Zorn composition-automorphism group; and the split-Cayley stabilizer inside linear equivalences preserving the actual Zorn product. `CuntzBraidExpectationIntertwiner` gives a permutation hom into automorphisms of the noncommutative Cuntz algebra. These carriers are distinct from their root-label, finite-point, or matrix readouts. By contrast, double-coset equivalence relations, generic generated-set stabilizers, and supplied-hypothesis BN₂ peeling statements are reusable action/group lemmas, not additional exceptional groups. `Exceptional/G2ArtinPresentation.lean` defines the kernel of the Artin-to-Weyl quotient; its concrete root-permutation bridge is recorded alongside the G₂ Weyl owners. The diagonal triality Lie subalgebra is not promoted as an operator symmetry group. The inspected sources include `InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean`, `InfoGeometry/Algebra/KingdonArtinBraidAction.lean`, `InfoGeometry/Algebra/KingdonPeterssonIsotope.lean`, `InfoGeometry/Algebra/SplitCayleyF2LiteratureGenerators.lean`, `InfoGeometry/Algebra/Zorn/BruhatPeelingTransport.lean`, `InfoGeometry/Algebra/Zorn/GaloisPeelingFiltration.lean`, `InfoGeometry/Algebra/Zorn/KingdonCanonicalBridge.lean`, `InfoGeometry/Algebra/Zorn/LeviRootDecompositionBN2.lean`, `InfoGeometry/Algebra/Zorn/SplitCayleyStabilizer.lean`, `InfoGeometry/Lie/ConcreteSplitCartan.lean`, `InfoGeometry/Lie/SplitOctonionImaginaryAction.lean`, `InfoGeometry/Lie/CanonicalZornG2BasisAlignment.lean`, `InfoGeometry/Lie/CanonicalZornPeirceStabilizer.lean`, `InfoGeometry/Lie/CanonicalZornG2WeylGroupAction.lean`, `InfoGeometry/Lie/CanonicalZornG2CoxeterRelations.lean`, `InfoGeometry/Lie/SplitOctonionEllStabilizer.lean`, `InfoGeometry/Exceptional/G2ArtinRootPermutationLift.lean`, `InfoGeometry/Exceptional/G2ArtinPresentation.lean`, `InfoGeometry/Exceptional/G2PhaseTransport.lean`, `InfoGeometry/Exceptional/G2ArtinWeylBridge.lean`, `InfoGeometry/GroupTheory/GeneratedSetExhaustion.lean`, `InfoGeometry/GroupTheory/DoubleCoset.lean`, `InfoGeometry/GroupTheory/DoubleCosetOrbit.lean`, `InfoGeometry/Categorical/ArtinGarsideCenterBridge.lean`, `InfoGeometry/Categorical/LogJordanTensorPowerStabilization.lean`, and `InfoGeometry/Algebra/CuntzBraidExpectationIntertwiner.lean`.

The G₂ dihedral Weyl model now has an explicit noncommuting-pair witness on
the concrete split-octonion automorphism subgroup: the two reflection
generators are transported from `DihedralGroup 6` through
`dihedralWeylMulEquiv`. The theorem is kernel-checked in
`InfoGeometry.Algebra.Zorn.G2WeylDihedralEquiv`; it gives a concrete
noncommutative algebra-automorphism carrier rather than a scalar or diagonal
model.

The projective, categorical, and twistor candidates further distinguish
central/unit subgroups and braid kernels from actions on projective or
configuration labels. `ProjectiveUnitary6.lean` aliases the center of the
existing noncommutative unitary group, `KleinQuadricLogCharacter.lean` uses the
commutative unit-circle subgroup only as a character target, and the
configuration owners provide permutation actions. The braid centralizer,
stabilization, and pure-braid kernel declarations are genuine subgroups of
the presented braid group. Twistor `kinematicStabilizer` is an actual subgroup
of permutations of the packet carrier; the momentum and configuration maps
are readouts/actions. Sources: `InfoGeometry/Categorical/ArtinGarsideCenterBridge.lean`,
`InfoGeometry/Categorical/LogJordanTensorPowerStabilization.lean`,
`InfoGeometry/Projective/ProjectiveUnitary6.lean`,
`InfoGeometry/Projective/KleinQuadricLogCharacter.lean`,
`InfoGeometry/Projective/HadjiivanovRankTwoBraidFrame.lean`,
`InfoGeometry/Projective/TwistorConfigurationSpace.lean`,
`InfoGeometry/Twistor/ProjectiveNullUnorderedConfiguration.lean`,
`InfoGeometry/Twistor/RealMomentumTwistor.lean`,
`InfoGeometry/Twistor/TwistorInternalSymmetry.lean`,
`InfoGeometry/Twistor/RollingSpinorMobiusBridge.lean`, and
`InfoGeometry/Twistor/Cl55CelestialOrderedExchangePureBraidMonodromy.lean`.

The remaining indexed owners include the fixed subgroup of a group
automorphism in the symmetric-space layer, the SU(3) subgroup of the actual
unitary matrix group, the six anharmonic permutations of the punctured sphere,
and a crossed-product group-unitary map for the D₄-star color action. The
wallpaper module's translation subgroup and the parabolic stabilizer in
`RealSL2` are likewise actual subgroups. The Clifford CAR quadratic owners
are infinitesimal Lie subalgebras in `Cl(n,n)`; the other Weyl, cocycle,
matching, and weight declarations in this batch are action or invariant data.
Generic double-coset, quotient, action-cocycle, and generated-set APIs are
reusable constructions parameterized by arbitrary groups, not new named
families. Sources: `InfoGeometry/Architecture/SymmetricSpace.lean`,
`InfoGeometry/Arithmetic/ConnesFiniteTraceBridge.lean`,
`InfoGeometry/Arithmetic/PrimeValuationLatticeWeyl.lean`,
`InfoGeometry/AsanoRuelle/MobiusPoleScaleAction.lean`,
`InfoGeometry/Cocycle/ActionCocycle.lean`,
`InfoGeometry/Cocycle/LogarithmicOrderParameter.lean`,
`InfoGeometry/Core/DoubleCoset.lean`, `InfoGeometry/Core/HomogeneousSpaces.lean`,
`InfoGeometry/Core/SymmetricSpaces.lean`, `InfoGeometry/Core/TitsExhaustion.lean`,
`InfoGeometry/Cosmology/SpacetimeParabolicQuotient.lean`,
`InfoGeometry/External/Auto/BogoliubovBraidGraphWeld.lean`,
`InfoGeometry/External/Auto/SUNLoopBraidCuntzBoundary.lean`,
`InfoGeometry/External/Auto/SouriauCasimirEntropyLeaves.lean`,
`InfoGeometry/External/Auto/WallpaperSemidirectProduct.lean`,
`InfoGeometry/Geometry/AnharmonicPunctures.lean`,
`InfoGeometry/Geometry/AnharmonicSixPermutations.lean`,
`InfoGeometry/Geometry/CocyclicDressing.lean`,
`InfoGeometry/Geometry/PenroseBraidCliffordDigest.lean`,
`InfoGeometry/GrandUnification/TypeDWeylSemidirectAction.lean`,
`InfoGeometry/MassSpectrometry/PeakFragmentMatching.lean`,
`InfoGeometry/OperatorAlgebra/D4StarFiniteCrossedProduct.lean`,
`InfoGeometry/Physics/SouriauEntropyFoliation.lean`,
`InfoGeometry/Physics/SplitCliffordAlgebras.lean`,
`InfoGeometry/Quantum/KrausBoundaryDuality.lean`,
`InfoGeometry/Quantum/QutritMobiusTripotentOrientationBridge.lean`,
`InfoGeometry/Riemannian/ConeAction.lean`,
`InfoGeometry/Routing/FunctionalRouteCore.lean`,
`InfoGeometry/Routing/PermutationPerfectMatching.lean`,
`InfoGeometry/Spectral/Algebra/QuotientGroup.lean`,
`InfoGeometry/Spectral/Algebra/Subgroup.lean`,
`InfoGeometry/SuperGrassmannian/TrialityGrothendieckGroupAction.lean`,
`InfoGeometry/Synthesis/FisherSouriauGroupInversePermutation.lean`,
`InfoGeometry/Synthesis/FisherSouriauMoorePenrosePermutation.lean`,
`InfoGeometry/TKK/TKKFramework.lean`,
`InfoGeometry/Volume/FunctorialCocycleCalculus.lean`, and
`InfoGeometry/Volume/OrientedPfaffian.lean`.

The remaining topology-indexed owners add the topological subgroup `PinMinus55`
of units in the opposite split Clifford algebra, Klein deck actions by plane
permutations, and D₄-star color actions descended to graph and quotient
carriers. The spinor glide file defines two specific permutations on the total
cover carrier; those are transformations, not a claimed full symmetry group.
`D4StarQuotientFactorization.lean` and `MobiusSouriauThermodynamicFlow.lean`
are action/readout owners. These sources are
`InfoGeometry/Topology/D4StarQuotientFactorization.lean`,
`InfoGeometry/Topology/D4StarGraphContinuousAction.lean`,
`InfoGeometry/Topology/Pin55TopologicalGroups.lean`,
`InfoGeometry/Topology/KleinDeckRepresentation.lean`,
`InfoGeometry/Topology/D4StarGraphQuotient.lean`,
`InfoGeometry/Topology/D4StarQuotientContinuousAction.lean`,
`InfoGeometry/Topology/KleinBieberbachWeyl.lean`,
`InfoGeometry/Topology/KleinBottleSpinorGlide.lean`,
`InfoGeometry/Topology/D4StarDiscreteColorFlow.lean`,
`InfoGeometry/Topology/PauliJungD4StarTopology.lean`, and
`InfoGeometry/Topology/MobiusSouriauThermodynamicFlow.lean`.

The uniform exceptional root-coordinate Weyl subgroup lives in the full
`ℤ^rank` coordinate lattice, generated by the integral simple-reflection
equivalences from the local Chevalley root data. Its source-level proof
preserves the existing inductive `IsRoot` predicate. Its faithful action on
Boolean configurations is by inverse reindexing and is packaged as a
permutation representation. Since each lattice is countably infinite, the
owner reindexes configurations to the repo's `CantorWord` carrier and defines
an isomorphic Weyl image subgroup there. This is distinct from the finite
signed-root permutation representation supplied by Coxeter, and no
relationship to the Brin–Thompson simple group is established.

These families overlap: a Weyl group can also be finite and Coxeter, while a
braid representation can induce a permutation action. The source contains many
specialized bridges and readouts beyond the representative owners in this
table.

### Cantor random Markov operators and the Clifford symmetry closure

`InfoGeometry.Clifford.ClNNPermutationSymmetry` uses a genuine noncommutative
carrier: automorphisms of the finite split Clifford algebra and automorphisms
of its exterior-Fock algebra. It defines the generated permutation symmetry
closures and the linear operator
`randomPermutationCliffordAverage`, a finite weighted sum of those algebra
automorphisms. The same owner defines conjugation automorphisms on the full
endomorphism algebra of the Fock module, the subgroup they generate, and a
Birkhoff-weighted linear channel on that noncommutative operator algebra. The
Birkhoff theorem decomposes finite doubly-stochastic matrices into permutation
matrices; the Clifford and Fock-operator averages preserve their respective
units for normalized weights.

The owner proves `randomPermutationCliffordAverage_generator`: on every
Clifford generator, the average is the corresponding weighted sum of the
genuine permuted generators. This closes the immediate operator-action gap
without promoting the coefficient matrix to the symmetry carrier. `exists_randomPermutationCliffordAverage_primalMatrixAction` supplies
inverse-reindexed Birkhoff weights for each doubly-stochastic matrix and proves
its exact action on primal Clifford generators, matching the pullback
convention. Fock mode permutations now also intertwine CAR annihilation under
the dual mode action, and `randomFockOperatorAverage_annihilation` proves the
exact weighted action on annihilation operators in the full operator algebra.
`Cantor/CliffordMarkovOperators.lean` now proves this intertwining on each
normalized Cantor finite-mode Clifford generator and proves the corresponding
weighted channel action. Intertwining on the full split-Clifford
representation `towerFockRep` and any multiplicative or automorphism property
for the Clifford-carrier average remain open. The owner proves that composing two Clifford-carrier averages expands
to the ordered-pair average of their successive permutation actions. The
Fock-operator channel has the corresponding ordered-pair composition formula.
General bistochastic averages remain Markov operators / channels; the
invertible permutation automorphisms form the symmetry group. Identifying any smaller
invertible Markov subgroup requires a separate proof. Carrier alignment must
also be carried through the Cantor configuration action and the direct-limit
inclusions before claiming a Cantor-boundary Markov symmetry closure.

`InfoGeometry.Cantor.CantorRandomWalk` provides binary-sequence bit flips.
`InfoGeometry.Cantor.CliffordMarkovOperators` now supplies finite-mode
represented Clifford operators on the Fock module, with involution and
cross-mode CAR theorems; this is the noncommutative operator carrier. It also
proves that the finite Fock symmetry closure permutes these operators by
conjugation and that the Birkhoff Markov channel acts by their weighted sum.
A random Markov average on the infinite Cantor-word carrier and compatibility
with the infinite Cantor permutation group remain unproved.
`SimpleCantorPermutationGroup`
provides a separate simple permutation group on the Cantor-word carrier; no
Markov-operator or Clifford-closure relation is currently proved between it
and the finite-stage Clifford permutation group. `SimpleCantorOperatorGroup`
now faithfully represents that simple group by invertible linear operators on
real-valued functions on the Cantor-word carrier, proves the operator-unit map
injective by function probes, and transports simplicity to the image subgroup
of endomorphism units. This supplies an operator realization of the imported
simple Cantor group; it does not yet identify that image with the Clifford
operator closure or with a stochastic Markov subgroup.

### Cantor-boundary Weyl claim: owner-level status

`InfoGeometry.Experimental.WeylCantorFock` is imported by
`InfoGeometry.AllExhaustive`, so its declarations are in the exhaustive source
surface. Its `CantorWeylData` is a structure carrying a natural-number order,
a sign function, and a bit-stream action function. The inspected declaration
does not equip this data with a group operation, prove group axioms, provide a
`MulAction`, or connect the data to the D₄/root-lattice Weyl subgroups. The
module's prose calls the intended object the infinite hyperoctahedral group
`(ℤ/2)^ℕ ⋊ S_∞`, but that prose is not an implemented group declaration. Its
`signFlipInvariant_readback` theorem takes invariance as an input hypothesis
and returns that same equality; it does not establish a Cantor Weyl symmetry
action. By contrast, the external OAI Brin/Thompson modules contain constructed
groups with simplicity proofs and their local actions, and selected such
results are imported at the root as listed below. This distinction identifies
a concrete gap for the requested Cantor/root-Weyl bridge.

The OAI Cantor-cube carrier is explicit: in
`OAI.FiniteAlgebraicEnvelopes.TwistedBrinThompson`, `Cube X` is
`X → Stream' Bool`, and `group` is a subgroup of `Equiv.Perm (Cube X)` generated
by permutations admitting finite twisted dyadic tables. The owner proves
`infinite_group_simple` when `X` is infinite. Separately,
`OAI.TwistedBrin.localGroup ρ` is built from a group action
`ρ : A →* Equiv.Perm S`, and `localGroup_simple` proves it simple when `S` is
infinite. These are concrete permutation groups/actions on symbolic bitstream
cubes; the inspected owners do not provide a topological `Homeomorph` group
instance for the product space. Root imports of the theorem modules establish
the declarations' import surface, while current owner builds remain the
verification evidence for those imports.

## External Lean simple-group source scan

The external-reference pass searched exact `IsSimpleGroup`,
`isSimpleGroup`, and `SimpleGroup` identifiers, then read each non-CFSG owner
that matched. This distinguishes theorem owners from files that only assume
simplicity or contain generated proof attempts. Outside `external_refs/CFSG`,
the current hits are:

| External source | Files | Source-level result | Root status |
|---|---:|---|---|
| `openai-math` | 24 | 21 OAI theorem/support files under `OAI/GroupTheory/` plus three `ComparatorChallenges` summaries | All 21 OAI files are imported by the root entrypoints; the comparator summaries are not Lean proof imports. |
| `atlas-lean` | 2 | `GaloisTheory.lean` uses the Mathlib simplicity theorem for A₅; `SimpleGroups.lean` proves simplicity of `SU(2)/Z(SU(2))` from its SU₂ normal-subgroup classification | A₅ is already covered by the root alternating-family API. The SU₂ quotient theorem was not found in repo-owned Lean and remains a local-port candidate. |
| `LeanCamCombi` | 1 | `GrowthInGroups/Lecture1.lean` states Babai's conjecture with `[IsSimpleGroup G]` as an assumption and uses `showcased`; `LeanCamCombi/Util.lean` declares `axiom showcased {P : Prop} : P` | An admitted proposition, not a proof of a named simple group; do not import as a theorem result. |
| `LeanAide` | 3 | Similarity-search `TestResults/false-*` files contain generated `IsSimpleGroup` statements with `by sorry` | Generated attempts, not library proof owners and not import candidates. |
| `atlas-lean` Galois A₅ statement | included above | Reuses `alternatingGroup.isSimpleGroup_five` | Duplicate use of the root Mathlib theorem, not a new group proof. |

In `external_refs/CFSG/CFSG`, exact `IsSimpleGroup` text occurs in 23,072
Lean files in the full tree, 141 files under `LieType/`, and 254 under
`Sporadic/`. These are file-match counts, not theorem-owner counts; the CFSG
tree contains large certificate and proof-support subtrees. Its direct family
theorem owners and root-port status are tracked in
`CFSG_EXCEPTIONAL_PORT_STATUS.md`.

The non-CFSG source scan is reproducible with:

```bash
find external_refs -mindepth 1 -maxdepth 1 -type d ! -name CFSG -print0 \
  | xargs -0 rg -l --glob '*.lean' --glob '!**/.lake/**' \
      '\b(IsSimpleGroup|isSimpleGroup|SimpleGroup)\b'
```

This scan is navigation evidence. A source match counts as a proved result
only after its exact declaration, dependencies, assumptions, and kernel status
are checked.

## Finite-simple-group search in repo-owned Lean

A current repo-wide search over `lean/**/*.lean` for the exact terms
`IsSimpleGroup`, `SimpleGroup`, `SporadicRep`, and `alternatingGroup` returns
18 source lines in seven files: ten lines in the CFSG port and eight lines in
three `Omega` files. The CFSG lines include cyclic-prime, alternating, and
PSL₂-model simplicity lemmas, the alternating-family model, and the sporadic
carrier predicate; the `Omega` lines use alternating groups in Galois-group
hypotheses. `IsSimpleGroup` occurs in the new
`CFSGPort/SimpleFamilyCatalog.lean` and
`CFSGPort/ClassicalSimpleFamilyCatalog.lean`; the separate exact string
`SimpleGroup` does not occur. This is an exact-string result, not a claim that no differently
named simplicity predicate or construction exists. The command was:

```bash
rg -n --glob '*.lean' '\b(IsSimpleGroup|SimpleGroup|SporadicRep|alternatingGroup)' lean
```

The three `Omega` owners are
`Omega/SyncKernelWeighted/RealInput40P7Branch10GaloisS10.lean`,
`Omega/SyncKernelWeighted/WeightedNewmanQGaloisS37.lean`, and
`Omega/POM/A4TNewmanOcticFieldGaloisS8.lean`. The four CFSG owners are
`CFSGPort/ModelCatalog.lean`, `CFSGPort/SimpleFamilyCatalog.lean`,
`CFSGPort/ClassicalSimpleFamilyCatalog.lean`, and
`CFSGPort/SporadicGroups.lean`.

## Non-Lean group and symmetry sources

The repository also contains mathematical group computations and declarations
outside Lean. These are separate evidence: a GAP `Group(...)` computation or a
Coq/Isabelle structure does not establish a Lean theorem or join the Lean
import graph.

| Source | Symmetry/group material located | Evidence status |
|---|---|---|
| 79 GAP files in `scripts/` and `tools/` matching the group/Weyl/G₂/triality scan | Finite matrix and permutation groups, G₂ flag stabilizers and Bruhat/Weyl calculations, D₄ Weyl orbits and triality stabilizers, F₄ generators, split-octonion G₂, braid/Weyl actions, and specific finite quotient computations | GAP computations or scripts; inspect each script's assertions and execution status before treating an output as certified |
| `tools/infra/bridge_data/E8Triality.v` | Coq records/constants for E₈ dimensions and functions on Spin(8) representations with order-3/order-2 triality claims | Coq source; not a Lean declaration, and proof completeness/build status is separate |
| 22 Coq, Isabelle, M2, Sage, and Julia files matching the group/symmetry/Weyl/triality declaration scan | Wallpaper representations, isospin/triality structures, mirror symmetry, TKK symmetry statements, and split-octonion/G₂ classification sources | Coq/Isabelle definitions, axioms, and lemmas; assess assumptions and proof status per file |
| 39 Python files matching the group/Weyl/triality/Galois scan | Root-system, G₂/split-octonion, D₄ triality, Weyl/permutation and finite matrix calculations | Symbolic/computational evidence, not kernel-checked Lean group proofs |

Representative GAP owners include `scripts/derive_g2_native_flag_stabilizer.g`,
`scripts/verify_g2_true_bruhat_cover.g`,
`scripts/classify_g2_weyl_rank_one_carriers.g`,
`tools/gap/d4_triality_orbit_stabilizers.g`, `tools/gap/f4_generators.g`, and
`tools/gap/dual_split_octonion_group_backbone.g`. This map comes from
extension-specific searches over `src/`, `tools/`, and `scripts/`; it is a
candidate map, not a line-by-line semantic audit of every such file.

The non-Lean search counts above use these reproducible searches:

```bash
rg -l --glob '*.g' --glob '*.gap' 'Group\(|Weyl|G2|triality|sporadic|AlternatingGroup|SymmetricGroup' scripts tools
rg -l --glob '*.py' --glob '!**/test*' 'FiniteGroup|PermutationGroup|DihedralGroup|LieGroup|WeylGroup|triality|Triality|GaloisGroup|galois_group|class\s+\w*(Group|group)' src tools scripts
rg -l --glob '*.v' --glob '*.thy' --glob '*.m2' --glob '*.sage' --glob '*.jl' '(Definition|def|theorem|lemma|inductive|structure|class)[^\n]*(group|Group|symmetry|Symmetry|Weyl|triality)' src tools scripts
```

The import surfaces are not identical to the full source tree. The root
`InfoGeometry.lean` and the canonical `InfoGeometry.All` umbrella import
`InfoGeometry.Exceptional.CFSGPort.All`, Coxeter adapters, and the selected
OAI simple-group modules. `InfoGeometry.All` imports `InfoGeometry.AllExhaustive`,
which in turn imports `InfoGeometry.Cantor.All`, `InfoGeometry.Lie.All`, and
`InfoGeometry.RootSystem.All`; `Omega.lean` separately imports the Omega group
and symmetry modules. Thus the inventory below includes declarations from the
source tree even when a narrower root entrypoint does not import that owner.

### Declaration-level review: first ten distinct indexed owners

To turn the high-recall declaration index into a semantic inventory, the first
ten distinct owner files encountered in
`SYMMETRY_GROUP_CARRIER_DECLARATIONS.txt` were checked at the indexed
declarations and their relevant consumers. This batch distinguishes groups
and actions from infinitesimal algebras, presentation data, and individual
permutations.

| Candidate declaration | Source-level classification | Operator-carrier status |
|---|---|---|
| `Experimental/Sandbox/Topology/KleinBieberbachWeyl.lean:KleinNormal`, `KleinGroup` | `KleinNormal` is the normal closure of the Klein-bottle relator in a free group; `KleinGroup` is the corresponding quotient fundamental-group presentation. The inspected declarations establish the relation, not a symmetry action. | No endomorphism-unit or operator action is supplied by these declarations; do not count the presentation as an operator symmetry group. |
| `Algebra/BaezF4H3Zorn.lean:H3ZornF4Derivations`; `Algebra/F4Derivations.lean:H3ZornDerivationLieSubalgebra` | Lie subalgebras of endomorphisms consisting of Jordan derivations; the latter aliases the former. These are infinitesimal symmetry algebras, not separate global groups. | The carrier is genuinely noncommutative `Module.End`, but a corresponding global automorphism subgroup is not established by these declarations. |
| `Algebra/Clifford55GaugeSubalgebraBridge.lean:smStabilizerLieSubalgebra` | Lie subalgebra of the `HMatrix` commutator algebra stabilizing the stated idempotent system. | Noncommutative infinitesimal carrier; no global subgroup is defined by this declaration. |
| `Algebra/CuntzBraidExpectationIntertwiner.lean:permCuntzAction`, `permutedRangeProjector` | `permCuntzAction` is a monoid hom from `Equiv.Perm (Fin n)` to algebra automorphisms of the noncommutative Cuntz quotient, with generator, relation, and composition proofs. `permutedRangeProjector` is an image/readout of that action, not another group. | Actual noncommutative algebra-automorphism carrier. It is distinct from the Fock endomorphism-unit channel carrier. |
| `Algebra/CuntzLorentzPoincarePresentation.lean:PoincareTransformGroup`, `affineEquiv`, `affinePoincareElement` | The first is the subgroup of permutations of four-vectors preserving the squared Minkowski interval; `affineEquiv` proves affine Lorentz-plus-translation maps are permutations, and `affinePoincareElement` embeds each such map into the subgroup. New declarations `poincareObservableOperatorRep` and `poincareObservableOperatorGroup` add a faithful pullback representation on the invertible endomorphisms of real four-vector observables. | The operator representation and injectivity proof have been written, but the focused kernel check is still waiting on the shared build lock; do not count them as verified yet. |
| `Algebra/H3ZornCubicOperatorGeometry.lean:h3zornCubicStabilizer` | Lie subalgebra stabilizing the trilinear cubic norm; its norm-similitude transport is an induced Lie equivalence. It is not itself a global group. | Endomorphism Lie algebra only; do not promote to an operator-unit group without a proved integration/action map. |
| `Algebra/H3ZornInfinitesimalReconstruction.lean:h3zornUnitAnnihilator` | Lie subalgebra of endomorphisms annihilating the distinguished unit. It is an infinitesimal constraint carrier, not an automorphism group. | Noncommutative endomorphism carrier, but no group structure or global action in this declaration. |
| `Algebra/KingdonArtinBraidAction.lean:sigma1`, `sigma2`; `Algebra/KingdonPeterssonIsotope.lean:peterssonCyclePermutation` | Two adjacent transpositions and a three-cycle in `S₃`, used as braid and coordinate-permutation readouts. These elements do not define three additional groups; the owners explicitly do not assert the full Kingdon-carrier action/isotope construction. | Permutation data only; no noncommutative operator representation is supplied by these declarations. |

### Next indexed owner batch

The next three new owners in the index were also checked directly:

| Candidate declaration | Source-level classification | Operator-carrier status |
|---|---|---|
| `Algebra/NonAssocDerivation.lean:derivations` | Generic Lie subalgebra of linear endomorphisms satisfying the Leibniz rule for a possibly nonassociative multiplication. It is an infinitesimal symmetry algebra, not a global group. | Actual endomorphism Lie carrier with a proved commutator-closure law; integration to an automorphism group is not supplied here. |
| `Algebra/SpecialUnitary.lean:su` | The real Lie subalgebra of skew-Hermitian trace-zero complex matrices, i.e. an infinitesimal `𝔰𝔲(n)` carrier. The declaration is not the special-unitary matrix group. | Matrix Lie algebra only; no operator-unit group construction is given by this owner. |
| `Algebra/SplitAlbertInnerTraceSpan.lean:h3ZornTraceZeroLieSubalgebra` | Lie subalgebra of endomorphisms whose outputs have zero `linearTrace`; it contains the inner-derivation span, but the owner explicitly does not claim that span exhausts all Jordan derivations. | Endomorphism Lie carrier, not a group; no global noncommutative operator symmetry is identified here. |

### Further indexed owner batch

The next ten distinct owner files were read at the indexed declarations and
their relevant consumers:

| Candidate declaration | Source-level classification | Operator-carrier status |
|---|---|---|
| `Algebra/SplitAlbertStructureOperators.lean:structureOperatorLieSubalgebra` | Lie subalgebra of operators `D + Lₐ` on the split-Albert carrier; the owner proves its commutator formula and closure but explicitly does not identify it with an exceptional Lie algebra by dimension or name. | Actual noncommutative endomorphism Lie carrier, not an operator-unit group. |
| `Algebra/SplitCayleyF2LiteratureGenerators.lean:elementaryDeltaNativeSubgroup` | Subgroup generated by the named elementary automorphisms of the noncommutative split Cayley algebra over `𝔽₂`. The owner says these generators are not proved to generate the full automorphism group. | Genuine subgroup inside `SplitOctF2Aut`, the algebra-automorphism carrier. |
| `Algebra/SplitMetricLieAlgebra.lean:nativeSkewAdjointLieSubalgebra` | Native skew-adjoint endomorphisms form a Lie subalgebra; `SplitMetricLieAlgebra` is an abstract Lie-algebra-with-faithful-action record. Neither declaration constructs the global orthogonal group. | Noncommutative endomorphism Lie carrier; global group integration is not established here. |
| `Algebra/TrilinearStabilizer.lean:trilinearStabilizer` | Generic infinitesimal stabilizer of a trilinear form in `Module.End`, with closure under commutator and transport by conjugation. It is a Lie algebra, not a global stabilizer group. | Noncommutative endomorphism Lie carrier; a unit-group stabilizer is not defined in this owner. |
| `Algebra/Zorn/BruhatPeelingTransport.lean:InCell`, `CellSet`, `HasPeelingStep` | Predicates for double cosets and a conditional BN₂ peeling step. These describe Bruhat cells; they do not define new groups. | Group/subgroup parameters are supplied abstractly; no new operator group is constructed. |
| `Algebra/Zorn/CanonicalDerivationBridge.lean:canonicalDerivationLieAlgebra`, `kingdonDerivationLieAlgebra` | Exact images of native derivation Lie algebras in endomorphism Lie algebras on canonical-Zorn and Kingdon carriers. These are two represented infinitesimal algebras, not global groups. | Faithful maps into noncommutative endomorphism carriers, but no unit-group image is proved by these declarations. |
| `Algebra/Zorn/G2BN2InductivePeeling.lean:InCellBsB`, `InBruhatCover` | Bruhat-cell/cover predicates used in a word-peeling argument; not group constructions. | Abstract group parameters only. |
| `Algebra/Zorn/G2BNBruhatFramework.lean:g2weylGroup`, `concreteN` | `g2weylGroup` is generated by two named automorphisms and is proved contained in `concreteWeylSubgroup`, with cardinality at most 12. `concreteN` aliases the full concrete Weyl subgroup and has cardinality 12. The containment theorem does not identify the generated subgroup with the full Weyl subgroup. | Genuine subgroups of `SplitOctF2Aut`, acting on the concrete G₂ carrier; retain the distinction between the generated subgroup and the order-12 Weyl subgroup. |
| `Algebra/Zorn/G2BNPair.lean:doubleCoset`, `quotientOrbit` | Generic double-coset and quotient-orbit definitions, with transport theorems and an abstract Tits-system interface. These are action/cell data, not additional ambient symmetry groups. | Uses supplied group actions and subgroup carriers; no new noncommutative operator group is defined. |
| `Algebra/Zorn/G2BruhatResidual.lean:residualSubgroup` | A Weyl-parameterized family `U ∩ (w₀w)⁻¹ U (w₀w)` of actual subgroups of `SplitOctF2Aut`. The longest-parameter case is proved equal to the 64-element unipotent subgroup; general cardinal formulas are stated from explicit equivalence hypotheses. | Genuine subgroups inside the noncommutative algebra-automorphism group; a parameterized family of subgroups, not ten separate ambient groups. |

### G₂ finite-generator and coset-action candidates

The following nine distinct owner files continue the same candidate-index
review. Their proof dependencies were traced where the owner claims subgroup
equality or generation.

| Candidate declaration | Source-level classification | Operator-carrier status |
|---|---|---|
| `Algebra/Zorn/G2BruhatResidualSimpleEquiv.lean:canonicalResidualGeneratedSubgroup` | Subgroup generated by canonical PC words inside a Weyl residual subgroup. The owner separately proves the canonical word image has 8 elements, is not the full residual carrier, and the residual carrier has cardinality 32; it does not establish the generated subgroup's own cardinality here. | Actual subgroup of `SplitOctF2Aut`; the canonical image is proper in the residual carrier, not a new simple-group carrier. |
| `Algebra/Zorn/G2CASGeneratorSubgroup.lean:casGeneratedSubgroup` | Closure of the six CAS automorphism generators; proved equal to `flagGeneratedSubgroup`. The equality does not itself identify either with the full ambient automorphism group. | Genuine subgroup of the split-octonion automorphism group. |
| `Algebra/Zorn/G2CASNativePointAction.lean:casPointPerm`, `correctedTPointPerm` | Individual permutations of the 63-point carrier, with proved intertwining against specified native automorphisms. This owner does not package all generators into a group homomorphism from `SplitOctF2Aut`. | Permutation readouts on a finite point carrier; no noncommutative operator representation is defined here. |
| `Algebra/Zorn/G2ConcreteBN2CorrectSecondConjugation.lean:correctedTComplementSubgroup`; `G2ConcreteBN2FirstConjugation.lean:swap01ComplementSubgroup` | Subgroups generated by five of the six PC generators, omitting respectively the zeroth or first coordinate generator. The owners prove corresponding PC-word containment in the unipotent subgroup. | Genuine subgroups of `SplitOctF2Aut`; these are complementary subgroups within the existing finite unipotent carrier. |
| `Algebra/Zorn/G2ConcreteGeneratorInfrastructure.lean:concreteBNGeneratorSubgroup` | Closure of the unipotent subgroup and two simple Weyl generators. The owner proves containment in the flag-generated subgroup; downstream `G2NativeCellDecomposition.BN_generators_eq_top` proves it is top using `G2CorrectedBruhatCover.concrete_cover` and the corrected quotient/orbit certificate. | The proved top subgroup is the full `SplitOctF2Aut` carrier, a noncommutative split-octonion automorphism group. |
| `Algebra/Zorn/G2CorrectedTComplementCard.lean:zeroBitPCSubgroup` | Explicit subgroup of PC words whose zeroth bit is false; it is proved equal to `correctedTComplementSubgroup` and has cardinality 32. This is another presentation of the preceding complement subgroup, not a separate group. | Genuine subgroup of `SplitOctF2Aut`. |
| `Algebra/Zorn/G2CosetActionHomomorphism.lean:permComm` | Defines the commutator of two elements of `Equiv.Perm (Fin 63)` and proves an involution identity. The owner describes its coset action as an abstract contract and explicitly does not construct the concrete action from `SplitOctF2Aut`. | Permutation helper only; no concrete group representation or operator carrier is provided here. |
| `Algebra/Zorn/G2CoxeterGeneratingEquality.lean:casSubgroup` | Closure of the CAS Coxeter generators; `cas_lean_generating_equality` proves equality with `concreteWeylSubgroup`, and `casSubgroup_card_eq_twelve` proves order 12. Keep distinct from `g2weylGroup`, for which only containment and an upper bound are established in `G2BNBruhatFramework.lean`. | Genuine Weyl subgroup inside `SplitOctF2Aut`, acting through algebra automorphisms. |

### G₂ root, coset, and incidence candidates

The next ten distinct owner files in the index were checked at their
definitions and action/group laws:

| Candidate declaration | Source-level classification | Operator-carrier status |
|---|---|---|
| `Algebra/Zorn/G2CyclotomicSignedRootBridge.lean:cyclotomicS1Perm`, `cyclotomicS2Perm`, `cyclotomicCoxeterPerm` | Three permutations of the signed-root coordinate carrier, with proved signed-root intertwining and sixth-power identity for the Coxeter element. The owner does not define their generated subgroup as a separate group. | Root-coordinate permutation representation data; not an endomorphism-unit realization. |
| `Algebra/Zorn/G2FlagAndParabolicQuotient.lean:cosetProj`, `InDoubleCoset` | Quotient projection, fiber, and double-coset definitions/theorems for supplied groups and subgroups. These are quotient and cell constructions, not new symmetry groups. | Inherits whatever group carrier is supplied; no new operator group. |
| `Algebra/Zorn/G2FlagIncidenceAction.lean:PreservesIncidence`, `flagPerm` | Incidence-preserving permutations are closed under identity, composition, and inverse; each induces a permutation of incident flags. The owner does not package the preserving permutations as a subgroup or prove that a specified automorphism family preserves the incidence certificate. | Permutation action on finite incidence data; no noncommutative operator carrier or full group representation is provided here. |
| `Algebra/Zorn/G2FlagWordEvaluator.lean:flagGeneratedSubgroup` | Subgroup generated by the native flag-word generators. `G2CASGeneratorSubgroup.lean` proves it equals the CAS-generated subgroup, so it is the same subgroup already inventoried above. | Genuine subgroup of `SplitOctF2Aut`; do not count the two names as distinct groups. |
| `Algebra/Zorn/G2GAPCosetHomomorphismBridge.lean:actionHom` | Generic construction of a group homomorphism `G →* Equiv.Perm (Fin n)` from left translation on `G ⧸ H` and an explicit enumeration. This is a genuine permutation representation contract for supplied `G,H,enum`, not a new concrete G₂ group. | Permutation representation of the supplied group; it does not itself construct an endomorphism-unit representation. |
| `Algebra/Zorn/G2GaloisCorrespondence.lean:galoisStabilizer` | Pointwise stabilizer in `SplitOctF2Aut` of a specified subset of the split Cayley algebra, with subgroup operations proved. It is a genuine stabilizer subgroup. | Subgroup of the noncommutative algebra-automorphism carrier. |
| `Algebra/Zorn/G2ImaginaryOctImBridge.lean:octImPointPerm`; `G2ImaginaryPointPermutation.lean:pointPerm` | Multiplicative permutation representations of `SplitOctF2Aut` on the 63 isotropic imaginary-octonion points, once on the native subtype and once transported to `Fin 63`. These are the same action under the proved point equivalence, not two groups. | Actual group action on points, represented by permutations; faithfulness is not asserted by these declarations. |
| `Algebra/Zorn/G2IndexTwoRankOneBN2.lean:InCellBsB`, `InBruhatCover` | Generic double-coset predicates and a conditional index-two rank-one BN₂ theorem. These are Bruhat criteria, not group constructions. | Group and subgroup carriers are parameters. |
| `Algebra/Zorn/G2NativeFlagStabilizerTransport.lean:nativeFlagStabilizer` | Stabilizer subgroup of the intrinsic base flag under the existing `SplitOctF2Aut` action; the owner proves PC-word elements fix that flag. | Genuine subgroup of the noncommutative algebra-automorphism group. |

The next candidate owner, `G2NativeFullFlagAction.lean`, remains for the next
review batch; this table does not imply that the 562-row index is complete.

These batches add source-level distinctions, not a completeness claim for the
562-row candidate index. The remaining owners still require the same
definition/import/consumer review before the full declaration-level inventory
can be called complete.

## External exceptional Lie type catalog

`external_refs/CFSG/CFSG/Blueprint/Chevalley.lean` defines root-system tags
G₂, F₄, D₄, E₆, E₇, and E₈. Its
`CFSG/Blueprint/Catalog.lean` defines model predicates for the exceptional
Chevalley families G₂, F₄, E₆, E₇, E₈, twisted ²E₆ and triality ³D₄; its Ree/Tits and
Suzuki models include ²G₂, ²F₄, ²B₂, and the Tits group. The universal
catalog also includes classical families, cyclic prime-order groups,
alternating groups, and sporadic groups. These are finite groups of Lie type
and associated root data; they should not be conflated with formalizations of
real or complex topological Lie groups.

## Continuous exceptional Lie symmetry status

The repo-owned continuous exceptional lane located in this scan is the real
split-octonion derivation algebra, exposed as
`InfoGeometry.Lie.CanonicalZornDerivation.canonicalZornDerivations` and
`InfoGeometry.Lie.G2SplitChevalley.RealSplitG2LieAlgebra`. Its dimension is
proved to be 14, and the root-system bridge records twelve roots and the G₂
Cartan pairing. `InfoGeometry/Lie/RealSplitOctonionG2Classification.lean`
explicitly records the current status as `exactNativeLieAlgebra`; it keeps a
native Lean equivalence to the real automorphism group as a separate status
value. The repo separately defines the real split-octonion automorphism group
and proves one-parameter flows from derivations into that group, but this does
not itself identify the full group with a Lie group integrating the derivation
algebra. The current G₂ root bridge supplies an embedded-G₂ certificate and
the twelve-root enumeration; the inspected owner does not supply the
irreducibility instance required by Mathlib's
`LieAlgebra.IsKilling.isSimple_iff_isIrreducible`. This is the immediate
missing step for proving simplicity of this real derivation algebra through
that criterion. The exceptional CFSG catalog above instead concerns finite
Chevalley and twisted groups. A search of the external `atlas-lean` Lie group
sources found general Lie-group and Lie-algebra representation theory, but did
not identify a root-importable construction of the exceptional real groups
G₂, F₄, E₆, E₇, or E₈. This is a scoped source search, not a claim about all
external mathematical projects.

The external project's universal simple-group catalog therefore contains
these families:

| Simple-group family in CFSG | External owner | Root integration status |
|---|---|---|
| Cyclic groups of prime order | `CFSG/Blueprint/Catalog.lean` | Included in the root `FiniteGroupModelCatalog` predicate |
| Alternating groups, degree at least five | `CFSG/Blueprint/Catalog.lean` | Included in the root `FiniteGroupModelCatalog` predicate |
| Classical Lie type: PSL, PSU, PSp, PΩ families | `CFSG/Open/StatedDefs.lean`; `CFSG/Milestones/FAM_classical_model_membership.lean` | Adapted model predicates and carriers in `CFSGPort/ClassicalCatalog.lean`, included in `FiniteGroupModelCatalog` |
| Exceptional Chevalley and diagram-twisted types | `CFSG/Blueprint/Chevalley.lean`; `CFSG/Blueprint/Catalog.lean` | Root port exposes root/group models for G₂, F₄, D₄, E₆, E₇, E₈, ²E₆, ³D₄ |
| Suzuki, Ree, and Tits types | `CFSG/Blueprint/Catalog.lean` | Root port exposes ²B₂, ²G₂, ²F₄, and Tits model predicates |
| The 26 sporadic groups | `CFSG/Blueprint/NativeSporadic.lean`; `CFSG/Blueprint/Catalog.lean` | Root port exposes their carrier models and `SporadicRep` in `CFSGPort/SporadicGroups.lean`, using external generator data |

The imported sporadic carrier tags are M₁₁, M₁₂, M₂₂, M₂₃, M₂₄; J₁, J₂,
J₃, J₄; Co₁, Co₂, Co₃; Fi₂₂, Fi₂₃, Fi₂₄′; HS, McL, He, Ru, Suz, O′N,
HN, Ly, Th, the Baby Monster, and the Monster. These are represented by
permutation subgroups, matrix seed groups, or a presented group as declared in
`CFSGPort/SporadicGroups.lean`; the `SporadicRep` predicate asserts an
isomorphism to one of these carriers, not their simplicity.

For J₁ specifically, `CFSGPort.J1GeneratorOrders` now defines the two seed
elements on the local unit-closure carrier through `j1GLSeedEquiv`, proves
their orders are 2 and 3, and proves the product has order 7. The external
primitive-action certificate and stabilizer-order calculation are still
needed before the imported primitive-coprime criterion yields J₁ simplicity.

The repo also has a separate split-octonion `G₂(2)` automorphism carrier. Its
`G2TwoAutomorphismOrderLedger` records GAP/Atlas order data `|G₂(2)| = 12096`
and `|G₂(2)'| = 6048`, with index two, but explicitly does not construct the
derived subgroup or prove an isomorphism/classification theorem. This finite
order ledger is not a simplicity proof and does not establish the CFSG
family theorem for adjoint `G₂(q)` when `q ≥ 3`.

`OperatorAlgebra.G2TwoOperatorRepresentation` gives this actual automorphism
carrier a faithful representation by invertible endomorphisms of real-valued
functions on the split-octonion carrier. It transports the two proved
noncommuting simple-root generators into the operator-unit image. This is a
noncommutative operator realization of the finite group; it does not upgrade
the order ledger to a simplicity theorem.

### Exceptional simplicity theorems available in CFSG

The source has actual simplicity theorems, beyond the model predicates. In
`CFSG/LieType/Simplicity/Exceptional.lean`, `fam_g2_simplicity`,
`fam_f4_simplicity`, `fam_e6_simplicity`, `fam_e7_simplicity`,
`fam_e8_simplicity`, `fam_2e6_simplicity`, and the imported
`fam_3d4_simplicity` establish `Nontrivial G ∧ IsSimpleGroup G` from the
corresponding exceptional Chevalley model. `ExceptionalConverse.lean` combines
these in `fam_chevalley_exceptional_simplicity` and also dispatches the Ree/Tits
and Suzuki families through `fam_exceptional_converse`. `TitsModel.lean`
contains `fam_tits_simplicity` and `fam_ree_tits_simplicity`; the remaining
specific owners are `Simplicity/ReeSmall.lean` and
`Simplicity/ReeLargeModel.lean` (²G₂ and ²F₄), and `Simplicity/Suzuki.lean`
(²B₂). These source declarations give a precise
integration target for the exceptional finite simple families.

They are **not imported as external modules into the root project**. The local
`CFSGPort/ExceptionalCatalog.lean` exposes corresponding model predicates, but
those predicates do not entail `IsSimpleGroup`. The generic
`QuasisimpleTransport` lemmas transfer a result only after family-specific
quasisimplicity has been proved. The external CFSG project is pinned to Lean
4.35.0-rc3 and Mathlib revision `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`,
while the root project remains on Lean 4.34.1 and Mathlib `v4.34.1`. Its source
theorems therefore cannot be treated as root-checked imports; integration
proceeds by local source ports proved against the unchanged root toolchain.
The local unconditional result covering simple-family overlap remains the PSL₂
theorem in `CFSGPort/ClassicalSimpleFamilyCatalog.lean`. A conditional G₂
family-model adapter now mirrors the external model theorem's statement shape;
it still takes local adjoint quasisimplicity as a hypothesis and is not a
replacement for the exceptional proof.

The external exceptional simplicity owner is
`external_refs/CFSG/CFSG/LieType/Simplicity/Exceptional.lean`; its imports
identify the substantive proof dependencies as Curtis--Tits exceptional
recognition, adjoint Steinberg perfectness, and the separate G₂ Steinberg
argument. The local `CFSGPort/CommutatorTorus.lean` supplies source-level
perfectness for the six untwisted adjoint root-group models over fields with
at least three elements, but does not supply the missing quasisimplicity steps
(including the required normal-subgroup and central-quotient arguments). This
external theorem dependency is a porting map, not evidence that the
exceptional simplicity proof has been locally imported.

The external-reference tree contains more group work than CFSG. A current
no-ignore scan for the broad identifiers
`IsSimpleGroup|isSimpleGroup_|LieGroup|RootSystem|WeylGroup|alternatingGroup|Exceptional`
finds 54,110 Lean files. The counts by external top-level directory are CFSG
50,785; `openai-math` 1,758; `upstream_pr_snapshots` 1,248; `atlas-lean` 111;
`ProjectiveSpace_lean4` 68; `differential-geometry` 61; `automath` 30;
`gift-framework-core` 16; `AbstractSimplicialComplex` 13; LeanAide 5;
`atlas-embeddings` 4; `ten-proofs` and `LeanMillenniumPrizeProblems` 2 each;
and one file each in `lean_test_v4160`, `aesop`, `VirasoroProject`,
`Seed-Prover`, `LeanCopilot`, `LeanCamCombi`, and `ExteriorPowers`. This
includes duplicate upstream snapshots and vendored Mathlib copies, so it is
not a count of unique mathematical constructions. Source-grounded examples
outside CFSG include:

A current no-ignore scan for the literal identifiers
`IsSimpleGroup|isSimpleGroup_` returns 30,864 external Lean files and 82,129
matching lines. By external top-level tree, 30,820 files are in CFSG; the
remaining matches are 24 in `openai-math`, ten in
`ProjectiveSpace_lean4`'s vendored Mathlib tree, four in
`AbstractSimplicialComplex`'s vendored Mathlib tree, three in LeanAide test
artifacts, two in `atlas-lean`, and one in `LeanCamCombi`. The count
intentionally includes nested `.lake/packages` mirrors; it is a token-use
count, not a count of theorem owners. The actual owner-source results are
audited separately below, and false-proposition tests, assumptions, uses, and
mirrored library files are not promoted as imported simple-group proofs.

| External owner | What the inspected declarations show | Relation to this root port |
|---|---|---|
| `lean-coxeter/Coxeter.lean` and `Coxeter/` | A Coxeter system/group API built on Mathlib: generators and Coxeter matrices, reduced words, permutation and geometric representations, bilinear forms, strong exchange/deletion, and Bruhat order with subword/lifting properties. This is directly relevant infrastructure for studying Weyl groups as reflection groups generated by root reflections. | The submodule at `external_refs/lean-coxeter` is exposed as a root Lake library. Both root entrypoints import the compatible modules used by the repository, and `InfoGeometry.CoxeterPort.OperatorRepresentation` builds a faithful representation by invertible operators on a real function module. The G₂ Coxeter adapter is separately owner-imported. The umbrella `Coxeter` module and `Coxeter.GeometricRepresentation` are not imported: the latter currently fails to build because its nondegeneracy rewrites and dependent proofs do not elaborate against the pinned Mathlib API. The submodule manifest pins Mathlib `v4.34.1` at the root commit; no root or submodule dependency pin was changed in this pass. |
| `CFSG/CFSG/Blueprint/Catalog.lean` | Universal finite-simple-group model catalog: cyclic, alternating, classical, exceptional, Suzuki/Ree/Tits, and sporadic families | External source; its group-family coverage is adapted in the imported repo-owned `CFSGPort` model catalog, but the external declaration itself is not Lake-imported |
| `atlas-lean/Atlas/AlgebraNotes/code/SimpleGroups.lean`; `GaloisTheory.lean` | A tactic proof claiming `SU(2) / Z(SU(2))` is simple, with a transitive dependency on a `sorry`, and a theorem stating simplicity of `alternatingGroup (Fin 5)` | Separate examples; the A₅ fact is already available from Mathlib as `alternatingGroup.isSimpleGroup_five`; the SU(2) result is not kernel-complete and the file is not imported wholesale |
| `atlas-lean/Atlas/LieGroups/` | Lie-group/Lie-algebra representation theory and a `LieSimplicityBridge` owner | General Lie theory; it does not add more named finite exceptional families to the CFSG catalog |
| `openai-math/lean/OAI/GroupTheory/` | Direct simple-group results include `localGroup_simple` for a twisted Brin local group, `infinite_group_simple` for a constructed infinite group, `polygonAlternatingGroup_simple` for an infinite polygon alternating group, and `SimpleAmenable.main`, which constructs an infinite finitely presented simple Følner-amenable group. `BooneHigman.Main` also proves countable and finitely generated simple overgroup theorems embedding any finitely generated group with decidable word problem | The inspected OAI theorem owners and support modules are imported from both root entrypoints. `SimpleAmenableWitness.lean` now provides a repo-owned explicit stage-206 polygon alternating subgroup witness. The current locked `InfoGeometry.All` build passes (28,137 jobs, exit code 0); the external source scan is not a claim that every OAI file has been built. |
| `LeanCamCombi/LeanCamCombi/GrowthInGroups/Lecture1.lean` | A theorem statement quantified over finite simple groups | General finite-simple-group result, not an exceptional-family model |
| `LeanAide/SimilaritySearch/RunTests/TestResults/false-*` | Contains test-case propositions/examples mentioning finite simple-group implications | Search/evaluation artifacts, not promoted theorem sources |

The three `external_refs/openai-math/lean/ComparatorChallenges/` files
`SimpleAmenable.lean`, `SimpleOvergroups.lean`, and `BooneHigman.lean` also
contain `IsSimpleGroup` statements, but their principal declarations are
proved with `sorry`. They are challenge statements, not proof owners, and are
not imported as evidence of simple-group results. The corresponding
repo-owned `OAI.GroupTheory` modules are the relevant source surface; their
kernel-checked status is determined by the root umbrella builds rather than
these challenge files.

Reproduce the external owner count without letting repository ignore rules
hide the external tree:

```bash
rg -l --no-ignore --glob '*.lean' --glob '!**/.lake/**' \
  --glob '!**/Mathlib/**' --glob '!**/mathlib/**' \
  'IsSimpleGroup|isSimpleGroup_' external_refs/openai-math/lean
```

This returns 24 files: 21 under `OAI/GroupTheory/` and the three comparator
challenge statements above. The 21 OAI files are the imported proof/support
surface; the three challenge files are excluded from proof-import claims.
A source-path-to-import comparison derives the 21 module names from those
owner paths and finds every one directly imported by both
`lean/InfoGeometry.lean` and `lean/InfoGeometry/All.lean`; this verifies import
coverage at source level, not elaboration under the current Lake configuration.

A later `InfoGeometry.All` build after the current staged integration initially
failed in four `Omega.Zeta` targets and
`InfoGeometry.OperatorAlgebra.PeirceNambuGorkov`, although its
`InfoGeometry.Clifford.All` prerequisite passed. `PeirceNambuGorkov` now passes
after correcting its noncommutative square-zero precession coefficient. The
four `Omega.Zeta` owners also pass after removing unsupported assertions of a
function-field Galois group; the proved geometric S₄ monodromy subgroup is
preserved. The exceptional root-operator Weyl import has a successful target
build. Fresh locked root builds after all repairs pass for `InfoGeometry.All`
(28,100 jobs) and `InfoGeometry` (29,349 jobs), both exit code 0; these
supersede the historical failed umbrella result above.

The 58,036-file result is a candidate scan over all material present under
`external_refs`, including mirrored snapshots; it is not an exhaustive
semantic classification of every external declaration. The root does not
directly import CFSG modules through Lake; the `CFSGPort` sources are local
adaptations, and the sporadic seed data is read from the external source tree.

The external universal `Catalog` is a model-family predicate. The separate
`CFSG.classification_finite_simple_groups` theorem in `CFSG/Statement.lean`
classifies finite simple groups by the external CFSG index and depends on the
larger CFSG development. The root imports its adapted model predicate, but not
the external `Catalog` declaration or the classification theorem.

The external-source simple-group audit found proof-level results in addition
to the imported model predicates:

For the exceptional finite Lie-type results, the seven family/converse owners
`Simplicity/Exceptional.lean`, `TrialityD4.lean`, `Suzuki.lean`,
`ReeSmall.lean`, `ReeLargeModel.lean`, `TitsModel.lean`, and
`ExceptionalConverse.lean` have a transitive closure of 953 CFSG source modules.
A source scan of that closure found no `sorry`, `admit`, or `axiom` tokens.
These remain external proof sources, not root-imported theorems. Direct Lake
integration is presently version-blocked: the root uses Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, while CFSG declares Lean
4.35.0-rc3 and Mathlib `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`. The local
`CFSGPort` imports the family models and selected Chevalley constructions; it
does not yet port the family-specific simplicity proofs. Generic
quasisimple-central-quotient transport steps have been ported locally as
`InfoGeometry.Exceptional.CFSGPort.Simplicity.isSimpleGroup_of_mulEquiv` in
`CFSGPort/QuasisimpleTransport.lean`. The general root/torus commutator identity
used by the external G₂ perfectness argument is locally proved as
`Chevalley.torus_commutator_pinnedX` in `CFSGPort/CommutatorTorus.lean`, using
the existing torus conjugation and pinned-root parameter laws. The new module
is included in `CFSGPort.All`, and the root import graph and dependency pins
were inspected. `CFSGPort.All` and the root umbrella passed locked Lean builds
under the unchanged root pins with the build cache preserved. These helpers do
not prove that any exceptional Chevalley group is quasisimple.

`Chevalley.rootSubgroup_le_commutator_of_torus` has now been added beside that
identity. It ports the next external G₂ perfectness step: a root subgroup is
contained in the adjoint group's commutator subgroup when a torus weight acts
nontrivially on its root parameter. This theorem and the following local G₂
helpers pass the locked root build with the cache preserved; they do not close
G₂ quasisimplicity. The local `Chevalley.adjointGroup_eq_rootSpan` gives the
root-span generation statement needed downstream. The same local file contains
`Chevalley.rootSubgroup_le_commutator_G2`, which transfers the simple-root
containment to every pinned root subgroup by conjugation inside the adjoint
group, and `Chevalley.isPerfect_adjointGroup_G2_of_three_le_card`, which
combines that inclusion with root-span generation. These statements are
kernel-checked in the successful root build. `Chevalley.nontrivial_adjointGroup_G2`
supplies the nontriviality witness required by the external quasisimplicity
theorem and is also kernel-checked. The generic external `CTGroupDatum`/
`isPerfect_of_rootGroup_single_le_commutator` bridge is still unported, and
proving the central-normal-subgroup condition for quasisimplicity remains a
separate task. The same local file now includes source-level ports of the
external field-cardinality and odd-G₂-Cartan helpers needed to choose those
torus parameters, and `Chevalley.simpleRootSubgroup_le_commutator_G2` for each
simple-root subgroup. A local three-clause `RootGroupCommutatorData` interface
has also been added, with a uniform instance for all six untwisted tags:
self-commutators vanish because each pinned root subgroup is abelian, and the
doubled-root clauses are vacuous by the checked reduced-root certificates.
Its root-list case split and interface are kernel-checked. The local port also contains
`cartanInvG2`, its matrix-inverse identity, and `isIndecomposable_cartan_G2`,
matching discrete inputs in the external G₂ `Extras` and `Perfect` modules;
these proofs pass the locked root build. The exact external conclusion path is
`g2_isCTGroupDatum`, `g2_steinbergExtras`, `g2_bruhatExtras`,
`g2_rootGroupCommutators`, `isIndecomposable_cartan_G2`, and
`isPerfect_g2`, assembled by `TitsSimplicity.isQuasisimple`. The local port
has the perfectness, nontriviality, reduced-root commutator interface, and
Cartan indecomposability inputs, but its local root-group API is not yet
packaged as a compatible `IsCTGroupDatum`, and the Steinberg normalizer and
Bruhat data are absent. The comparison with external
`SteinbergExtras` is more specific: local `rootSubgroupEquiv` and
`rootSubgroup_isMulCommutative` give the root-parameter/abelian facts;
`posUnipotent_inf_negUnipotent` and `posUnipotent_isSolvable` give the
positive/negative intersection and solvability facts; and the local torus
conjugation lemmas give the root-parameter weight action. In the `CFSGPort`
carrier, current owner files do not yet establish cross-root commutator
containment in sums of intermediate root groups, uniqueness of ordered
positive/negative root products, rank-one Bruhat decomposition, or the
positive-root normalizer criterion needed by the external structure. More
precisely, external
`TitsSimplicity/Simplicity.lean` first shows each normal subgroup lies in the
Borel or generates the whole group with the Borel, using the CT and Steinberg
root data plus Cartan indecomposability. Bruhat data identifies the Borel
normal core with the center; the other case uses Borel solvability and group
perfectness to force the normal subgroup to be top. The local
`QuasisimpleTransport.isQuasisimple_of_forall` already ports the final
central-or-top-to-quasisimple deduction. The local
`isQuasisimple_adjointGroup_G2_of_normalDichotomy` now composes that lemma with
the G₂ perfectness theorem, and
`isSimpleGroup_of_G2Model_of_normalDichotomy` transports the result to a
modeled group. `g2_family_simple_of_normalDichotomy` now matches the external
family theorem's `Nontrivial G ∧ IsSimpleGroup G` result shape under that same
premise. These adapters are kernel-checked and expose the carrier-compatible
normal-subgroup dichotomy explicitly; proving it from the local root data
remains the main gap for G₂ simplicity.
`CFSGPort/ExceptionalModelSimplicity.lean` adds local adapters from untwisted
adjoint and twisted derived-fixed-subgroup quasisimplicity hypotheses, Ree/Tits
derived-subgroup quasisimplicity hypotheses, and Suzuki operator-group
simplicity hypotheses to simplicity of their corresponding models. The Suzuki
carrier is the image in `LinearMap.GeneralLinearGroup K (Fin 4 → K)` of the
coordinate generator group under `Matrix.GeneralLinearGroup.toLin'`, with
`exists_suzuki_coordinate_equiv` recording an isomorphism to that coordinate
subgroup. `MatrixInverseTranspose.lean` locally ports the external CFSG
inverse-transpose automorphism of `GL` using the pinned Mathlib transpose
equivalence to the opposite ring and group inversion. The checked theorem
`suzukiUpperMatrixGroup_inverseTranspose` proves that this automorphism maps
the external-orientation upper-root generator subgroup onto the local
lower-root operator subgroup. This resolves the carrier-orientation bridge;
it does not port Suzuki simplicity. `CFSGPort/SuzukiOvoid.lean` now defines
the external projective ovoid chart on `ℙ K (Fin 4 → K)` and proves its
finite-point chart injective, the infinity point outside that chart, and
`Nat.card ovoid = |K|² + 1`. It is exposed through `CFSGPort.All`. The
theorems `upperRootOperator_smul_infinity`,
`upperRootOperator_smul_finite`, and `upperRootOperator_maps_ovoid` prove the
projective action of the noncommutative upper-root matrix operators preserves
the ovoid. `upperRootMatrixGroup_smul_mem_ovoid` lifts this action to the
subgroup those actual GL operators generate over a finite field. The new
`suzukiWeylOperator` is the invertible antidiagonal operator; its infinity,
zero, and nonzero-norm finite-chart actions are proved explicitly. Under the
stated Suzuki norm hypotheses, `rootWeylOperatorGroup_smul_mem_ovoid` proves
that the subgroup generated jointly by the root and Weyl operators preserves
the ovoid. `rootWeylOperatorGroup_noncommuting_pair` proves that this subgroup
is itself noncommutative using the `(1,0)` root operator and the antidiagonal
Weyl operator. `upperRootMatrixGroup_noncommuting_pair` also proves a
noncommuting pair within the root subgroup whenever the Tits field
automorphism is nontrivial. `suzukiTorusOperator` is the actual `suzukiD`
linear operator, with kernel-checked membership in both the full Suzuki matrix
group and its endomorphism-operator image. Its chart and ovoid actions are
proved by `suzukiTorusOperator_smul_finite` and
`suzukiTorusOperator_maps_ovoid`. `suzukiUpperMatrixGroup_smul_mem_ovoid`
lifts root, torus, and Weyl generator actions to the existing full
upper-orientation Suzuki operator group, under the stated finite-field and
Suzuki norm hypotheses. `rootWeylOperatorGroup_two_transitive_on_ovoid` proves
two-transitivity of the root/Weyl subgroup under an explicit norm-zero
hypothesis, and `suzukiUpperMatrixGroup_two_transitive_on_ovoid` lifts that
result to the full upper-orientation Suzuki operator group. The same owner
proves solvability of the generated root–torus subgroup, but equality of that
candidate with the full ovoid point stabilizer remains open. The
`rootWeylOperatorGroup_le_suzukiUpperMatrixGroup` inclusion embeds the
noncommuting root/Weyl witness into the full group, and
`suzukiUpperMatrixGroup_noncommuting_pair` proves the full group is itself
noncommutative. The torus remains inside this group, not a separate symmetry
model. Suzuki simplicity remains open. The simplicity adapters still require
family-specific inputs. It also adds
`g2_family_simple_of_adjoint_quasisimple`, shaped after the external
`fam_g2_simplicity` theorem. These adapters are kernel-checked; the
family-specific quasisimplicity theorems remain missing.

The external F₄ and E₈ perfectness proofs additionally use that every simple
root has a simply-laced neighbor. `CFSGPort/ExceptionalCartanHelpers.lean`
ports the finite Cartan checks `exists_symmetric_simple_neighbor_F4` and
`exists_symmetric_simple_neighbor_E8`, matching `neighbour_F4` and
`neighbour_E8` in the external `Steinberg/Adjoint/Presentation.lean`; it now
also checks the same neighbor property for D₄, E₆, and E₇. The file contains
the F₄/E₈ Cartan inverse matrices and identity statements, plus
indecomposability statements. These declarations pass the successful locked
`InfoGeometry.All` build.
The local torus-commutator argument proves simple-root-subgroup containment in
the derived group for D₄, F₄, E₆, E₇, and E₈, extends it to all pinned roots
by Weyl conjugation, then uses `adjointGroup_eq_rootSpan` to source-prove
perfectness of these five adjoint groups over fields of cardinality at least
three. Together with the separately ported G₂ result, all six local
exceptional root tags now have a kernel-checked perfectness result in this
range. These declarations pass the successful InfoGeometry.All build; the D₄/E₆/E₇ results are local
extensions, not claims that their external proofs use this exact path. The
local `RootGroupCommutatorData` interface is now instantiated uniformly for
G₂, F₄, D₄, E₆, E₇, and E₈; reducedness for all six tags is obtained from
their checked finite root certificates.
The normal-subgroup argument needed for quasisimplicity and simplicity still
requires a carrier-compatible Curtis–Tits/Bruhat bridge.

The concrete noncommutative operator subgroup owners are distinct:
`InfoGeometry/Exceptional/CFSGPort/ChevalleyPinned.lean` defines pinned root
subgroups and the positive/negative root-generated subgroups inside
endomorphism units; `InfoGeometry/Exceptional/CFSGPort/CurtisTitsRankOne.lean`
defines the simple-Weyl, rank-one, and simple-root-torus operator subgroups on
the same root module;
`InfoGeometry/Exceptional/CFSGPort/ChevalleyRootTorusSubgroup.lean` defines
the generated root torus; and
`InfoGeometry/Exceptional/CFSGPort/ChevalleyBorelIntersection.lean` defines
their Borel join.
`InfoGeometry/Exceptional/CFSGPort/ChevalleyProductInjectivity.lean` proves
uniqueness/injectivity properties for ordered root products and does not
introduce another group carrier. These owners are imported by the root CFSG
port; matching carrier names do not by themselves provide the missing
external Tits/Bruhat compatibility theorem.

The first concrete family port target is the G₂ quasisimplicity result
`CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card`. The local
port has advanced through the perfectness half: `CommutatorTorus.lean` proves
that every pinned G₂ root subgroup lies in the derived subgroup and proves
`isPerfect_adjointGroup_G2_of_three_le_card`. This matches the external
`isPerfect_g2_of_three_le_card` path. The missing step is the normal-subgroup
argument in `CFSG.LieType.TitsSimplicity.Simplicity.isQuasisimple`: it needs a
bridge from the local Chevalley carrier to the G₂ Curtis--Tits datum, Steinberg
extras, and Bruhat extras used by that criterion. The local `posUnipotent` and
`negUnipotent` groups and their triangularity/nilpotency results are present in
`ChevalleyPinned.lean` and `ChevalleyRootGroupsTriangular.lean`, which now also
derives `posUnipotent_isSolvable` from the nilpotency result; the local
`RootGroupCommutatorData` and the uniform reduced-root instances are present
in `CommutatorTorus.lean`. This supplies corresponding ingredients, but does not
establish compatibility with the external criterion's carriers or its
normal-subgroup conclusion. A separate G₂ root-group development exists under
`InfoGeometry/Algebra/Zorn`, with carrier `SplitOctF2Aut`; its
`G2NativeBruhatRootSubgroupSystem.lean` explicitly leaves product normal forms
and rank-one peeling to a later BN-pair development. These native
characteristic-two automorphism groups are not yet identified with the
finite-field Chevalley adjoint groups in `CFSGPort`, so they do not fill this
bridge.
The external family-specific proof path through
`CFSG.LieType.Steinberg.G2.Perfect` has a source import closure of 194 CFSG
modules. That closure imports 760 `TauCeti`
modules in the external dependency tree. The available TauCeti checkout under
`.lake/packages` is itself pinned to Lean 4.35.0-rc3 / Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24` and has no built `.olean` files;
the root's compiled Mathlib is on the protected 4.34.1 pin. These counts are
source-graph measurements, not a build result. A truthful local proof port must
replace or adapt those dependencies against existing repo-owned carriers and
theorems; the checked quotient-transport helper alone is not the G₂ proof.

| External result | Source-backed status | Root integration |
|---|---|---|
| Exceptional finite Lie-type families are simple under their model hypotheses | `CFSG/LieType/Simplicity/Exceptional.lean` proves G₂, F₄, E₆, E₇, E₈, and ²E₆; `TrialityD4.lean` proves ³D₄; `Suzuki.lean` proves ²B₂; `ReeSmall.lean` and `ReeLargeModel.lean` prove ²G₂ and ²F₄; `TitsModel.lean` contains the Tits and Ree–Tits results | External proof modules remain unimported. Local model predicates and conditional quotient-transport APIs exist; the family-specific quasisimplicity inputs and simplicity proofs are still unported |
| Classical Lie-type families are simple under their hypotheses | `CFSG/LieType/Simplicity/Classical.lean` and `CFSG/ClassicalGroups/{Unitary,Orthogonal,Symplectic}/Simple.lean` | Not imported; source is in the external CFSG development |
| Named sporadic families are simple | `CFSG/Sporadic/` contains named family-simplicity owners; see the exact 32-file scan below | Not imported; model carriers in `CFSGPort/SporadicGroups.lean` have no corresponding root simplicity theorem. The M₁₁ carrier proves finiteness, nontriviality, and seed generation. It also ports the external criterion words, their orders 4 and 11, product order 11, and the first coprimality premise; the derived-pair generation, primitive-action certificate, and stabilizer bound remain open. |
| A₅ is simple | Atlas `GaloisTheory.s5_not_solvable_and_a5_simple` uses Mathlib's `alternatingGroup.isSimpleGroup_five` | The underlying Mathlib theorem is already in the root dependency surface; no duplicate wrapper is added |
| `SU(2) / Z(SU(2))` is simple | Atlas `SimpleGroups.su2_mod_center_isSimple` | Not imported: although this theorem has a tactic proof, it calls `su2_normal_subgroups`, which calls the `sorry`-proved `su2_normal_contains_all_traces`; the file contains four `sorry`s total. The theorem therefore is not a complete kernel proof and cannot be promoted without repairing that dependency |
| Every finite simple group is isomorphic to a CFSG catalog group | `CFSG.classification_finite_simple_groups` in `CFSG/Statement.lean`, with a certified theorem reference in `CFSG/Certified/Classification.lean` | Not root-imported: the external project is pinned to Lean 4.35.0-rc3 and another Mathlib revision; the current port captures model families, not this classification proof |

The exact external scan
`rg -l --no-ignore --glob '*.lean' '^theorem fam_.*simplicity' external_refs/CFSG/CFSG/LieType external_refs/CFSG/CFSG/ClassicalGroups external_refs/CFSG/CFSG/Sporadic`
currently finds 32 owner files. This theorem-name search does not claim to
enumerate every alternative theorem proving simplicity. The owner set is:

The exceptional-family subset maps as follows. `CFSGPort/ExceptionalCatalog.lean`
supplies the local family model, and the final model-to-simple transport is
available conditionally in `CFSGPort/ExceptionalModelSimplicity.lean` for each
carrier shape. In every row, the external family-specific quasisimplicity or
simplicity proof is still missing locally.

| Exceptional family | External theorem owner | Local model constructor | Local conditional transport |
|---|---|---|---|
| G₂ | `Simplicity/Exceptional.lean`: `fam_g2_simplicity` | `ChevalleyExceptionalModel .G2` inside `ExceptionalLieModel .G2` | `g2_family_simple_of_adjoint_quasisimple` |
| F₄ | `Simplicity/Exceptional.lean`: `fam_f4_simplicity` | `ChevalleyExceptionalModel .F4` | `isSimpleGroup_of_untwistedChevalleyModel` |
| E₆ | `Simplicity/Exceptional.lean`: `fam_e6_simplicity` | `ChevalleyExceptionalModel .E6` | `isSimpleGroup_of_untwistedChevalleyModel` |
| E₇ | `Simplicity/Exceptional.lean`: `fam_e7_simplicity` | `ChevalleyExceptionalModel .E7` | `isSimpleGroup_of_untwistedChevalleyModel` |
| E₈ | `Simplicity/Exceptional.lean`: `fam_e8_simplicity` | `ChevalleyExceptionalModel .E8` | `isSimpleGroup_of_untwistedChevalleyModel` |
| ²E₆ | `Simplicity/Exceptional.lean`: `fam_2e6_simplicity` | `TwistedChevalleyModel .E6` | `isSimpleGroup_of_twistedChevalleyModel` |
| ³D₄ | `Simplicity/TrialityD4.lean`: `fam_3d4_simplicity` | `TwistedChevalleyModel .D4` | `isSimpleGroup_of_twistedChevalleyModel` |
| ²B₂ | `Simplicity/Suzuki.lean`: `fam_2b2_simplicity` | `SuzukiExceptionalModel` on the general-linear operator carrier | `isSimpleGroup_of_SuzukiExceptionalModel` |
| ²G₂ | `Simplicity/ReeSmall.lean`: `fam_2g2_simplicity` | `ReeTitsRelationModel` through `ExceptionalLieModel .twistedG2` | `isSimpleGroup_of_ReeTitsRelationModel` |
| ²F₄ | `Simplicity/ReeLargeModel.lean`: `fam_2f4_simplicity` | `ReeTitsRelationModel` through `ExceptionalLieModel .twistedF4` | `isSimpleGroup_of_ReeTitsRelationModel` |
| Tits | `Simplicity/TitsModel.lean`: `fam_tits_simplicity` and `fam_ree_tits_simplicity` | `ReeTitsRelationModel` through `ExceptionalLieModel .tits` | `isSimpleGroup_of_ReeTitsRelationModel` |

This is a coverage crosswalk, not a proof-completion claim. The local
transport theorems take family-specific simple or quasisimple results as
inputs; none of the eleven rows yet has its external family proof ported and
kernel-checked against the root Mathlib pin.

```text
CFSG/ClassicalGroups/Unitary/Simple.lean
CFSG/LieType/Simplicity/Classical.lean
CFSG/LieType/Simplicity/Exceptional.lean
CFSG/LieType/Simplicity/ExceptionalConverse.lean
CFSG/LieType/Simplicity/ReeLargeModel.lean
CFSG/LieType/Simplicity/ReeSmall.lean
CFSG/LieType/Simplicity/Suzuki.lean
CFSG/LieType/Simplicity/TitsModel.lean
CFSG/LieType/Simplicity/TrialityD4.lean
CFSG/Sporadic/B.lean
CFSG/Sporadic/Co1.lean
CFSG/Sporadic/Co2.lean
CFSG/Sporadic/Co3.lean
CFSG/Sporadic/HN.lean
CFSG/Sporadic/HNSchreier/Simple.lean
CFSG/Sporadic/HS.lean
CFSG/Sporadic/He.lean
CFSG/Sporadic/J1.lean
CFSG/Sporadic/J2.lean
CFSG/Sporadic/J3.lean
CFSG/Sporadic/J4.lean
CFSG/Sporadic/Ly.lean
CFSG/Sporadic/Mathieu/M11.lean
CFSG/Sporadic/Mathieu/M12.lean
CFSG/Sporadic/Mathieu/M22.lean
CFSG/Sporadic/Mathieu/M23.lean
CFSG/Sporadic/Mathieu/M24.lean
CFSG/Sporadic/McL/Simple.lean
CFSG/Sporadic/ON.lean
CFSG/Sporadic/ONOddCore/CertifiedSimple.lean
CFSG/Sporadic/Ru.lean
CFSG/Sporadic/Suz/Simple.lean
```

Thus “all external simple-group material” is not yet integrated. This pass
establishes that the root port currently imports models/carriers, while the
external simple-family proofs and classification theorem remain outstanding.
The exact theorem inventory still needs to distinguish proved family results
from statements and conditional interfaces throughout the large CFSG tree.

The CFSG external project is pinned to Lean 4.35.0-rc3 and Mathlib revision
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`. This repository is pinned to Lean
4.34.1 and Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The root Lake manifest does not declare CFSG. The external CFSG Lake project
also declares TauCeti and has a very large default target set, so importing its
full proof development would require an explicit dependency/toolchain decision
and a narrowed, build-verified dependency closure.

A source-level recursive import walk starting from the six exceptional
simplicity owners (`Exceptional`, `TrialityD4`, `Suzuki`, `ReeSmall`,
`ReeLargeModel`, and `TitsModel`) reaches 1,002 local CFSG modules and 10
unresolved `TauCeti.*` modules, excluding Lean's built-in `Init` and Mathlib
imports from the unresolved count. This is an import-graph estimate, not a
successful build of those owners under the root pins. It shows why adding six
`import` lines alone would not integrate the external simplicity proofs.

## Current root import surface

`InfoGeometry.Exceptional.CFSGPort.All` is imported by both `InfoGeometry.lean`
and `InfoGeometry.All`. It is the umbrella for the adapted Chevalley root-group,
exceptional-family, classical-model, combined-catalog, and sporadic-carrier
modules. It exposes root
data and group models for G₂, F₄, D₄, E₆, E₇, E₈, ²E₆, ³D₄, ²B₂, ²G₂,
²F₄, and the Tits group, alongside PSL/PSU/PSp/PΩ models and all 26 sporadic
carriers. The `FiniteGroupModelCatalog` predicate combines the cyclic,
alternating, classical, exceptional, and sporadic model families. These are
models and carriers, not proofs that each is simple or a proof of CFSG. The
imported simple-family modules prove that the cyclic-prime and alternating
degree-at-least-five branches are simple, transporting Mathlib's results
across the catalog's `MulEquiv` model witnesses. The classical PSL branch is
also proved in dimension two when the field has at least four elements, using
Mathlib's `PSL₂(F)` simplicity theorem and the local matrix-group quotient
equivalence. Other classical branches and exceptional and sporadic root
branches still lack corresponding root simplicity theorems.

The external classification theorem remains unimported because CFSG uses
Lean 4.35.0-rc3 and a different Mathlib revision from the root pins.
`InfoGeometry.Exceptional.CFSGPort.All`, including the PSL₂ model result and
the generic torus commutator module, built successfully with the locked Lake
wrapper. The root top-level
import was checked with
`python3 tools/infra/run_locked_lean.py --wait-for-build-lock lean/InfoGeometry.lean`
and elaborated successfully (exit code 0).

No conclusion here asserts that every group-like name in the repository is a
symmetry group. For a declaration-level audit, follow each owner module's
carriers, operations, exact action/group laws, imports, and consumers.

## Supplement: explicit group instances found by owner-source scan

A second source scan searched repo-owned Lean files for declarations whose
instance target is explicitly `Group` or `CommGroup`. It excluded nested
`.kilo` scratch worktrees and compared owner paths and basenames against the
inventory above. The following 22 owner files were not cited there. This is a
coverage supplement: an algebraic group instance proves the group laws for
that carrier, but does not by itself prove the carrier is a symmetry group or
has a nontrivial action. `MulAction` instances are outside this table and are
tracked in the action sections above.

| Owner | Carrier declared with group laws | Inventory classification |
|---|---|---|
| `Algebra/Zorn/G2TwoPCGroup.lean` | `PCExponent` | Coordinate/collector group for the finite G₂ model; auxiliary algebraic carrier, not a symmetry operator group. |
| `Arithmetic/ProfiniteCyclotomicUnitLimit.lean` | `Carrier` | Cyclotomic unit-limit group; inspect its unit/action maps before counting it as a symmetry. |
| `Canonical/BrillouinWallpaperD8GroupBridge.lean` | `D8PointGroup` | Finite point-group carrier for the wallpaper action; a genuine geometric symmetry candidate. |
| `Canonical/FiniteHeisenbergGroup.lean` | `FiniteHeisenberg n` | Heisenberg group carrier; group structure alone does not establish a symmetry representation. |
| `Canonical/H3ZornS3JordanMonoid.lean` | `ContinuousJordanAutomorphism` | Automorphisms of the Jordan carrier; symmetry group by its action on that carrier. |
| `Canonical/RestrictedSheetContinuous.lean` | `RestrictedSheetContinuousEquiv E`, `ShaleStinespringEquiv E` | Equivalence/operator symmetry carriers; retain the owner-specific continuity and implementability conditions. |
| `Canonical/RestrictedVolumeCharacter.lean` | `RestrictedSheetEquiv E` | Restricted equivalence group; symmetry carrier, with its exact action determined by the owner. |
| `Canonical/SE2SouriauCocycle.lean` | `SE2RotationCarrier` | Rotation subgroup/carrier acting in the Souriau SE(2) construction. |
| `Canonical/SE2SouriauCompactOrbit.lean` | `RotationCarrier` | Rotation symmetry group acting on the compact orbit and related carriers. |
| `Canonical/V4Q8ProjectiveBridge.lean` | `Q8Elt` | Quaternion group model used in the projective bridge; inspect its represented action before treating it as an independent symmetry realization. |
| `Clifford/Cl55WittOrthogonalNative.lean` | `Q55.IsometryEquiv Q55` | Isometry group of the noncommutative Clifford/Witt carrier; direct operator-relevant symmetry group. |
| `Clifford/SplitBiquaternion.lean` | `NormOneSplitBiquaternion` | Norm-one units of the split-biquaternion algebra; noncommutative algebraic group carrier. |
| `Clifford/SplitQuaternion.lean` | `NormOneCoq` | Norm-one coquaternion carrier; noncommutative algebraic group. |
| `Lie/G2SplitChevalley.lean` | `FiniteChevalleyG2` | Finite Chevalley group, supplied from its existing group structure. |
| `Lie/G2TwoRealSplitClassification.lean` | `G2Two` | Group structure inherited from the split-octonion automorphism carrier; a finite exceptional symmetry group. |
| `Modular/PSL2Z.lean` | `Carrier` | PSL₂(ℤ) carrier; group structure is not by itself an action theorem. |
| `Modular/SemidirectAutomorphismGroup.lean` | `SemidirectGroup A` | Semidirect product of automorphisms with units; genuine automorphism-group construction. |
| `Stratum/Gauge.lean` | `PosGauge` | Positive gauge group; classify its action from the gauge owner, not from commutativity or scalar notation alone. |
| `Topology/BraidGroupPresentation.lean` | `braid_group n`, `braid_group_inf` | Artin braid groups; algebraic symmetry groups with representations inventoried separately. |
| `Topology/MobiusGeometry.lean` | `PGL2C` | Projective linear/Möbius transformation group; acts on the projective line. |
| `Topology/ProjectiveBoundarySL2Flow.lean` | `SL2BoundaryMatrix R` | Boundary matrix group; its boundary-flow action is described in the owner. |
| `Topology/V4RootSystem.lean` | `V4Group` | Klein four group attached to the root-system construction; retain its specific action/model distinction. |

The scan also found two duplicate `CommGroup` instances in
`lean/sandbox/TrifactorHomomorphism.lean` and
`lean/sandbox/TrifactorHomomorphismComplex.lean` (for `ScaleGroup` and
`ParityGroup`). They are sandbox constructions and are recorded as such, not
counted as independent noncommutative operator symmetry groups. The generated
candidate index remains broader than this owner scan; these supplemental rows
close only the explicit `Group`-instance citation gap found by this query.

## Additional external simple-group source audit

The root-pinned external-source review also checked the non-CFSG paths that
contain the literal `IsSimpleGroup` / `isSimpleGroup` identifiers. In
`external_refs/atlas-lean/Atlas/AlgebraNotes/code/SimpleGroups.lean`, the
statement `SimpleGroups.su2_mod_center_isSimple` concerns the noncommutative
quotient of the matrix Lie group `SU(2)` by its center. Its proof calls
`su2_normal_subgroups`, whose noncentral case uses
`su2_normal_contains_all_traces`; that lemma is proved with `by sorry` in the
same file. This is therefore a source candidate, not an accepted
kernel-checked simplicity result. The root declares Atlas as a Lake dependency,
but the Lean entrypoints do not import this `SimpleGroups` owner. No Atlas
submodule files were changed.

The remaining literal matches in the extra source paths do not add a proved
simple-group family: `LeanCamCombi/GrowthInGroups/Lecture1.lean` assumes
`[IsSimpleGroup G]` while stating Babai's conjecture; `LeanAide`'s
`SimilaritySearch/RunTests/TestResults/false-*` files contain counterexample
challenge outputs with false simplicity claims discharged by `sorry`; and
`AbstractSimplicialComplex/lake-packages/mathlib` is a vendored Mathlib copy
containing the prime-cyclic and alternating simplicity theorems already
available from the root-pinned Mathlib dependency. These are not additional
external family proofs to import. This audit supplements, but does not replace,
the CFSG owner-by-owner port map above.

For the OAI source library, an exact module-name comparison found 21 files
under `external_refs/openai-math/lean/OAI` containing the literal simplicity
identifiers, and all 21 are imported by the two root entrypoints. A broader
search also finds three `ComparatorChallenges` files in that external tree;
their advertised simple-group results are `sorry` challenge statements and
those modules are not imported. They are not counted as additional OAI proof
owners. This distinguishes the imported owner modules from all literal matches
in the surrounding checkout.

## G₂ native-action and root-subgroup owner review

The following declarations were checked in their Lean owners. They refine the
candidate index and distinguish subgroups from actions transported to finite
coordinates.

| Owner declaration | Source-grounded classification |
|---|---|
| `G2NativeFullFlagAction.nativeFlagPerm` | For `SplitOctF2Aut`, an `Equiv.Perm NativeFlag` representation. The owner proves bijectivity of the induced flag map and the multiplicative law `nativeFlagPerm (g * h) = nativeFlagPerm g * nativeFlagPerm h`; this is an action representation, not a newly defined group. |
| `G2NativeOnePointStabilizer.nativePointStabilizer` | The `MulAction.stabilizer` subgroup of `SplitOctF2Aut` at `nativeBasePointData`. The owner proves the PC subgroup lies inside it and identifies that PC subgroup with the separately named Sylow-2 subgroup. No equality of the point stabilizer with either subgroup is asserted there. |
| `G2NativeFlagStabilizerTransport.nativeFlagStabilizer` | The `MulAction.stabilizer` of `baseIntrinsicFlag` in `SplitOctF2Aut`; the owner proves PC-word membership. It is a flag stabilizer, distinct in definition from the point stabilizer; the cited owner does not prove the two stabilizers equal. |
| `G2RootSubgroup.rootSubgroup` | A subgroup of `SplitOctF2Aut` with carrier exactly `{1, rootAut α}`. Its closure proof uses the involution law `rootAut_sq α`; conjugation equivalences are supplied under the stated conjugation hypotheses. This is a rank-one order-at-most-two root automorphism subgroup, not a full root group claim. |
| `G2NativeRootProductImage.rootProductSubgroup` | The subgroup generated by the union of two root subgroups. The owner proves each input subgroup embeds in this generated subgroup and proves a selected short-root subgroup inclusion. It does not identify the generated subgroup with the ambient automorphism group or a residual subgroup. |
| `G2SteinbergPositiveRoots.positiveRootSubgroup` | The subgroup generated by the range of `positiveRootPacket`; packet membership and subgroup closure are proved. The declaration alone does not establish it is the full unipotent/radical subgroup. |
| `G2ImaginaryPointPermutation.pointPerm` | The 63-point action of `SplitOctF2Aut` conjugated through `pointEnum : Fin 63 ≃ Point`; the owner proves the representation multiplication law. This is a coordinate transport of the native action. |
| `G2ImaginaryOctImBridge.octImPointPerm` | The same native point action transported through `pointOctImEquiv`; the owner proves identity, application, and multiplicativity. It is a second carrier realization of the action, not an independent symmetry group. |
| `G2PointEnumRelabeling.casToNative` | A permutation relabeling between enumerations. It is a carrier equivalence, not a subgroup or independent action. |
| `InfoGeometry.OperatorAlgebra.G2TwoOperatorRepresentation.g2TwoOperatorGroup` | The faithful image of the finite split-octonion automorphism group in units of endomorphisms on real-valued functions over the octonion carrier; `g2TwoOperatorGroup_has_noncommuting_pair` exhibits noncommuting simple-root operators in this noncommutative carrier. |

These owners provide genuine noncommutative ambient symmetry data because their
acting group is the automorphism group of the split-octonion algebra. The
finite point/flag permutations are faithful only if a separate kernel or
faithfulness theorem establishes that property; the representation laws cited
above do not by themselves prove faithfulness.

## Further G₂ parabolic and incidence-owner review

| Owner declaration | Source-grounded classification |
|---|---|
| `G2PeirceParabolicStabilizer.peirceStabilizer` | Generic stabilizer subgroup for an arbitrary group action on a `PeirceFrame A`; membership is definitionally equivalent to fixing the frame. It is a reusable construction, not itself a concrete G₂ subgroup until instantiated with a specified action and frame. |
| `G2PeirceParabolicStabilizer.parabolicSubgroup` | Generic subgroup closure of an input subgroup `B₀` together with one element `s₂`. Its containment in the Peirce stabilizer is conditional on both generators fixing the frame. This declaration does not independently establish maximality or the concrete order of a parabolic. |
| `G2TwoBruhatClassification.standardParabolicP1Subgroup` | Concrete subgroup of `SplitOctF2Aut` generated by the Sylow-2 subgroup and `s`; the owner proves it lies in `nativePointStabilizer`. |
| `G2TwoBruhatClassification.standardParabolicP2Subgroup` | Concrete subgroup generated by the Sylow-2 subgroup and `t`; the owner proves generator membership and Sylow containment. The inspected declarations do not establish its equality with a separately defined Peirce stabilizer. |
| `G2TwoConcreteWeylGroup.concreteWeylSubgroup` | Subgroup of `SplitOctF2Aut` generated by `swap01Aut`, `cycle012Aut`, and `swapCartanAut`. The owner proves `Fintype.card concreteWeylSubgroup = 12` and identifies it with the subgroup generated by the range of its twelve explicitly enumerated automorphisms. |
| `G2FlagIncidenceAction.PreservesIncidence` / `flagPerm` | A predicate on permutations of the finite incidence points, followed by a flag permutation when the predicate is supplied. The owner proves the flag-map inverse and composition laws. These are incidence transport operations; this file does not identify all incidence-preserving permutations as an automorphism group or prove the split-octonion action preserves the certificate. |

This pass adds concrete parabolic subgroup candidates and generic conditional
stabilizer machinery while keeping incidence-preserving permutations separate
from the established `SplitOctF2Aut` action. In particular, an action on the
same finite set is not evidence that two acting groups coincide.

## Root-system and Weyl-group owner review

This pass follows the repository's root-lattice direction explicitly. It
records the root carrier acted on, and whether the Weyl action is realized on
root permutations, Cartan linear equivalences, or a canonical root-pairing
Weyl group.

| Owner declaration | Source-grounded classification |
|---|---|
| `Canonical.E8RootDecomposition.e8WeylGroup` | Subgroup of `Equiv.Perm E8Root`, generated by reflections in the explicitly enumerated 240-element E₈ root subtype. Root closure under each reflection and the involution law are proved. This is a genuine concrete Weyl permutation group on the root set; this definition does not identify it with a Clifford-algebra automorphism group. |
| `Canonical.A2InsideD5RootSubsystem.weylRepresentation` | Monoid hom from `Equiv.Perm (Fin 3)` to permutations of the six oriented A₂ roots embedded in the D₅ lattice. The owner proves injectivity and preservation of the root dot product, so it realizes a faithful S₃ Weyl action on that root subsystem. |
| `Lie.CanonicalZornG2WeylGroupAction.WeylGroup` | Subgroup of paired linear equivalences on the G₂ Cartan and its parameter carrier, generated by the short and long reflections. The owner proves the Cartan action injective and gives multiplicative equivalences to its Cartan-action range and the separately owned canonical Cartan Weyl subgroup. It is an actual operator-level linear symmetry group; it is not merely a six-root coordinate permutation. |
| `Lie.CanonicalZornG2WeylGroupAction.canonicalCartanActionMulEquiv` | Proved group equivalence from the paired-generator Weyl group to `CanonicalZornG2CoxeterRelations.cartanWeylSubgroup`. This establishes these two G₂ constructions as the same group up to the stated carrier equivalence, rather than counting duplicate groups. |
| `Lie.CanonicalZornRootSystemComparison.P.weylGroup` | Here `P` abbreviates the existing `canonicalZornRootSystem`; the owner proves that its Mathlib `RootPairing.weylGroupToPerm` acts on the native indexed roots compatibly with the root action. The owner establishes a root-index equivalence with Mathlib's native root subtype. This is the canonical root-pairing Weyl construction and is distinct in interface from the paired Cartan/parameter subgroup above; no equivalence between those carriers is asserted by the inspected theorem. |
| `RootSystem.ExceptionalRootCoxeterBridge.exceptionalTypeE_CoxeterToWeyl_surjective` | For E₆, E₇, or E₈, the abstract simply-laced Coxeter group maps surjectively onto the subgroup generated by the concrete simple reflections of the local integral root-coordinate lattice. The proof derives symmetry and off-diagonal Cartan entries from the shared `Tag.cartanE` formula. Surjectivity is proved; injectivity and a Coxeter presentation isomorphism are not claimed. The owner builds under the root-pinned toolchain. |
| `RootSystem.ExceptionalRootCoxeterBridge.exceptionalTypeE_CoxeterToOperatorWeyl_surjective` | The same E₆/E₇/E₈ Coxeter group maps surjectively onto `rootOperatorWeylGroup`, a subgroup of units in `Module.End ℝ (RootLattice τ → ℝ)`. This composes the root-lattice Weyl map with the already-proved faithful inverse-reindexing operator representation; `simplyLacedCoxeterToOperatorWeyl_simple` identifies each simple Coxeter generator with its concrete reflection operator. The target is genuinely noncommutative; these theorems concern this operator image and assert no new simplicity theorem for finite Chevalley groups. |

The E₈ and A₂ owners substantiate root-system symmetry groups and their
representations, but those finite permutation carriers are not substitutes
for the noncommutative operator automorphism groups elsewhere in the codebase.
Conversely, the G₂ Cartan action is already on linear-operator carriers and
has an explicit equivalence to its Coxeter-relation owner. The remaining root
families in the declaration index still require owner-by-owner review before
the inventory can claim comprehensive root-system coverage.

The E₆/E₇/E₈ Coxeter-to-Weyl and Coxeter-to-operator-Weyl surjections are imported by
`InfoGeometry.RootSystem.All`. They strengthen the root-system symmetry map
for the three simply-laced exceptional families; they do not import or prove
the external CFSG simplicity theorems for the corresponding finite Chevalley
groups, which use different carriers and remain tracked separately in
`CFSG_EXCEPTIONAL_PORT_STATUS.md`.

## Additional high-recall owner review

A path comparison found 31 candidate-index owner files not cited by full path
in the inventory. This batch checks a representative set of those owners and
classifies algebraic Lie subalgebras separately from actual groups and group
actions.

| Owner declaration | Source-grounded classification |
|---|---|
| `Canonical.NonAbelianDihedralSymmetry12.dihedralAction` | A hom from `DihedralGroup 3` to automorphisms of the chiral Zorn matrix algebra. Its range is proved equal to the subgroup generated by the rotation `R` and reflection `M`, and that subgroup is noncommutative when the coefficient algebra is nontrivial. The file separately defines `Order12DihedralModel := DihedralGroup 6` and proves its cardinality is 12; do not conflate that type with the action's `DihedralGroup 3` carrier. |
| `Clifford.Clifford55.nativeQuadraticReflectionSubgroup` | The subgroup generated by all nonisotropic quadratic reflections in the native `Q55.IsometryEquiv Q55` carrier. The owner proves it equals the full isometry group, so reflection generation is established on the actual quadratic space. |
| `Categorical.LogJordanBraidGroupInfRepresentation.hadjiivanovBraidGroupInfHom` | A representation of the presented infinite braid group in automorphisms of `StandardTensorPowerColimit`; the owner proves generator readback and finite-stage compatibility. `finiteStageReadbackSubgroup` is a subgroup of a finite braid group defined by equality of its colimit and finite-stage actions. |
| `Categorical.SylvesterBraidRepresentation.sylvesterBraidHom` | A representation of a finite braid group in permutations of a `PhasedState` carrier. This is an action hom, not a new group; faithfulness is not implied by the displayed definition. |
| `Algebra.TrilinearStabilizer.trilinearStabilizer` | The infinitesimal stabilizer of a trilinear form as a Lie subalgebra of `Module.End R V` under the commutator bracket. It is a Lie algebra of operators, not a group of global symmetries. |
| `Canonical.SplitOctonionSymplecticLieAlgebra.omegaSymplecticLieSubalgebra` | A Lie subalgebra of endomorphisms preserving the native phase-space bilinear form infinitesimally. The nearby `PolarizedAction` is data with a pairing identity; it is not declared as a group or representation in this owner. |
| `Canonical.CanonicalZornPhaseBridge.phasePreservingDerivations` | A Lie subalgebra of derivations satisfying `PreservesPhase`, with closure under zero, addition, scalar multiplication, and Lie bracket. It is infinitesimal symmetry data, not a multiplicative symmetry group. |
| `Canonical.SplitOctonionTKK55.hyperbolicSkewLieSubalgebra` | A Lie subalgebra of endomorphisms of the TKK carrier, identified through a linear equivalence with the underlying hyperbolic-skew submodule. The owner does not assert an integrated group equivalence here. |
| `Canonical.SuperUnified.StructureGroupLieAlgebra` | The even endomorphisms commuting with a specified complex structure, packaged as a Lie subalgebra. The word “Group” in the declaration name does not make this carrier a group. |

The index-to-inventory comparison is only a path-coverage aid: these 31 files
can contain multiple candidates each, and the crosswalk classifies indexed
declarations without establishing that every symmetry-like declaration in
each file has been semantically adjudicated.

## Broader carrier-scan boundary and false-positive review

A broader carrier-token scan (`Group`, `Subgroup`, `MulAction`, `Equiv.Perm`,
`LieSubalgebra`, and related forms) currently finds 1,364 Lean files. Only 372
of those paths occur in the inventory, because the broad scan also catches
generic hypotheses, group-valued parameters, group operations used in unrelated
algebra, and prose. This is a separate navigation set from the 562-declaration
focused index above; neither count is a semantic census of symmetry groups.

The following high-signal omitted owners were checked at source level to avoid
promoting names or exposition to group declarations:

| Owner file | Source-grounded classification |
|---|---|
| `InfoGeometry/Algebra/SplitE88Group.lean` | The inspected declarations give E₈/D₈ dimension and branching arithmetic; this owner does not define an E₈ group carrier, subgroup, or group action. |
| `InfoGeometry/Algebra/DihedralArtinI2SixSpinLift.lean` | The inspected source proves matrix-generator and braid/Coxeter identities. It does not package the matrices into a generated subgroup or a Weyl-group equivalence in this owner. |
| `InfoGeometry/Algebra/SplitMetricOperatorRepresentation.lean` | `SplitMetricOperatorRepresentation` is representation data with a group parameter and a metric-preservation field; it does not define the parameter group's carrier. |
| `InfoGeometry/Algebra/IwasawaParabolicDiracDecomposition.lean` | `ParabolicElement` is a record of a sign and two real coordinates, with selected matrices and a Klein holonomy relation. The owner does not define a multiplication or group instance on that record. |
| `InfoGeometry/Algebra/CayleyPeirceKANUnipotentBridge.lean` | The owner proves nilpotent and Cayley-transform identities in an associative ring. These elements are not packaged here as a unipotent subgroup. |
| `InfoGeometry/Algebra/Grothendieck.lean` | `Grothendieck M` is the additive-group completion of an additive commutative monoid, with its universal map. It is a genuine abelian group construction, but this owner does not identify it as a symmetry group. |

This false-positive review is intentionally narrow. The remaining broad-scan
files require owner-by-owner semantic inspection before the inventory can be
called a full-codebase census.

## Further candidate-owner review: gauge, sign, and finite-state actions

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.Folding.BinFoldGaugeSign.binFoldGaugeFiberSign` | The sign homomorphism from each fiber permutation group `Equiv.Perm (Fin d)` to the units of integers. It is a character/quotient map, not the gauge group itself. The original `BinFoldGauge` in `BinFoldGaugeDecomposition` is only a subtype, with no group instance in that owner; `BinFoldGaugeOperator.binFoldGaugeSubgroup` declares the matching permutation subgroup and a faithful endomorphism-unit representation. It also includes a window-6 noncommuting pair built from three points in the explicit fiber over `cBinFold 6 37`. The new owner and its import from the existing sign module are awaiting kernel verification. |
| `Omega.Folding.binFoldGaugeSignAbelianizationSizeSix` / `paper_fold_bin_gauge_sign` | A verified count of 21 sign bits from fiber sizes 2, 3, and 4 at window 6. The theorem proves a cardinality expression for the product of sign quotients; this is not by itself a proof that the entire gauge group's abelianization is exactly that product. |
| `Omega.POM.pom_s3_orbit_decomposition_act` | The coordinate action of `Equiv.Perm (Fin 3)` on Boolean triples, with proved Hamming-weight invariance and explicit orbit representatives. The owner does not package the map as a `MulAction` instance or prove its kernel trivial, so classify it as an action formula, not a separately defined group or a faithful representation. |
| `Omega.EA.chiRigidBlockPermutations` | The subgroup of `Equiv.Perm (Fin m)` in the kernel of the sign homomorphism, with subgroup closure proved. It is the alternating subgroup (including the small-degree cases as defined by the sign kernel). |
| `Omega.EA.foldGroupoidAutChiClassified` / `FoldGroupoidAutChiSemidirectProduct` | The owner proves an equivalence of underlying types between restricted automorphism data and `chiRigidBlockPermutations m × Bool`. The Boolean tag is only a type factor here; no group operation or semidirect-product group structure is defined on that product in this file. |
| `Omega.POM.pom_s3_orbit_decomposition_state` | `Bool^3` is the state carrier for the preceding action, not a symmetry group. Its eight explicit states are partitioned by Hamming weight in the orbit calculation. |

These distinctions matter for repository-wide counts: sign characters,
underlying-type equivalences, and state-space actions are evidence about
symmetry but are not additional groups unless the owner supplies the relevant
group structure.

## Remaining indexed owner paths: declaration-level crosswalk

The following paths were absent from the earlier exact-path comparison. The
classifications below were checked against the named declarations in their
owner files. This closes path citation for the indexed candidates; it does not
claim that every symmetry-like declaration in every source file has been
exhaustively enumerated.

| Owner file | Source-grounded classification |
|---|---|
| `InfoGeometry/Algebra/SplitAlbertInnerTraceSpan.lean` | `h3ZornTraceZeroLieSubalgebra` is a Lie subalgebra of endomorphisms with trace-zero outputs; it is infinitesimal structure, not a group. |
| `InfoGeometry/Algebra/TrilinearStabilizer.lean` | `trilinearStabilizer` is the Lie subalgebra of endomorphisms infinitesimally preserving the trilinear form. |
| `InfoGeometry/Algebra/Zorn/G2ImaginaryOctImBridge.lean` | `octImPointPerm` is the multiplicative permutation action of `SplitOctF2Aut` on isotropic imaginary-octonion points, transported through the point equivalence. It is an action representation, not another group. |
| `InfoGeometry/Algebra/Zorn/G2NativeFullFlagAction.lean` | `nativeFlagPerm` is the permutation representation of `SplitOctF2Aut` on native flags. The declaration is an action, not a separately defined group. |
| `InfoGeometry/Canonical/CanonicalZornPhaseBridge.lean` | `phasePreservingDerivations` and its `polarizedPhaseDerivations` subalgebra are closed under Lie operations and encode infinitesimal phase constraints, not global multiplicative symmetries. |
| `InfoGeometry/Canonical/NonAbelianDihedralSymmetry12.lean` | `sheetColorSubgroup` is the actual subgroup of chiral Zorn algebra automorphisms generated by `R` and `M`; the owner proves its noncommutativity under the stated coefficient-algebra condition. |
| `InfoGeometry/Canonical/SplitOctonionJordanStructure.lean` | `structureActionLieSubalgebra` is the Lie-algebra range of the structure action on the Jordan carrier; no global group identification follows from this declaration. |
| `InfoGeometry/Canonical/SplitOctonionSymplecticLieAlgebra.lean` | `omegaSymplecticLieSubalgebra` is the infinitesimal stabilizer Lie subalgebra for the phase-space form. |
| `InfoGeometry/Canonical/SplitOctonionTKK55.lean` | `hyperbolicSkewLieSubalgebra` is a Lie subalgebra of endomorphisms preserving the hyperbolic-skew condition infinitesimally. |
| `InfoGeometry/Canonical/SuperUnified.lean` | `StructureGroupLieAlgebra` is the even endomorphism Lie subalgebra commuting with the specified complex structure; its name does not define a group. |
| `InfoGeometry/Categorical/LogJordanBraidGroupInfRepresentation.lean` | `finiteStageReadbackSubgroup` is the subgroup of a finite braid group whose finite-stage and colimit actions agree. The infinite braid group representation is recorded separately in the inventory. |
| `InfoGeometry/Categorical/SylvesterBraidRepresentation.lean` | `sylvesterBraidEquiv` and `sylvesterStandardGen` are permutations of the phased-state carrier used in a finite braid representation; they are not extra symmetry groups. |
| `InfoGeometry/Clifford/Cl55WittNativeCartanDieudonne.lean` | `nativeQuadraticReflectionSubgroup` is generated by the native nonisotropic quadratic reflections; the owner proves it equals the full native isometry group. |
| `InfoGeometry/EmergentVacuum/KreinMetricStabilizer.lean` | `metricStabilizer` and `specialMetricStabilizer` are genuine subgroups of the complex general-linear group preserving the metric, with the latter also imposing determinant one. |
| `InfoGeometry/Exceptional/CFSGPort/J1GeneratorOrders.lean` | The two private `j1SeedA`/`j1SeedB` closures are matrix subgroups generated by the displayed J₁ seed units. They are local generator-order witnesses, not by themselves a full J₁ presentation or simplicity proof. |
| `InfoGeometry/Exceptional/CFSGPort/MatrixInverseTranspose.lean` | `inverseTranspose` is a multiplicative equivalence of the full general-linear group, an automorphism of the matrix operator group rather than an exceptional-family result. |
| `InfoGeometry/Exceptional/CFSGPort/SuzukiOvoid.lean` | `upperRootMatrixGroup` and `rootWeylOperatorGroup` are actual subgroups of `GL (Fin 4) K` generated by the stated Suzuki root and Weyl operators. Their ovoid action results do not identify them with the full Suzuki group or prove simplicity. |
| `InfoGeometry/Exceptional/FreudenthalChargeLinear.lean` | `symplecticOperatorLieSubalgebra` is the Lie subalgebra of endomorphisms satisfying the Freudenthal symplectic infinitesimal condition. |
| `InfoGeometry/Exceptional/G2ArtinKleinBridge.lean` | `throatConjugation` is an automorphism of the root-label permutation group given by conjugation with the specified Klein-label permutation. |
| `InfoGeometry/Exceptional/G2CyclotomicCoordinateActionBridge.lean` | `transportRootPermHom` transports the root permutation group action to the coordinate-root carrier; it is a representation hom, not an additional group. |
| `InfoGeometry/Exceptional/TrialityContactCantor.lean` | `fixedLieSubalgebra` is the fixed-point Lie subalgebra of the supplied triality rotation. |
| `InfoGeometry/Krein/DoubledSpace.lean` | `information_lie_algebra` is a Lie subalgebra of continuous endomorphisms satisfying the Krein-skew-adjoint condition. |
| `InfoGeometry/Krein/Metric.lean` | `neutralLieSubalgebra` is the infinitesimal isometry Lie subalgebra for the neutral-space metric. |
| `InfoGeometry/Lie/CanonicalZornG2RootStarAction.lean` | `rootActionOnFiniteRoot` is the Weyl-group action on the finite root index set transported through an equivalence; it is not a new group. |
| `InfoGeometry/Lie/GenericSplitOrthogonalBlocks.lean` | `splitOrthogonalLieSubalgebra` is the Lie algebra of endomorphisms skew-adjoint for the split form. |
| `InfoGeometry/Lie/SplitOctonionAxialCartanErlangen.lean` | `axialCartanLieSubalgebra` is the linear range of the axial-Cartan derivation map, with Lie closure; it is infinitesimal symmetry data. |
| `InfoGeometry/Lie/SplitOctonionDerivationWittBlockRealization.lean` | `transportedDerivationLieSubalgebra` is the range of the transported derivation Lie hom on the Witt-block carrier. |
| `InfoGeometry/Lie/SplitOctonionWittSkewEndomorphismSubalgebra.lean` | `neutralWittSkewLieSubalgebra` is the endomorphism Lie subalgebra satisfying the neutral-Witt skew condition. |
| `InfoGeometry/ProjectiveFoundation/RealProjectiveDescent.lean` | `centerQuotientMulAction` is an action of the center quotient on the projective carrier, induced by its permutation representation; it is not a new group carrier. |
| `InfoGeometry/Topology/KleinBottleCliffordGlide.lean` | `glideCliffordTotalPerm` and `transverseCliffordTotalPerm` are permutations of the product of the Klein cover and Clifford algebra carrier. These are individual transformations; this file's declarations do not package their generated closure as a group. |
| `InfoGeometry/Twistor/Cl55CelestialDeckPhaseMonodromy.lean` | `deckSignLinearRepresentation` is the permutation-sign character followed by scalar-unit operators on the module; it records a representation, not a new group. |

## Exceptional operator-carrier and presentation-owner review

| Owner declaration | Source-grounded classification |
|---|---|
| `Exceptional.CFSGPort.MatrixInverseTranspose.inverseTranspose` | A multiplicative equivalence of the full general linear group `GL n K`, built from transpose and inversion. This is an automorphism of a noncommutative operator group when the dimension and field make that group noncommutative; it is a generic symmetry construction, not an exceptional-family simplicity result. |
| `Exceptional.CFSGPort.Suzuki.upperRootMatrixGroup` | The subgroup of `GL (Fin 4) K` generated by the locally defined Suzuki upper-root operators. The owner proves its generators act on the stated projective ovoid and act transitively on its finite chart. |
| `Exceptional.CFSGPort.Suzuki.rootWeylOperatorGroup` | The subgroup of `GL (Fin 4) K` generated by those upper-root operators together with the antidiagonal Weyl operator. The owner proves ovoid preservation and transitivity on the ovoid, under explicit field-characteristic and twisting-map hypotheses. The inspected file does not identify this subgroup with the full Suzuki group or prove simplicity. |
| `Exceptional.CFSGPort.Suzuki.suzukiTorusOperator` | An actual invertible linear operator, with a theorem placing it in `Chevalley.suzukiMatrixGroup`; its projective action rescales the finite ovoid chart under the stated Suzuki endomorphism identities. This generator's membership in the Chevalley matrix group does not imply that the separately defined root-plus-Weyl subgroup contains it. |
| `Experimental.Sandbox.Topology.KleinBieberbachWeyl.KleinGroup` | The quotient of a free group by the normal closure of the Klein relator, with the Bieberbach conjugation relation proved. The owner constructs relator-preserving endomorphism candidates for Dehn twists and parity flip, but the inspected declarations do not establish that these descend to automorphisms of the quotient or classify its outer automorphism group. The prose claim `Out(π₁(K)) ≅ ℤ × ℤ₂` exceeds the group-level results visible in this source. |
| `Experimental.Sandbox.Topology.KleinBieberbachWeyl.kreinEta`, `paraComplexK` | Matrices on a two-dimensional module satisfying involution and anticommutation identities. These are operator generators/Clifford relations, not a declared symmetry group in this portion of the owner. |

This pass records Suzuki's noncommutative matrix realization as a genuine
local exceptional-group construction while keeping its proved scope separate
from the external CFSG simplicity theorem. It also avoids promoting a
presentation-level endomorphism calculation to an outer-automorphism
classification without quotient automorphism and exhaustiveness proofs.

## Further owner review: toggle and root-label permutation groups

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.POM.pathToggleGenerator` / `pathToggleOperatorClosure` | Actual involutive permutations of the finite path-independent-set state carrier, and the subgroup they generate in its full permutation group. Adjacent generators are proved noncommuting. `togglePathGroup` is an alias for this generated subgroup; the source expressly does not identify it with the full symmetric group. |
| `Omega.POM.toggleGeneralFiberGroup` | A dependent function type selecting one path-toggle group for each fiber. As written it is not packaged as a product group with pointwise operations in this owner. |
| `Omega.RatioResultant.rootPermutationOperatorRep` / `rootPermutationOperatorGroup` | The full permutation group on root labels represented by invertible operators on the root-function module; injectivity and noncommuting adjacent-transposition images are proved. This is a genuine noncommutative operator realization, and the owner explicitly does not identify it as a Galois group. |
| `Omega.Zeta.syncHatdeltaSpecializedPermutationClosure` | The subgroup of `Equiv.Perm (Fin 6)` generated by a six-cycle and one adjacent transposition. The owner proves this subgroup is top, hence the generated group is `S₆`. The theorem concerns a fixed specialized permutation calculation; it does not construct a generic Galois or monodromy action. |

These concrete owners strengthen the inventory's noncommutative-action
coverage while preserving the distinction between generated subgroups,
operator images, and groups whose identification with a Galois group would
require additional field-theoretic action data.

## Further owner review: quotient actions and orientation sectors

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.GU.normalizerDescend` | A homomorphism from the permutation group `Equiv.Perm (Fin 3)` into permutations of `Fin 3 ⊕ Fin 5`, acting on the first summand and fixing the second. Its owner verifies the S₃ generator relations after descent, but does not prove the representation injective; no operator lift is defined in this owner. |
| `Omega.EA.foldOrientationTag` / `foldOrientationConj` | The former records two permutation signs as a `Bool × Bool` tag; the latter is pointwise conjugation on a family of fiber permutation groups. The owner proves the tag is conjugacy-invariant and sectors/weights are preserved. It does not construct an additional group on the four Boolean tags or an operator representation. |
| `Omega.OperatorAlgebra.inducedFoldPermFun` | A construction used to show a fiber-preserving source permutation descends to a permutation of visible values. The owner proves existence of such a visible permutation for each compatible source permutation; it does not define a homomorphism, kernel, quotient group, or semidirect-product group. The semidirect-product wording in the theorem name is not itself a group construction. |

This source pass separates quotient actions and conjugacy invariants from
operator symmetry groups. These owners contribute action data, but they do
not yet satisfy the stronger noncommutative operator-carrier form used by the
Cantor/Clifford and root-lattice Weyl modules.

## Further owner review: lattice and finite monodromy operators

| Owner declaration | Source-grounded classification |
|---|---|
| `InfoGeometry.RootSystem.Exceptional.rootWeylOperatorUnitRep` / `rootOperatorWeylGroup` | Each exceptional root-lattice Weyl group is represented injectively by units of endomorphisms on real-valued functions on its root lattice. The mapped top subgroup is a concrete subgroup of this noncommutative operator-unit carrier; the owner proves simple reflections lie in it and that noncommuting pairs remain noncommuting. |
| `Omega.CircleDimension.s4HurwitzRepresentativeMonodromy` | The subgroup generated by the first two entries of an explicit permutation triple on four sheets. Its owner proves equality with top, hence it is `S₄`, and verifies the Nielsen product relation. This is a finite monodromy tuple calculation; the owner combines it with separate Hurwitz statements but does not make this subgroup an operator-algebra group. |
| `InfoGeometry.Topology.concretePGOperatorGroup` | The subgroup of units in endomorphisms of real functions on the integer lattice generated by a concrete glide and transverse translation. The operator representation of lattice permutations is proved injective, and the two generators are proved noncommuting in the generated group. The abstract `WallpaperGroupPG` structure alone is a package of relations, not a group carrier. |
| `Omega.GroupUnification.boundaryAxisStabilizer` | The point stabilizer subgroup of `Equiv.Perm (Fin 3)`; the owner identifies its underlying type with permutations of the complementary two-point subtype. This is a subgroup/isomorphism result, not a new independent group beyond the stabilizer. |

These owners add verified lattice Weyl, wallpaper, and finite monodromy
representations. In particular, the root-lattice actions lift the exceptional
Weyl symmetries to invertible noncommutative operators, consistent with the
repository's operator-carrier requirement.

## Further owner review: Lee–Yang monodromy and root-coordinate permutations

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.Zeta.xiLeyangGeometricMonodromyGroup` | The subgroup of permutations of four sheets generated by a four-cycle and an adjacent transposition. The owner proves it equals top, so the generated subgroup is all `S₄`. It explicitly does not construct a function-field Galois action or identify a Galois group with this permutation subgroup. |
| `Omega.Zeta.xi_terminal_zm_leyang_perron_p3_inertia_point_stabilizer_*` | Two explicit permutations of four sheets fixing the distinguished simple sheet: a three-cycle and a transposition on the other three sheets. The owner proves their orders and fixed-point behavior but does not package their generated subgroup or prove it equals the point stabilizer. |
| `Omega.Zeta.xi_terminal_zm_puiseux_infty_4cycle_monodromy` | The four-cycle permutation on the four local branches, with its pointwise action included in an algebraic certificate. This owner does not define the cyclic subgroup it generates or a representation from a fundamental group. |
| `Omega.Zeta.xiTerminalZmSigmaPerm` / `xiTerminalZmIotaPerm` | Explicit `S₃` coordinate permutations on three ordered roots: a three-cycle and a transposition. The owner proves the standard relations, nontriviality, and noncommutation, hence verifies concrete nonabelian `S₃`-type generators. It does not define a separate subgroup carrier or field Galois action. |

The source owners establish concrete finite permutation symmetries. Only the
first defines and identifies a generated subgroup; the remaining declarations
are individual permutations and relation certificates, not additional
group-level constructions.

## Further owner review: symmetric-coordinate invariance certificates

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.Conclusion.permuteBitVec` / `CommutesWithCoordinatePermutations` | The first precomposes bit vectors by `Equiv.Perm (Fin q)`; the second states simultaneous coordinate-permutation invariance of a kernel. The theorem proves that three scalar-valued kernel formulas are invariant. It does not define a homomorphism or operator representation of the symmetric group. |
| `Omega.Conclusion.relabelLocalizedPairwiseData` | A reindexing formula on pair-indexed data by a permutation of a finite cover. Its theorem transports pairwise unions and cardinality spectra under a supplied relabeling identity; it does not construct a separate group carrier or representation. |
| `Omega.Conclusion.primeAdjunctionPermute` | A reordering operation on a finite sequence, with a product-invariance theorem. The prime-adjoining budget is a natural-number product, not a group or operator action. |
| `Omega.Zeta.xi_terminal_zm_leyang_cover_primitive_data` | A structure whose field repeats the already proved equality of the Lee–Yang monodromy subgroup with top. Its degree-two block predicate quantifies over all `S₄` permutations and the owner refutes it, but the structure is not another monodromy group or a primitive-action instance. |

These files use the ambient finite permutation group as an index-relabeling
parameter. Their proved invariance statements do not add group carriers to the
repository inventory.

## Further owner review: fold stabilizers and torsion observables

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.GroupUnification.CubeAuto6` / `foldbin6GeoStabilizer` | `CubeAuto6` is a product type of a coordinate permutation and a Boolean mask, with an action formula on six-bit words but no group operation declared on the product. `foldbin6GeoStabilizer` is a filtered `Finset`, and the owner proves it consists of the identity pair and one involution. This verifies a two-element symmetry set, but the source does not define a subgroup or group isomorphism to `ZMod 2`; the “Z₂ stabilizer” theorem name is stronger than its group-carrier formalization. |
| `Omega.Conclusion.conclusion_monoidal_jump_theory_a2torsion_classification_data` | A structure bundling a function from `Equiv.Perm (Fin 2)` to `ZMod 2` and a multiplication/additivity law. The owner classifies its values on the two-element permutation group and constructs observable extensions. It is a homomorphism/character classification problem; the structure itself is not an additional symmetry group or noncommutative operator representation. |

The fold result is a concrete target for later strengthening: first give the
cube-automorphism carrier its actual composition law, then show the audited
stabilizer is a subgroup and transport that subgroup to a noncommutative
operator-unit representation. Until those steps are present, report it as a
finite symmetry set rather than an established group.

## Further owner review: groupoid automorphism proxies

| Owner declaration | Source-grounded classification |
|---|---|
| `Omega.EA.foldGroupoidAut0OddGenerator` | A dependent sum of fiber labels and `Fin (fiberMultiplicity - 1)` indices. It records odd cohomology generator labels and a cardinality formula; it is not a group carrier. |
| `Omega.EA.foldGroupoidAut0PoincarePolynomial` | A product of `PU(d)`-motivated polynomial factors. It is a formal Poincaré polynomial proxy, not a defined topological group or a representation on a noncommutative operator algebra. |
| `Omega.EA.foldGroupoidAutPi1OrderProxy` | The natural-number product of fiber multiplicities. The theorem proves prime divisibility properties of this order proxy; it does not construct the claimed connected automorphism fundamental group or prove its order equals this product. |

These owners use “groupoid automorphism” in their proxy labels, but the
formalized declarations are generator-index sets and numerical invariants.
They should not be counted as additional groups without a group carrier,
composition, and action being defined.

## Active non-Lean mathematical-source scan

A case-insensitive lexical scan of Python, TypeScript, GAP, and Sage files in
`tools/`, `scripts/`, `src/`, and `cli/` found 58 candidate files for
`symmetry group`, `permutation group`, `dihedral group`, `Weyl group`, `Lie
group`, `automorphism group`, or `group action`. These are not 58 additional
formal group declarations: the set mixes executable GAP/Sage constructions,
CAS verification scripts, SymPy calculations, documentation strings, and
false positives. Reproduce the candidate set with:

```bash
rg -il --glob '*.py' --glob '*.ts' --glob '*.sage' --glob '*.g' --glob '*.gap' \
  '(symmetry group|permutation group|dihedral group|Weyl group|Lie group|automorphism group|group action)' \
  tools scripts src cli
```

Representative non-Lean group-computation sources include the G₂ Bruhat and
flag-action checks in `scripts/verify_g2_root_bruhat_cas.py`,
`scripts/verify_g2_bn_bruhat_complete.py`, and
`scripts/derive_g2_native_flag_stabilizer.g`; the D₄ triality orbit
computation in `tools/gap/d4_triality_orbit_stabilizers.g`; the G₂/SU(3)
stabilizer computation in `tools/gap/g2_su3_stabilizer.g`; and the O(5,5)
Weyl/wallpaper computation in `tools/sage/o55_weyl_wallpaper.sage`. These
sources may supply computational evidence or candidate structures, but they
do not add Lean theorem owners or prove identification with the repository's
noncommutative operator carriers. In particular, the G₂ CAS checks are
separate from the local `adjointGroup` proofs and do not close its missing
`rankOne_bruhat` theorem.

This scan improves coverage beyond the Lean source index, but is not a
declaration-complete census of non-Lean code: lexical scans can miss
conventionally implemented groups and include untyped strings. Archive,
generated, runtime, and external-reference trees remain separately scoped;
the full semantic group inventory is still open.


## CFSG root-operator port update (2026-10-30)

The exceptional group carrier and proof import surface is `InfoGeometry.Exceptional.CFSGPort.All`, included by `InfoGeometry.All`. That surface builds under the root-pinned Lean/Mathlib environment. The local Chevalley port now kernel-checks the G₂ sparse root-operator Weyl-conjugation table for all root indices, simple reflections, and degrees 1–3, and derives the operator identity from each successful checker row. This is a proved relation for the sparse table operators, not an exceptional simplicity theorem or a completed table-to-pinned-generator identification. Exceptional family simplicity and the declaration-complete symmetry census remain open.

The local `ChevalleyRootOperatorMirror.lean` is now publicly imported by
`InfoGeometry.Exceptional.CFSGPort.All`. Its proved `entriesOp_eq_simpleRootCoefficients`
theorem identifies the sparse positive and negative simple-root tables with
the pinned `xCoeff` and `yCoeff` operators for each exceptional root datum in
the local catalog, at degrees 1, 2, and 3. The narrow owner build passed under
the root Lean 4.34.1 / Mathlib d13f23b pin, and the exceptional umbrella also
passed after adding the import (8,989 jobs). This closes the table-to-root-
coefficient identification for the stated rows; it does not yet identify all
root subgroup operators with external Chevalley generators or discharge any
exceptional family normal-subgroup dichotomy. The external CFSG package remains
on its own Lean 4.35.0-rc3 / Mathlib b63f6e8 pin and is not imported by root
Lake.

The earlier root `InfoGeometry.All` failure in the separately modified
`InfoGeometry.Algebra.ZornRightProjectionObstruction` was superseded by the
latest locked aggregate build: 28,248 jobs passed with exit code 0 after
importing the current exceptional CFSG port. `InfoGeometry.Audit` again
reported zero declarations depending on `sorryAx` and 303 generated explicit
axiom constants elsewhere in the repository. This is not a claim that the
repository is axiom-clean or that its full symmetry inventory is complete.

`Exceptional/CFSGPort/ChevalleyRootHeightDescent.lean` now proves positive
height descent by a simple reflection for every nonsimple positive root in
the six certified exceptional root systems. It is publicly imported by
`CFSGPort.All`; the focused target passed (8,942 jobs), the exceptional
umbrella passed (8,990 jobs), and the root `InfoGeometry.All` build passed
(28,248 jobs) on 2026-10-30. This supplies the height induction step from the
external `RootOps.CommAll.commContained_pos` proof. Root-operator commutator
containment in the open-cone root subgroup, the remaining exceptional-family
quasisimplicity proofs, and the complete semantic symmetry census remain open.
