# Corrected Peirce/operator archetypes

## Contract

Replace the proposed `UnifiedGeometryOperatorSignificance` narrative, not the
existing owner definitions, with the following separate mathematical layers.
There is no universal five-pillar geometry theorem here. In particular, a
conjunction of identities does not construct maps between exceptional groups,
analytic operator algebras and differential geometry.

## Source snapshot and stage coverage

The primary source for the Peirce stream is the refreshed Drive export
`cached/aistudio_prompt_1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe_updated.json`
(SHA-256 `4a1318e72e6807bfca2314dc7cc10bfd75b7474f08db6e90fe7b6ac75fe9b34d`).
It contains 35 ordered chunks (18 user, 17 model), from
`2026-10-29T15:50:56.358Z` through `2026-10-30T03:11:33.126Z`. The extracted
transcript contains all labels A1–A44, 30 fenced blocks (20 Lean), and 2,235
math-expression occurrences. These are source-occurrence counts, not counts of
distinct claims. The extraction is indexed in
`cached/aistudio_extracts/aistudio_prompt_1t9Q3cbWphRcmuigvp9LZomzS7Q8Pclxe_updated/`.

The owner coverage is modular rather than a copy of the repeated monolithic
Lean blocks: A1–A11 are in `Tetraktys`; A12–A22 are split between `Unipotent`
and `Homogenized` (`Homogenized` owns the A17 sandwich character table, and `Unipotent` owns the A18 shear identities); A23–A25 are in `Bergman`; A26–A28 in `Supercharge`; A29–A32
in `MixedDifferentials`, `ChiralDifferentials`, `GeneratorDifferentials`, and
`LaplacianHomogenization`; A33–A38 are covered across `Orientation`,
`ComplementSymmetry`, `GeneratorDefect`, `DefectParity`, `DefectLevelSet`,
`DefectTower`, `TransferDefect`, and `ParityProducts`; A39–A44 are mapped in
the sections below. A20 contributes only `x = x` and is intentionally omitted
as a theorem target. The source's tagged Lean blocks remain untrusted input;
owner declarations and their kernel builds are the verification evidence.

The separate 1ofa continuation archive contains 232 ordered turns, 153 Lean
fences, and declarations labeled through A85. Its labels are not unique node
identifiers: source headings reuse A21–A22, A63–A64, A66, A68, A70, A72, and
A73–A75 for distinct or later revised packages. Some later blocks explicitly
say “audited,” “extended,” or “cleaned.” Therefore the dependency map must key
claims by source turn and declaration, retaining the raw label only as source
metadata. Transcript order plus the owner files—not a simple A-number
sequence—determines the causal order. The 1ofa review ledger marks semantic
coverage incomplete; lexical owner-name matches do not establish equivalence.

### 1. Associative inverse decomposition and Peirce corners

Drazin nilpotence requires the Drazin hypotheses. The identity
`x - x*d*x = x*(1-d*x)` alone is a ring expansion, not a spectral theorem.
For orthogonal idempotents p,q, `(p*x*q)^2=0`; sums of such corners can have
nonzero mixed products and higher nilpotency index. No universal shell
filtration or disappearance of mixed associators is claimed in this extension.
The Drazin and filtration corridors remain separate from the pair construction.

### 2. Reflexive square-zero pairs and regular-module projections

Explicit assumptions: d*d=0, B*B=0, d*B*d=d, B*d*B=B.
Existing owner: `Canonical.ReflexiveNilpotentFlows.support_table`.
It supplies idempotence and mutual annihilation of dB, Bd and 1-dB-Bd.
New owner: `Canonical.PeirceWeightedTrace.complement_fixed_iff`:

    (1-dB-Bd)*x=x iff d*x=0 and B*x=0.

This is an exact common-kernel characterization on the regular module. It is
not an elliptic Hodge theorem. Self-adjointness of the products is explicit in
`support_complement_selfAdjoint`; no inverse or adjoint existence is assumed
implicitly. The support projection is not called the Hodge Laplacian.

### 3. Active-corner polynomial identities and ambient units

Owners: `Canonical.GrassmannianBundleCyclotomicOrientability` and
`Canonical.ReflexiveNilpotentFlows`.
Use involutivity for Gamma^2=Delta, not Phi_2. Phi_2(t)=t+1.
Phi_3, Phi_4 and Phi_6 are polynomial identities with Delta as the active
corner identity. They do not establish Kähler integrability or geometric
triality. The Weyl triple product and its two-sided inverse give an actual
ambient unit. Fourth power one means order dividing four, not exact order four.

### 4. Algebraic scalar actions and weighted tracial identities

`ReflexiveNilpotentFlows` owns unipotent, diagonal and rotor composition laws.
Weyl conjugation exchanges the diagonal parameters; it does not identify
negation of an involution with inversion of that involution.

`PeirceWeightedTrace.supportWeight a b d B = a*(Bd)+b*(dB)` (scalar action)
extends the existing full-support CAR density calculation to arbitrary active
support. Its four eigenproduct equations prove division-free intertwining.
`weighted_trace_boundary` reuses
`OperatorAlgebra.TracialCARDensity.eigenproductKMS` and its existing `weighted`
linear functional. No positivity, normalization, topology, analytic strip,
modular operator or Tomita–Takesaki theorem is asserted. Squared weights a=u²,
b=v² are ordinary specializations, not additional axioms.

### 5. Special Jordan products in an associative envelope

Owner: `Core.JordanAssociatorRing`, namespace `Core.JordanAssociator`.
`symm_operator_commutator` proves

    [M_s,M_t](x) = [[s,t],x],  M_s(x)=sx+xs.

`symm_associator_eq_double_commutator` fixes the associator convention.
`symm_operator_reversed_bracket_iff` characterizes when the wrong reversed
sign accidentally agrees, including characteristic two. These results require
no nilpotent pair and are logically independent of layers 2–4. They do not
identify E6 or F4. Reuse these owners rather than duplicating them under
exceptional-algebra names.

### 6. Alternative algebras and their associative operator representations

This is a distinct carrier layer. Alternativity permits square and polarized
anticommutator identities for left multiplication, not preservation of arbitrary
products. The associator measures the failure of multiplicativity. A Clifford
representation need not be injective. An octonionic associator is not called a
Nambu bracket without the required identities. No unconditional gl(3|1),
Cl(3,4) embedding, or exceptional-group identification follows from the pair
identities. Existing Zorn/CAR and obstruction owners must be used for any
further specialization; this change does not replace them.

## Verification boundary

`Canonical.PeirceWeightedTraceAudit` audits the new declarations and the
Jordan sign/trace dependencies directly. The target build checks imported
owners in its dependency cone; it is not a repository-wide build or a proof of
the stronger geometric interpretations excluded above.

## Additive parity exactness when two is invertible

`PeirceSpine/ParityExactness.lean` proves that, for an involutive ring
automorphism σ and invertible 2, `Y + σ Y = 0` holds exactly when
`Y = X - σ X` for some X. The explicit preimage is `(⅟ 2) * Y`.
It specializes to the actual parity ring equivalence. This is an additive
statement with a stated hypothesis, not multiplicative Hilbert 90.
`ParityExactnessAudit.lean` audits its four theorem declarations.

## A51–A52: ordered pullbacks, Jordan triples, and sandwich charges

The mathematical dependency order is:

```text
Basic corner relations ──► InnerPullback ──► PullbackTriple
Unipotent ──► Bergman (existing jordanTriple) ──► PullbackTriple
Basic ──► Tetraktys ──► SandwichCharge
                           five charge equations
                              └─► iterated charge polynomial
```

`InnerPullback.lean` owns `g⁻¹[P,g]`, its conjugate-idempotent interpretation,
and the actual quadratic equation `{P,ω} + ω² = ω`. Its ordinary-derivation
flatness residual is `ω - 2ωP`. The two-cone left and right ordered formulas
are already proved there. `PullbackTriple.lean` adds their sum and difference,
the associative Jordan triple fundamental identity, and the J triple value.
Existing `Bergman.archetype_A25_jordan_triple_and_grade_inversion` supplies the
two cone triple values and the Φ triple value.

`SandwichCharge.lean` defines two-sided multiplication and
`charge P K X = [P,K X] - K([P,X])`. It proves the five integer charge equations,
the square-zero extremal sandwiches, both vanishing same-side mixed
compositions, the double commutator formulas, and the alternating corner
ladder formulas. It explicitly proves the first and second charge iterates,
the cubic difference, and the advertised fifth-degree polynomial
`Δ⁵ K - 5 Δ³ K + 4 Δ K = 0` for the specified sum of five corner operators.
The intake's displayed A52 theorem did not contain this fifth-degree claim.
`ChargePullbackAudit.lean` audits the declarations in these three owners.

These results make no claim of a direct-sum eigenbasis in arbitrary
characteristic, a full Kantor–Koecher–Tits Lie algebra, or differential
Maurer–Cartan flatness. Those require additional structures and proofs.
The integer charge equations themselves need no division or commutativity
assumption on the ambient ring, and apply to full matrix rings.

### Full endomorphism-ring annihilator

`PeirceSpine/EndomorphismCharge.lean` strengthens the specified-sum result to
**every** native integer-linear endomorphism `K : Module.End ℤ B`.
Its dependency chain is the existing
`Core.PeirceAdjointCycle.ad_cube_eq_ad`, the universal associative-ring lemma
`tripotent_comm_fifth`, and the native adjoint action on the endomorphism ring.
`endomorphismCharge_fifth` proves the fifth-degree equation in that ring;
`endomorphismCharge_pow_apply` identifies its powers with `chargeIter`, and
`chargeIter_fifth_of_linear` gives the pointwise theorem. Linearity is explicit:
this statement is not asserted for arbitrary functions `B → B`.

The umbrella and `EndomorphismChargeAudit` compiled successfully in the locked
build (3218 jobs, exit 0). The five audited declarations use only standard Lean
foundational axioms. This establishes an annihilator, not minimality or a
characteristic-free eigenspace decomposition.

### Charge sectors and the bracket closure law

`PeirceSpine/ChargeSectors.lean` defines the integer charge-n sector as the
native submodule `ker (endomorphismCharge P - n • id)` of `Module.End ℤ B`.
It proves that charge is a derivation of composition, composition adds charges,
and the native Lie bracket adds charges. The identity endomorphism has charge
zero. These six declarations are audited by `ChargeSectorsAudit.lean`.

This step depends on `EndomorphismCharge`, but needs no idempotence hypothesis:
charge addition holds for the adjoint action of any P. Idempotence enters the
separate fifth-degree annihilator. Neither result alone identifies the listed
five sample maps with all the homogeneous components, nor proves directness
in characteristics where the integer charges coincide.

### Concrete operators inhabit the charge sectors

`CornerChargeSectors.lean` reuses `LieJordanBoundaryComposition.sandwichOp`,
`crossTransport`, and `LieJordanEndomorphisms.lieOp`; it introduces no second
bundling of these operators. The two same-corner sandwiches have charges ±2,
the two corner inner derivations have charges ±1, and cross transport has
charge zero. The commutator of the opposite corner inner derivations equals
`lieOp ℤ Σ`, which consequently belongs to the neutral sector.

Dependencies: `SandwichCharge` pointwise identities → `ChargeSectors` native
submodules, together with the existing LieJordan composition owners →
`CornerChargeSectors`. Seven theorem declarations compiled and passed the
axiom audit using only `propext` and `Quot.sound` (locked build, 3120 jobs).
These memberships do not assert that five particular operators span every
sector, or that coincident integer charges are independent.

## A39–A44: defect, transfer, cyclotomic, and chiral-factor claims

The later source snapshot's A39 defect iteration is represented by
`DefectTower.lean`; A37 transfer-defect and A36 seed-level identities are
owned by `TransferDefect.lean`, `DefectLevelSet.lean`, and `TransferMoments.lean`.
`CyclotomicBridge.lean` records the ordered polynomial evaluations, and
`PrimalDual.lean` owns the chord-potential identities. These are polynomial
identities in the Peirce ring; analytic zeta, number-field splitting, and
convex-analytic interpretations do not follow from the names.

`ChiralEulerFactors.lean` proves the four ordered products of the two
orthogonal Peirce cycles, their quadratic product, and the ordered
four-supercharge product. Two accompanying prose claims need correction:

* In A43, `superDerivPhiBar` annihilates `Σ`, but on the chiral factor
  `1 - Σ` it has residual `2Φ`. `ChiralDifferentials.lean` proves the
  residual and the exact iff condition for vanishing.
* In A44, the mixed products have odd residuals in the `N₋` corner for the
  stated factor orders. `Supercharge.lean` proves those expansions and the
  condition under which replacing the residual by the `N₊` corner is valid.
* The shortened A40 chiral Mangoldt identity omits a term in general.
  `TransferDefect.lean` proves the corrected product and characterizes when
  the shortened equality holds.

These results justify the finite ordered ring factorizations only. The labels
“Euler factor,” “Dirichlet factor,” “prime,” and “Mangoldt” add no analytic or
arithmetic structure to the carrier.

## A45–A50: grading perturbations, defect decompositions, and transport

The pasted continuation reuses the labels A49 and A50 for two different
packages. Preserve the mathematical dependency order rather than treating the
labels as unique identifiers:

```text
A43–A44 chiral factors
 └─ A45–A46 grading perturbations and commutator modes
     ├─ A49b completed-square transfer identity
     └─ A50b double-commutator mode equations
A47 ring-hom naturality ──► A48 matrix-limit coherence
A49a–A50a parity decomposition and defect anomaly
```

`GradingPerturbation.lean` proves the squares of `S ± Φ` and `S ± J`, their
ordered products, and the grading sandwich identities. `GradingTransfer.lean`
proves the transfer-defect/square relation, the completed-square identity,
and the first commutators of `S + Φ` on `J` and `Σ`, together with second
commutators on `J`, `Φ - Σ`, and the grading. These are operator-valued
polynomial identities in an arbitrary associative ring. The coefficients
multiplying modes are not scalar eigenvalues over a field, and no
diagonalization is claimed.

`DefectParity.lean` proves the general even/odd decomposition of the
idempotency defect, the defect of an odd perturbation of `P`, and its
commutator-square formula. It also proves the mixed `V + Φ` decomposition and
the second-order derivation mismatch. These owner statements formalize the
valid algebraic content of both A49/A50 versions without identifying the
parity difference with a Hilbert 90 theorem or a field extension.

`RingHomTransport.lean` proves naturality for the listed Peirce polynomial
operators (including the four homogenized channels), while
`MatrixColimitTransport.lean` proves the stated bonding-map coherence in the
repository's existing matrix limit. This is not a theorem that every
cohomology group or every object in the repository's operator spine is
transported by a single declaration.

### Supported endomorphism decomposition

`EndomorphismBlocks.lean` uses the negative-corner projection, the existing
`Core.PeirceGrading.even`, and the positive-corner projection. Their sum is the
identity; for idempotent P they are pairwise orthogonal idempotents. Every
integer-linear endomorphism K decomposes as the nine blocks `Eᵢ K Eⱼ`.
The extraction theorem recovers a block and annihilates differently supported
blocks, without dividing by charge differences. Equality is detected by all
nine blocks. `fiveSupportedComponent` groups them by output-input degree
(-2 through 2), and their sum reconstructs K.

This is a support-based construction on the full endomorphism ring, valid in
all characteristics. At this stage its reconstruction and nine-block
extraction are formalized; identifying the grouped components with charge
submodules and packaging a graded algebra remain separate obligations.

### Charges of the supported components

`BlockCharges.lean` connects the full supported decomposition to the charge
submodules. The degree of each of the three Peirce projections is -1, 0, or 1.
Its left and right compositions with `ad P` are both multiplication by that
integer. Thus `Eᵢ K Eⱼ` has charge `degree i - degree j`, for arbitrary K in the
full integer-linear endomorphism ring. Adding blocks of the same degree gives
membership of each `fiveSupportedComponent P K d` in charge sector `d - 2`.
These are inclusions; equality with whole eigenspaces is not asserted.
`BlockChargesAudit.lean` audits both public statements and their dependencies.

## A53–A54: corrected scaled extraction and ordered brackets

For Dₙ = chargeIter P (cornerOperatorSum P A C) n, the corrected equations are

```
4D₂ - D₄ = 3(G₊₁ + G₋₁)
4D₁ - D₃ = 3(G₊₁ - G₋₁)
(4D₂ - D₄) ± (4D₁ - D₃) = 6G±₁
D₄ - 5D₂ + 4D₀ = 4G₀
(D₄ - D₂) ± 2(D₃ - D₁) = 24G±₂.
```

`ChargeExtraction` owns the five individual extraction formulas;
`ChargeExtractionBalances` owns the paired sum/difference coefficients.
The original factors 12 and 6 in the degree-one paired equations are incorrect.
These are division-free scaled identities, not an inverse Vandermonde matrix
over ℤ: for the ordered charges `(-2, -1, 0, 1, 2)`, the power-matrix
determinant is `288`, which is not a unit in ℤ. `ChargePowerMatrix.lean`
contains the determinant and no-left/right-inverse theorem statements with
proof terms. `ChargePowerMatrix.lean` passed the locked
`ChargeExtractionBracketAudit` build. Recovering unscaled operators requires
appropriate invertibility.
The fifth-degree annihilator is already owned by `SandwichCharge` and, on all
integer-linear endomorphisms, by `EndomorphismCharge`.

`CrossChargeBrackets` reuses the existing LieJordan bundled maps and proves
ordinary inner-derivation/sandwich bracket identities. In particular the
extremal bracket is **Q₊ X Q₋ - Q₋ X Q₊**, because right multiplication reverses
order under composition. The exact residual of the intake's same-support
formula is **-V X Σ**. Membership in charges -1, +1, and 0 follows from the
already proved charge-addition law; the opposite inner-derivation bracket is
owned by `CornerChargeSectors.opposite_lie_comm`.

Causal order: `SandwichCharge` → scaled extraction; `CornerChargeSectors` plus
`LieJordanBoundaryComposition` → ordered bracket formulas and sector membership.
`ChargeExtractionBracketAudit` audits these corrected statements. A combined
locked build of `ChargePullbackAudit` and `ChargeExtractionBracketAudit` passed
(exit 0), with
axiom reports limited to standard foundations (`propext`, `Quot.sound`, and
`Classical.choice` for the determinant/non-inverse results). The replay emitted
warnings in unrelated `FiniteMatrixNoncommutativity` and
`LieJordanEndomorphisms` dependencies. This does not identify the five sample
operators with a full Kantor–Koecher–Tits algebra.

The degree-one paired equations are scaled by 3, not 12 and 6:
`4D₂-D₄ = 3(G₊₁+G₋₁)` and `4D₁-D₃ = 3(G₊₁-G₋₁)`. Combining them gives
`6G₊₁` and `6G₋₁`, respectively. The degree-two combinations do give
`24G±₂`. These are integer-scaled identities; the charge power matrix has
determinant 288, so the proposed integer Vandermonde inverse is false.

The A51 pullback owners were checked in the same audit run via
`ChargePullbackAudit`. Their correction satisfies the
idempotency-transport equation. The ordinary commutator expression is not
asserted to satisfy `dΩ + Ω² = 0`; the matrix Maurer–Cartan cochain is a separate
owner surface.

## A55–A58: defect polarization, tripotents, and polynomial evaluations

The later 232-turn export at
`cached/aistudio_extracts/aistudio_prompt_1ofaG3fBD1VlprR7ShtsdctpOVRjmjB9f/`
contains the A55–A85 continuation. Its lexical extraction is not a semantic
or proof audit; the accompanying `cached/source_stream_1ofa/review_ledger.json`
marks the review as incomplete.

The sound A55 core starts with the universal identity

```
δ(x + y) - δ(x) - δ(y) = x*y + y*x.
```

`Core.IdempotentGraphGrassmannian.idempotencyDefect_add_polarization` now owns
this identity over an arbitrary associative ring. The idempotent specialization
is then connected to odd Peirce perturbations by
`PeirceSpine.DefectParity.odd_perturbation_defect`; the generator cases and
defect/commutator comparisons are in `GeneratorDefect` and `DefectParity`.
This is defect polarization and a Peirce-grade formula; it does not make the
defect a universal grading operator on the whole ring.

`PeirceSpine.TripotentDefect` records the division-free polynomial identities
for `τ(T) = T^3 - T` and the three scaled color expressions. Under `T^3 = T`,
the zero-color expression is idempotent, while the other two satisfy scaled
projector equations with factor 2. For orthogonal idempotents `R,G`, the
difference `R-G` is tripotent and `1-R-G` is the complementary idempotent.
This algebra alone does not construct an `su(3)` representation or prove a
three-color symmetry algebra. The new owner passed its locked targeted build
(exit 0; 620 jobs); only a LeanArchitect dependency warning remained.

`PeirceSpine.CyclotomicBridge` owns finite polynomial evaluations on the
transfer generators. Its Cayley–Weyl inverse statement is explicitly
equivalent to vanishing of the metric idempotency defect; it does not assert
unconditional roots of unity, a spectrum, or an analytic zeta function.

### A63–A66: Peirce block invariance and the cone–sheet braiding core

The A63–A64 continuation contains valid Peirce statements alongside physical
interpretations. Self/anti-self-duality of `Q₊` and `Q₋`, and `[P,V]=[P,Σ]=0`,
are already owned by `StarGrading`/`Basic`. The new `BoundaryDependence` owner
proves that even Peirce additions to either input leave both cones, all four
tetraktys generators, and the transfer defect unchanged. This is the precise
algebraic content of “depends only on cross-corner data”; it does not prove an
entropy or geometric area law.

The transcript's `W₁₂`, `W₂₄`, and `mog24` operators are presented as
integer-linear combinations of the charge maps. Those formulas alone do not
construct Golay codes, the Leech lattice, or a quantum error-correcting code:
such interpretations need a specified carrier, code submodule, and proved
intertwining/correction property. The displayed four-link plaquette
interpretation is also not promoted here; its claimed low-order expansion
must be proved against the noncommutative Peirce normal form before it can be
used as an archetype theorem.

Dependency order: Peirce corner support → star/parity identities and
`BoundaryDependence`; Peirce cycle orthogonality → finite defect splitting and
`ConeSheetBraiding`; a code or lattice interpretation would require a further
explicit map from these operators to the relevant finite carrier.

The A65/A66 transcript gives six ordered relations between the Peirce cycles
`Q₊ = N₊N₋`, `Q₋ = N₋N₊` and the cones `N₊`, `N₋`. The generic lemma
`Core.idempotencyDefect_iterates_intertwines` propagates the two cross-sheet
intertwiners through every finite defect iterate; one-sided annihilation is
also preserved under iteration. The new `ConeSheetBraiding` owner packages
these six consequences and the resulting commutation of the sum of the two
iterated sheets with each cone and with `Φ` and `J`. It is staged, but its
kernel build is pending.

This establishes an algebraic precursor to the transcript's claimed error
immunity. It does not establish the claimed Golay/Leech `W₂₄` or `mog24`
recovery: no such map is defined by these Peirce relations, so that claim
needs its own carrier and intertwining theorem. The archive reuses archetype
labels in later blocks; this entry is identified by its transcript position
and mathematical content, not by A65/A66 alone.

Causal order: Core defect polynomial → defect polarization and Peirce
decomposition (`DefectParity`) → generator specializations (`GeneratorDefect`)
→ tripotent polynomial consequences (`TripotentDefect`). The selected
cyclotomic evaluations depend on `Unipotent` and `TransferDefect`. The further
A59–A62 group and coding-theory interpretations are not consequences of these
polynomial identities alone; they require separate carrier maps and proofs.

## A85: block-lower-triangular operators and orthogonal intervention

The archived A85 block in the 1ofa continuation defines an operator as the
sum of its `11`, `01`, and `00` Peirce corners. The corresponding abstract
ring claims are: the upper-right corner vanishes; the three displayed corner
projections recover their inputs; this class of operators is closed under
multiplication with the stated block formula; and compression by the
complement of an orthogonal idempotent is idempotent, annihilates that
idempotent on both sides, and preserves the original `11` corner.
`PeirceSpine.BlockTriangularIntervention` is the small owner for these claims.
Its initial revision passed the targeted locked Lake build (613 jobs; exit 0),
with unused-section-variable warnings on four compression lemmas. After a
section refactor narrowed the compression theorem hypotheses, a combined
locked build requested this module and `TripotentDefect` and exited 0; Lake
rebuilt `TripotentDefect` and reported `BlockTriangularIntervention` already up
to date. It proves algebraic block identities over an arbitrary ring;
the causal-attention, token-mask, and intervention semantics in the source
are not encoded by the ring alone. In particular, a Peirce block pattern does
not model the row-normalized softmax attention map, learned time bias, or the
paper's event-causality extractor. The connection is an algebraic analogy
requiring an explicit representation map before it can be called an
isomorphism. `idempotentCompression_removed_terms` isolates the exact
noncommutative difference `T - (1-Q)T(1-Q) = QT + TQ - QTQ`; orthogonality
then gives the separate `11`-corner nullity result for the intervention
difference and preserves the factual corner under compression. The initial
proof terms were kernel-checked by the targeted build; the current refactor
was included in the combined locked build, which exited 0; the module was
reported already up to date.

Causal prerequisite: the Peirce corner normal form and idempotent complement
identities in `PeirceSpine.Basic` precede the block multiplication and
compression consequences. This local algebraic dependency does not establish
the intervening A63–A84 source blocks, which require their own source-to-owner
review.

### Supported component projectors

`EndomorphismBlocks → BlockCharges → SupportedProjectors` bundles the five
support-defined components as native integer-linear endomorphisms of
`Module.End ℤ B`. For an idempotent P, they are mutually orthogonal idempotents,
sum to the identity, and uniquely recover a decomposition whose terms are fixed
by the corresponding projectors (`supportedProjector_unique`). This is a
characteristic-free support decomposition, not a claim that integer charge
eigenspaces are distinct in characteristics 2 or 3. It does not identify the
result with a Kantor–Koecher–Tits construction.

### A58–A60: polynomial evaluations versus group structure

`PeirceSpine.CyclotomicBridge` proves finite polynomial evaluations and an
iff criterion relating the Cayley–Weyl pair to the defect-zero locus. These
identities do not by themselves make `P + J` a root of unity off shell:
its displayed cyclotomic evaluation is `1 - V`, which vanishes only under an
additional condition such as `V = 1`.

The transcript's proposed `S₃` and `V₄` terminology also needs a scope
condition. The displayed rotation pair has product `V`, and the proposed
reflections have squares involving `V` or `V²`; these are not group relations
without appropriate unit-shell hypotheses. A claim about an abstract group
requires an explicit group carrier and a verified multiplication action. The
operators `(V, Φ, J, Σ)` alone do not define a Klein four group.

### A61–A62: scaled charge maps and defect iteration

The all-depth identity that the defect iterates split across two orthogonal
inputs is owned by `Core.IdempotentGraphGrassmannian.idempotencyDefect_iterates_add_of_orthogonal`.
It applies to the orthogonal Peirce products `Q₊` and `Q₋` and is a genuine
finite algebraic iteration result.

The transcript's proposed `W₁₂` and `W₂₄` charge frames do not have the stated
sector coefficients: with the displayed definitions, `golay12Root` is three
times the sum of the degree `±1` sectors, and the `golay24` degree `±1`
expressions inherit the incorrect A53 coefficients. These formulas should not
be called a Golay code, Leech lattice, MOG, or Knill–Laflamme correction
statement without an explicit carrier and proved code/error conditions.

The A55 comparison between the derivation mismatch/projector value and the
second defect iterate is now exposed as two reusable lemmas in
`PeirceSpine.GeneratorDefect`. The locked `GeneratorDefectAudit` build passed;
the new declarations have only `propext` and, for the projector rewrite,
`Quot.sound` among their reported axiom dependencies. This is a finite
re-expression using `δ(P+Φ)=V`, not a proof of an infinite grading.

### A63–A64: Peirce duality and boundary invariance

`Orientation` proves eigen-equations for the repository's map
`hodgeStar P X = invS P * X`; this is an algebraic involution and does not by
itself provide metric Hodge theory. `BoundaryDependence` proves that even
Peirce shifts of the inputs leave the cone generators, tetraktys, and transfer
defect unchanged. That is an algebraic cross-corner dependence result, not an
entropy or information-theoretic area law.

The proposed Wilson loop identity is incorrect for the displayed words. With
`a=N₊`, `b=N₋`, expansion gives `U=1+Σ−VJ+Q₊²` and the reversed word
`Urev=1−Σ+VJ+Q₋²`. Hence the even Peirce component of
`(1−U)+(1−Urev)` is `−V²`, not `2V`. A separate corrected loop observable
would need its own definition and proof.

The corrected ordered plaquette expansions now have a dedicated owner in
`PeirceSpine.WilsonPlaquette`. The locked `WilsonPlaquetteAudit` build passed;
both theorem axiom reports contain only `propext`.

### A65–A67: all-depth two-sheet braiding

`PeirceSpine.ConeSheetBraiding` proves the six ordered annihilation and
intertwining relations for the two iterated QGT sheets at every natural defect
depth. Their sum commutes with both cones and therefore with `Φ` and `J`.
This is the operator-algebraic content of the all-scale protection claim.
The related `W₂₄`/MOG decoder language is not supported by this owner: the
transcript's degree `±1` sector maps retain the A53 coefficient error, and no
logical code submodule, error set, or Knill–Laflamme criterion is supplied.

### A68–A69: linear combinations of sandwich maps

The A68 diffusion/focusing formulas are decompositions of existing double
commutators into the cross-sandwich residual and same-sandwich term, both
already represented in `PeirceSpine.Tetraktys`. Those are valid algebraic
identities under the Peirce hypotheses. Their dynamical labels do not add a
wave, horizon, or soliton model. A69's single-sheet decoder claims rely on the
transcript's `W₂₄`/MOG sector formulas, including the A53 coefficient error,
so no error-correction conclusion is promoted.

### A70–A72: focusing labels and parity-reversed Steinberg conjugation

The Peirce corner facts behind A70 are already covered by `Basic`, `Tetraktys`,
and `ConeSheetBraiding`: same-corner products vanish; the two QGT corners have
their stated two-sided support; the same-corner sandwich acts on the cones by
the corresponding cubic words; and defect iterates retain the ordered
intertwining relations. These facts are algebraic. The archive's separate names
`focusingOp`, `diffusionOp`, `daughterIdemTower`, `mandelbrotTower`,
`chiralFractalBranch`, and `mog24V` do not occur as definitions in the searched
repo-owned Lean sources. In particular, no physical retrocausality or
error-correction result follows from the corner identities.

For A71–A72, `Unipotent` proves the Steinberg braid has the displayed inverse,
and `Supercharge` proves that parity conjugation is an involutive ring action.
The new `PhaseConjugateSteinberg` owner combines those existing facts to prove
that parity conjugates the braid to its inverse and that the associated
conjugation/parity round trip fixes every element of the ring. Its audit build
passed; both declarations report only `propext`. The result is an associative
ring identity and does not establish an optical medium, a turbulence model, or
the archive's dual-Bruhat claim. The dual-Bruhat names have no corresponding
definitions in the searched Peirce owner modules.

Causal order: Peirce corner relations → Steinberg braid inverse and parity ring
action → parity-conjugate braid identity → round-trip identity. A70's proposed
all-scale “decoder” is downstream of the incorrectly scaled A53 sector maps
and is not accepted as a code theorem.


## A73-A84: operator dynamics and ideal/projective extensions

The transcript contains several later uses of the A73 label and blocks A74-A84.
The A73 core identity is owned by `PeirceSpine.ParityDoubleDerivation`:
for all `X` over an arbitrary associative ring with an idempotent `P`,
`comm P (derivSqPhi P A C X) = derivSqJ P A C (comm P X)`, and the reverse
identity holds with `Φ` and `J` exchanged. The locked
`ParityDoubleDerivationAudit` build passed (615 jobs, exit 0); both declarations
report only `propext`. The module is imported by `PeirceSpine.lean`; the
integrated locked build passed after both A73 and A74 integrations (3234 jobs, exit 0).

A second A74 core is owned by `PeirceSpine.CurvatureDoubleCommutator`. It
formalizes the sum of the `Σ` inner derivation and the signed `Φ` double
commutator and proves its quadratic relation on both `Φ` and `J`. The locked
audit build passed (615 jobs, exit 0), with axiom dependencies limited to
`propext` and `Quot.sound`. The remaining A73/A74 statements and later A75-A84
claims are not implied by these two extracted results.

The A77-A79 ideal/chart subclaims have matching owners in `StarGrading` and
`IdealChartPairing`: these prove the star reversal of Peirce corners, the
grading-twisted anti-involution, the principal-ideal pairing, the chord square,
and the ordered chart fidelity and defect equations. Their combined locked
audit passed (677 jobs, exit 0). One A79 equation in the transcript is wrong:
`(P_A + P_C - P)^2` is `P - J - V`; the shorter `P - V` form holds iff
`J = 0`. The owners prove operator-valued algebra only, not probability or
positivity. A80/A82 still depend on the unlocated all-scale tower APIs.

Turn 229's finite ABL-style sandwich of the chart elements is now owned by
`PeirceSpine.TwoStateSandwich`: writing `Q₊ = N₊N₋`, it proves
`(P-N₊) Φ (P+N₋)=0`, `(P-N₊) J (P+N₋)=2Q₊`, and
`(P-N₊) V (P+N₋)=Q₊-Q₊²`. The submitted equality for the `Σ` sandwich was
incorrect: its value is `Q₊+Q₊²`, not `Q₊-Q₊²`. The locked audit build passed
(615 jobs, exit 0), and the theorem reports only `propext`.

The complementary-ideal pairing is also proved in `TwoStateSandwich`, under
the explicit `StarRing` and `star P = P` assumptions. Its correction is
`peirce00 P (star X) * peirce00 P X - Q₋(star X, X)`: reversing the two
arguments of `Q₋` is necessary in the noncommutative product. The extended
locked audit passed (676 jobs, exit 0); this theorem reports only standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`). It is an
operator-valued pairing identity, not a positivity or Krein-space theorem.

`chart_spinor_selection_products` proves the four ordered products of
`Φ±J` with the two chart elements. The final product is `+2N₊`; the submitted
`-2N₊` sign is false. The other three products match the corrected ring
identities. This is a product table, not a representation of the Klein-four
group.

The finite chart-point product `(P-N₊)(P+N₋)=P-Q₊` is also proved by
`chart_point_product`; its off-diagonal terms vanish by Peirce support.

There is also a concrete A82 error already at defect depth `n = 0`:
`(P-N₊) Σ (P+N₋)` differs from `(1-V)Q₊` by exactly `2Q₊²`.
`chart_sigma_euler_compression_residual` proves this correction in the same
noncommutative ring setting. Thus the proposed A82 `Σ` compression is false
without an extra hypothesis forcing `2Q₊² = 0`; no such hypothesis is present
in the transcript. The targeted audit passed (677 jobs, exit 0), and the new
residual theorem reports only `propext`.

The same turn's star-chart duality is covered by `StarGrading`; it remains
conditional on a self-adjoint idempotent. The claimed Klein-four “group action”
is not established by the displayed elements, and the proposed dual Bruhat
map and complementary Krein signature need separately defined carriers and
proofs.

### Full all-depth extensions and misconception corrections (A65–A86 and PeirceDefectBridge)

1. **A20 homogenized-channel sandwich intertwiners (`PeirceSpine.Homogenized`):**
   `archetype_A20_weyl_clifford_covariance_of_homogenized_projectors` proves
   all eight displayed identities for arbitrary `A`, `C`, and `X` in a ring
   with an idempotent `P`: each of the four polynomial channels intertwines
   with the specified `J` sandwich and the specified `Φ` sandwich. These are
   identities of polynomial maps under those sandwiches; the theorem does not
   assert that either sandwich is invertible or defines a group action.

2. **A18/A72–A73 Dual Steinberg products (`PeirceSpine.Unipotent`, `PeirceSpine.PhaseConjugateSteinberg`):**
   `steinbergBraidDual` and `steinbergBraidDualInv` formalize the lower
   three-factor product `(1 - N₋)(1 + N₊)(1 - N₋)` and its two-sided inverse
   (`steinbergBraidDual_mul_inv`). `steinbergBraid_dual_expansion_and_difference`
   proves its Cayley–Weyl decomposition `W - (1 - V) N₋`, the product-difference
   identity `steinbergBraid - steinbergBraidDual = (1 - V) Φ`, and the associated
   ring-element sum identities. These are not a Yang–Baxter equation or trace
   statements. `parityConj_steinbergBraidDual_and_bruhat_factors`
   proves that parity conjugation sends `steinbergBraidDual` to its inverse and
   exchanges the two-factor Bruhat chart factors with their inverses.

3. **A66/A74/A75 Chiral defect-iterate sheet `qgtDefectDiff` (`PeirceSpine.ConeSheetBraiding`):**
   `qgtDefectDiff P A C n = δ^[n](Q₊) - δ^[n](Q₋)` formalizes the chiral
   cycle difference at arbitrary defect depth `n : ℕ`.
   - `qgtDefectDiff_anticomm_cones` and `qgtDefectDiff_anticomm_generators`
     prove that `qgtDefectDiff P A C n` anticommutes with `N₊`, `N₋`, `Φ`, and
     `J` at every depth `n`.
   - `qgt_defect_iterates_cross_orthogonal` proves multi-depth cross-sheet
     orthogonality `δ^[n](Q₊) δ^[m](Q₋) = 0 = δ^[n](Q₋) δ^[m](Q₊)` for all
     `(n, m : ℕ)`.
   - `qgt_defect_iterates_graded_products` proves the multi-depth product table
     for `δ^[n](V)` and `qgtDefectDiff P A C n`.
   - `qgt_defect_iterates_invS_and_parity` proves the all-depth `invS P` grading
     action (`invS P * δ^[n](V) = qgtDefectDiff P A C n` and
     `invS P * qgtDefectDiff P A C n = δ^[n](V)`) and `parityConj P` invariance.
   - `qgt_defect_iterates_chiral_eigenvalues` records the all-depth left action
     of `Σ` on the two defect sheets and their sum/difference.
   - `sandwichSame_multipass_idempotencyDefect` identifies the three multipass
     differences with `-δ(V)` times the corresponding cone or `Φ`; the sign is
     part of the proved statement.

4. **A75b/A76 All-depth curvature double commutator (`PeirceSpine.CurvatureDoubleCommutator`):**
   `curvatureDoubleCommutator_mul_genV_defect_iterate` proves that
   `curvatureDoubleCommutator P A C` commutes with right multiplication by
   `δ^[n](V)`. Consequently, `curvatureDoubleCommutator_even_defect_iterates`
   and `curvatureDoubleCommutator_quadratic_odd_defect_iterates` extend the
   first-order relaxation law on `qgtDefectDiff P A C n` and the second-order
   telegrapher quadratic relation on `Φ δ^[n](V)` and `J δ^[n](V)` to all
   depths `n : ℕ`. `madelung_vorticity_factorization_defect_iterates` further
   identifies the two commutator actions with the paired `J` and `Φ` modes and
   factors their product through `Σ` and the squared symmetric defect iterate.

5. **A80 local-chart all-depth two-state sandwiches (`PeirceSpine.TwoStateSandwich`):**
   `chart_two_state_qgtPlus_defect_iterate`, `chart_two_state_qgtMinus_defect_iterate`,
   `chart_two_state_genV_and_qgtDefectDiff_iterates`, and
   `chart_two_state_odd_defect_iterates` prove the two-state chart sandwiches
   at every defect depth `n : ℕ`:
   - `(P - N₊) δ^[n](Q₊) (P + N₋) = δ^[n](Q₊)`
   - `(P - N₊) δ^[n](Q₋) (P + N₋) = -V δ^[n](Q₊)`
   - `(P - N₊) δ^[n](V) (P + N₋) = (1 - V) δ^[n](Q₊)`
   - `(P - N₊) (qgtDefectDiff P A C n) (P + N₋) = (1 + V) δ^[n](Q₊)`
   - `(P - N₊) (Φ δ^[n](V)) (P + N₋) = 0` and `(P - N₊) (J δ^[n](V)) (P + N₋) = 2 V δ^[n](Q₊)`.
   These are identities for the local chart factors defined in that file. They
   do not identify those factors with the separate transcript tower symbols
   `P_{k+1}` and `P_{C,k}`; that bridge remains unformalized. Within the local
   chart, the chiral sheet difference is compressed by `1 + V`, with residual
   `2 V δ^[n](Q₊)`. Similarly, in `TwoStateSandwich`, `chart_bruhat_factor_mul_inv`,
   `chartBruhatConj_mul`, and `chartBruhatConj_genV` prove that the two-factor
   chart map preserves multiplication and fixes `genV P A C`; no identification
   with the transcript's distinct multiscale map is asserted here.

6. **A83 Two-connection Jordan vs. Lie cross-terms (`PeirceSpine.Tetraktys`):**
   `phi_add_j_square_genV_form`, `phi_j_comm_expansion`, and
   `phi_add_j_mul_phi_sub_j` prove that the cross-term in `(Φ₁ + J₂)²` is the
   Jordan anticommutator difference `-(genV P A₁ C₂ - genV P A₂ C₁)`, whereas
   the chiral curvature sum `genSig P A₁ C₂ + genSig P A₂ C₁` appears in the
   commutator `-[Φ₁, J₂]` and in the conjugate product `(Φ₁ + J₂)(Φ₁ - J₂)`.

7. **A86 All-depth lower-triangular Peirce assembly (`PeirceSpine.BlockTriangularIntervention`):**
   `blockLower_genV_defect_iterate` proves that at every defect depth `n : ℕ`,
   `blockLower P (δ^[n](V)) (Φ δ^[n](V)) (δ^[n](V)) = (1 + N₋) δ^[n](V)`.

8. **Multiscale unipotent idempotent tower and Peirce defect bridge (`PeirceSpine.Unipotent`, `OperatorAlgebra.PeirceDefectBridge`):**
   `unipotentIdempotentTower` formalizes the recursive unipotent shear tower
   `P_{k+1} = (1 + N_{+,k}) P_k (1 - N_{+,k})` with idempotence, parent–child
   absorption, and edge-commutator theorems at every scale `k : ℕ`.
   `PeirceDefectBridge` proves the exact bridge from `oddGrade P A` and
   `evenGrade P A` to `genV P A A`, `qgtPlus P A A`, `qgtMinus P A A`, and
   `idempotencyDefect`. Separate concrete noncommuting `2 × 2` matrix
   witnesses are owned by `OperatorAlgebra.PeirceDefectMatrixWitness`.

9. **A58–A60 Operator cyclotomic roots, `S₃` braiding, and Klein-four tomography (`PeirceSpine.CyclotomicBridge`):**
   `archetype_A58_operator_cyclotomic_roots_and_discriminants`,
   `archetype_A59_s3_operator_cyclotomic_braiding_and_reflections`, and
   `archetype_A60_s3_klein_four_decomposition_and_tomography` formalize
   `peirceTransferJComplement`, `cubeRootOp`, `cubeRootOpConj`, `s3Refl0`,
   `s3Refl1`, and `s3Refl2` with two SymPy-verified sign corrections to the
   `1ofaG` transcript (`cubeRootOp² - cubeRootOpConj = 1 - genV P A C` in A59,
   and `s3Refl1 P A C - s3Refl2 P A C = -genJ P A C - (2 : ℤ) • genSig P A C`
   with `hProjSig` coefficient `-16` in A60).
   In addition, `unipotentPlus_double_pass_and_parityConj_round_trip` (`A71` in
   `PhaseConjugateSteinberg`), `qgt_defect_iterates_sandwichCross` (`A66`–`A68`
   in `ConeSheetBraiding`), `qgt_defect_iterates_cone_echo_and_cubic` (`A70` in
   `ConeSheetBraiding`), and `derivSq_and_hProj_defect_iterates` (`A65`/`A67` in
   `CurvatureDoubleCommutator`) complete the defect-tower operator identities.

10. **Stage D₁₅ Directed adjacency split, grading-twisted Laplacian, and 3-layer DAG resolvent (`PeirceSpine.StarGrading`, `PeirceSpine.BlockTriangularIntervention`):**
    `digrac_flow_imbalance_and_magnet_laplacian` in `StarGrading.lean` formalizes
    `digracSym`, `digracImb`, `magnetAdj`, and `magnetLaplacian` over an arbitrary
    `[Ring B] [StarRing B]` with self-adjoint idempotent `P`.
    `ranked_dag_three_layer_resolvent` and
    `stage_D15_digrac_magnet_dag_resolvent_and_tcr_former` in
    `BlockTriangularIntervention.lean` formalize the three-layer transition
    operator `dagEdge2`, its truncated Neumann inverse `dagGreen2`, and the
    combined 18-conjunct synthesis with `blockLower` and `idempotentCompression`.
