# Corrected Peirce/operator archetypes

## Contract

Replace the proposed `UnifiedGeometryOperatorSignificance` narrative, not the
existing owner definitions, with the following separate mathematical layers.
There is no universal five-pillar geometry theorem here. In particular, a
conjunction of identities does not construct maps between exceptional groups,
analytic operator algebras and differential geometry.

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
over ℤ. Recovering unscaled operators requires appropriate invertibility.
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
`ChargeExtractionBracketAudit` audits these corrected statements. This does not
identify the five sample operators with a full Kantor–Koecher–Tits algebra.

### Supported component projectors

`EndomorphismBlocks → BlockCharges → SupportedProjectors` bundles the five
support-defined components as native integer-linear endomorphisms of
`Module.End ℤ B`. For an idempotent P, they are mutually orthogonal idempotents,
sum to the identity, and uniquely recover a decomposition whose terms are fixed
by the corresponding projectors (`supportedProjector_unique`). This is a
characteristic-free support decomposition, not a claim that integer charge
eigenspaces are distinct in characteristics 2 or 3. It does not identify the
result with a Kantor–Koecher–Tits construction.
