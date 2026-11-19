# Yang–Mills Lane Unification Plan

Status: planning document; first compatibility obstruction is kernel-checked

Scope reviewed from the current checkout at `HEAD` `abd5826b3` with a dirty,
partly staged worktree. This document records the source-grounded unification
plan; it does not claim a fresh repository build or a continuum Yang–Mills
result.

Review basis: direct symbol searches across repo-owned `lean/` and `src/`
sources, followed by inspection of the named owner declarations, their relevant
imports, and selected in-repository consumers. This is a bounded source audit;
it does not establish absence outside the searched identifiers and inspected
dependency paths, nor does it certify the dirty tree by compilation.

## 1. Executive summary

The repository contains several related but distinct Yang–Mills lanes:

1. Peirce/two-sheet operator identities in associative rings;
2. matrix-valued exterior-algebra curvature and self-duality;
3. finite Zorn/Dirac/Higgs spectral-action identities;
4. a finite QFT/mass-gap scaffold with explicit witness hypotheses;
5. a concrete tensor-tower algebraic direct limit;
6. generic star-ring colimit-cone/channel constructions;
7. real doubled Hestenes–Krein analytic and algebraic-colimit lanes, with
   finite-stage transport; and
8. a separate `src/` cross-lane synthesis lane.

They should be related by **explicit carrier maps and compatibility theorems**,
not identified by vocabulary or collected into one large conjunction theorem.
The diagram below is a proposed dependency plan, not a theorem graph already
established by the repository. In particular, the spectral-action lane has not
been shown to consume the matrix/exterior curvature owner:

```text
Peirce data in B
    ├── [open map] ──> Matrix-valued exterior algebra
    │                       │ self-duality + Bianchi
    │                       ▼
    │                 Yang–Mills equation
    │
    └── finite spectral-action identities
                 │ explicit stage maps
                 ▼
          Algebraic direct limit
                 │ trace/order hypotheses
                 ▼
          Coercivity transfer
```

The direct-limit/coercivity branch and the finite Yang–Mills implication are
currently distinct results; the diagram does not assert that the first feeds
the second.

The finite QFT scaffold remains a separate conditional layer until an actual
map transports its state, positivity, and reconstruction data to a colimit.

## 2. Current source inventory

### 2.1 Canonical Peirce owner

`lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean`

Canonical operators:

```text
N₊ = conePlus P A
N₋ = coneMinus P C
Φ  = genPhi P A C
J  = genJ P A C
V  = genV P A C
Σ  = genSig P A C
D_P(X) = [P, X]
F_P = D_P(Φ) + Φ²
```

Existing scope includes:

- square-zero Peirce boundary components;
- `Φ² = V`, `J² = -V`, and `J Φ = Σ`;
- Peirce grading and covariant derivatives;
- Maurer–Cartan curvature decomposition;
- a Bianchi/self-dual Yang–Mills identity in an associative ring.

These are algebraic identities. `V` is an operator, not automatically a
positive scalar mass or a physical spectral gap.

### 2.2 Matrix/exterior-algebra Yang–Mills owners

- `lean/InfoGeometry/Canonical/YangMillsSelfDualInstantonBridge.lean`
- `lean/InfoGeometry/Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean`

Carrier:

```text
Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)
```

The carrier is a finite matrix over an exterior algebra, but the owner does not
encode a dimension-four manifold, a metric Hodge-star law, or an analytic gauge
field. The self-dual implication assumes `★ F = F` and `D_A F = 0`; the
anti-self-dual implication additionally uses `D_A (-F) = -D_A F`. Here `star`
is an arbitrary module endomorphism satisfying the displayed self-duality
hypothesis. The Peirce bridge relates `genV` to the even part of an algebraic
connection curvature under an explicit derivative compatibility condition;
it does not construct that compatibility for a nonzero differential.

### 2.3 Finite spectral-action owner

`lean/InfoGeometry/Algebra/NoncommutativeYangMillsHiggsSpectralAction.lean`

The current staged revision contains:

- `zorn_tetraktys_hilbert_schmidt_pythagoras`;
- `unified_yang_mills_higgs_dirac_spectral_action`;
- `bps_square_completion_and_bianchi_harmonicity`.

The carrier is a nested finite matrix construction over a ring `B`; the trace
identity is `B`-valued and no order structure is assumed. The BPS theorem is a
square-completion identity plus a conditional Jacobi/Bianchi consequence, not
an integrated positive monopole-energy theorem.

### 2.4 Finite QFT scaffold

- `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean`
- `lean/InfoGeometry/Canonical/YangMillsFiniteBridge.lean`

`FiniteYangMillsBridge` contains explicit fields for gauge rank, a finite model,
operators, a state vector, KMS-like/OS-like/Wightman-like hypotheses, and a
positive scalar `spectral_gap`. The construction
`ofExpectationSeedFromLogDet` derives a positive finite scalar from explicit
log-determinant coercivity while still requiring the other witness data.

This is a **conditional finite package**. It is not currently a theorem that
all Peirce or matrix-tower data satisfy these QFT fields.

### 2.5 Concrete tensor-tower direct limit

- `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`
- `lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean`
- `lean/InfoGeometry/Canonical/PeirceTetraktysColimitCoercivity.lean`

The stages are

```text
Stage n = MatStage n
        = Matrix (Idx n) (Idx n) ℝ
        ≃ Matrix (Fin (2^n)) (Fin (2^n)) ℝ
```

with `stageEmbed n` given by tensoring with the `2 × 2` identity. The algebraic
direct-limit carrier is:

```text
Limit := DirectLimitSuperClosure Stage stageBond
ofStage n : Stage n →+* Limit
```

The limit has a transported star operation and star-ring structure. This is an
algebraic direct limit. It must not be described as an analytic completion or
as a categorical colimit with a universal property unless that additional
construction is explicitly proved.

### 2.6 Generic star-ring colimit/channel owner

`lean/InfoGeometry/Canonical/TwoSheetedYangMillsInductiveColimit.lean`

defines:

```text
InductiveStarColimitCone
stepHom : A k →⋆+* A (k+1)
toColimit : A k →⋆+* A_inf
compat : toColimit (k+1) ∘ stepHom k = toColimit k
```

Its concrete tail tower is:

```text
TowerLevel R k = (Fin k → R) × R
TowerColimit R = ℕ → R
```

This channel tower is distinct from the `Cl11TensorTowerLimit.Limit`. No
identification between the two constructions currently exists.

### 2.7 Hestenes–Krein realification and analytic transport

The existing real doubled carrier is `DoubledSpace E := WithLp 2 (E × E)` (see
`lean/InfoGeometry/Krein/DoubledSpace.lean`). Its Hilbert product is positive,
while its Krein product is the signed form defined by the fundamental
symmetry `spectral_epsilon`:

```text
kreinInner u v = ⟪spectral_epsilon u, v⟫_ℝ
               = ⟪P₊u, P₊v⟫_ℝ - ⟪P₋u, P₋v⟫_ℝ.
```

The operator Krein adjoint is `J A† J` (`KreinSpace.kreinAdjoint` in
`lean/InfoGeometry/Krein/KreinSpace.lean`), where `J` is that fundamental
symmetry. `DoubleRealKreinProjectorPairing.kreinInner_eq_spectral_projector_difference`
proves the signed positive-sheet-minus-negative-sheet formula. In particular,
the positive product on the doubled carrier must not be substituted for its
signed Krein pairing. The finite Cl(1,1) GNS realification owner
(`lean/InfoGeometry/Canonical/Cl11GNSRealDoubledKreinBridge.lean`) explicitly
says that it does not identify its positive Hilbert–Schmidt product with the
indefinite Krein pairing. For a complex operator algebra represented in real
coordinates, entrywise complex conjugation/Dirac conjugation must be proved to
intertwine the chosen real fundamental symmetry; it is not automatic from
splitting coordinates into real and imaginary parts. The finite realification
owner constructs real coordinate readouts and left/right actions for the
finite Hilbert--Schmidt carrier, but explicitly retains the positive Hilbert
pairing as distinct from the indefinite Krein pairing. This is one owner, not
a second independent realification result.

The algebraic bilingual carrier
`lean/InfoGeometry/Physics/HestenesKreinBilingualCarrier.lean` is also only a
carrier-law owner: it gives commuting left `A` and right `Aᵐᵒᵖ` actions by
associativity and records opposite-word order, while explicitly claiming no
Hilbert-module completion or Morita equivalence. It therefore cannot by itself
supply the realification, Krein adjunction, DGA, or colimit data required by a
Yang--Mills bridge.

`FilteredPhaseCone` and `HestenesKreinCone` (in
`lean/InfoGeometry/Canonical/FilteredInductiveHestenesAnalyticity.lean` and
`lean/InfoGeometry/Canonical/FilteredHestenesKreinColimit.lean`) prove
phase/Cauchy analyticity for continuous-linear bonding and inclusion maps,
assuming the stage spaces, a
complete normed target, those maps, phase compatibility, and the cone equation
`ι (n+1) ∘ bond n = ι n` are already supplied. This is not a construction of a
categorical colimit or of an analytic completion. The separate
`HestenesKreinFilteredColimitBridge`
(`lean/InfoGeometry/Canonical/HestenesKreinFilteredColimitBridge.lean`) does
use Mathlib's actual `ModuleCat ℝ` colimit to descend compatible algebraic
endomorphisms, but proves no norm, completion, Krein-pairing, or analytic
universal property. Several complementary algebraic colimit results also
exist and should be reused rather than reconstructed under new names. The
`ModuleCat ℝ` bridges descend compatible Hestenes operators and bilateral
actions; the `RingCat` bridge descends regular left/right actions on an
algebraic filtered ring colimit; and `PeirceTwoSheetKreinColimitBridge`
descends a Peirce conjugation endomorphism and sheet exchange for real
algebras, including its `SheetMatrix` specialization. The
`TwoSheetKreinStageSystem` supplies a concrete constant-stage Peirce/Krein
spine. `FilteredDirectLimitOwner` supplies generic universal-property and
readback abstractions. These are genuine, complementary results on different
carriers and diagrams, not one already unified colimit. Their scopes do not
include a Yang--Mills exterior DGA/connection, a scalar-valued indefinite
Krein form on the colimit, a metric-compatible completion, or an analytic
colimit theorem. Algebraic endomorphism descent does not prove descent of a
bilinear pairing or of connection, curvature, differential, and Hodge data.

Keep the following constructions separate in all further claims: actual
`ModuleCat ℝ` and `RingCat` categorical colimits; the supplied
`InductiveStarColimitCone` (not a universal property by its name alone); the
complete normed cone assumed by `HestenesKreinCone`; and the algebraic
`Cl11TensorTowerLimit` direct-limit carrier. No equivalence among these
carriers is established by the cited owners.

The repo's “bilingual analyticity” has a precise existing meaning:
`BilingualAnalyticAt` in the canonical owner
`lean/InfoGeometry/Geometry/BilingualAnalyticity.lean` packages a
phase-linear real Fréchet derivative together with a
`CauchyHestenesCompatibility`; the latter is used to obtain the geometrically
calibrated closed-form / boundary-integral result. A similarly named `src/`
copy is an audit/promotion lane, not evidence of a distinct carrier theorem.
`ComplexOperatorBilingualAnalyticity` in
`lean/InfoGeometry/Canonical/ComplexOperatorBilingualAnalyticity.lean`
separately converts
`AnalyticAt ℂ` into phase-Cauchy data for complex normed operator targets and
proves closedness of its calibrated planar form. Neither result alone proves
analyticity of a Yang–Mills connection/curvature map on a colimit carrier.

## 3. Existing finite-to-colimit results

### 3.1 Transport of the two-sheeted operator system

Theorems:

- `stageEmbed_intertwines_two_sheeted_tetraktys`;
- `ofStage_intertwines_two_sheeted_tetraktys`;
- `ofStage_bond_two_sheeted_tetraktys`;
- `limit_two_sheeted_tetraktys_from_stage`.

They transport the operators `opBitGrading`, `opZig`, `opZag`, `opElectron`,
`opAxial`, `opQuadraticCoupling`, `opSpinDipole`, and `derivSqPhi` through the
stage maps and into `Limit`. Consequently, a stage idempotent gives the limit
identities

```text
N₊² = 0
N₋² = 0
Φ² = V
J² = -V
J Φ = Σ
```

along with the stated curvature double-commutator law.

### 3.2 Scale invariance under a generic colimit cone

`colimit_renormalization_scale_invariance` proves that compatible stage maps
preserve:

- `opQuadraticCoupling`;
- `opSpinDipole`;
- grading-star sandwiches;
- the negative adjoint-square/dissipator operator.

This is exact algebraic scale/representative invariance. It is not a
renormalization-group existence theorem.

### 3.3 Higgs/triplet transport

`colimit_connes_higgs_triad_lift` transports the finite algebraic relations:

```text
Φ² = V
J² = -V
Φ J = -Σ
J Φ = Σ
M(Φ) = 0
M(V) = 0
M(J) = -4 • (V J)
M(Σ) = -4 • (V Σ)
```

`colimit_higgs_mexican_hat_and_goldstone_lift` transports the additional
reflexive cross-sheet hypotheses when they are explicitly supplied.

`colimit_coherent_bec_higgs_vev_scaling` shows linear scaling of `Φ` and `J`,
quadratic scaling of `V`, `Σ`, and the mass operator, and corresponding limit
identities.

### 3.4 Channel orthogonality and decoupling

For the concrete `TowerColimit R = ℕ → R`, distinct channel supports are
orthogonal. `colimit_orthogonal_channel_higgs_decoupling` proves:

- additive `V` for two distinct channels;
- `V₁ V₂ = V₂ V₁ = 0`;
- decoupling of the double-commutator operator;
- additive axial/mass readouts.

This is a channelwise algebraic result, not a theorem about independent
physical particles or a tensor-factor separability interpretation.

### 3.5 Trace and coercivity transport

The tensor-tower owner proves normalized-trace invariance under one-step and
multi-step bonding maps. With an explicitly supplied trace extension

```text
tau : Limit →ₗ[ℝ] ℝ
htau : tau (ofStage n x) = normalizedTrace n x
```

it proves:

- the Peirce Hodge boundary/coboundary identity at `Limit`;
- transfer of an assumed uniform finite-stage quadratic inequality;
- finite off-corner energy contractivity;
- `unit_horizon_mass_stage_coercivity` with constant `2`;
- `peirce_tetraktys_unit_horizon_coercivity_descends` with the same constant;
- `seed_unit_horizon_mass_coercivity_descends`, deriving the cofinal hypotheses
  from one finite self-adjoint idempotent seed.

The source-lane theorem
`yang_mills_colimit_vortex_coercivity_descent` additionally packages a
constant-`8` vortex coercivity readout under explicit cofinal projection,
self-adjointness, trace, and unit-horizon assumptions. That theorem is in the
modified `src/` lane and must be promoted only after independent review and
validation.

### 3.6 BdG and conditional mass amplification

The tensor-tower owner also contains:

- `limit_peirceBdGHamiltonian_noncomm_sq_and_trace_positivity`;
- `limit_peirceBdGHamiltonian_mass_gap_amplification`.

The amplification theorem assumes a lower bound of the form

```text
m_gap ≤ tau (star X * genV P A (star A) * X)
```

and derives domination by the BdG-square energy. It does not construct `m_gap`
from the colimit alone.

### 3.7 Existing Hestenes–Krein and Peirce colimit transport

The colimit lane has more proved structure than a generic cone alone, but its
current results remain split across carriers. The `ModuleCat ℝ` owners
`HestenesKreinFilteredColimitBridge` and
`HestenesKreinBilingualFilteredColimitBridge` descend compatible endomorphisms
and commuting left/right actions and provide stage readbacks. The
`HestenesKreinBilingualColimitBridge` uses an actual filtered `RingCat`
colimit to descend the regular left and right actions. The
`PeirceTwoSheetKreinColimitBridge` descends the Peirce conjugation involution
and sheet exchange on a real-module colimit, with a `SheetMatrix`
specialization; `TwoSheetKreinStageSystem` supplies its finite constant-stage
counterpart. `FilteredDirectLimitOwner` provides generic universal-property
and uniqueness/readback infrastructure.

These results establish real algebraic colimit transport for the operations
in their statements. They do not yet produce one filtered Yang–Mills
connection DGA, a colimit-valued signed Krein pairing, a compatible Hodge
operator, or a normed/analytic completion. The next proof obligation is to
instantiate the appropriate existing colimit for the actual connection
diagram and prove descent of the missing operations; only if the required
structure is not preserved by that colimit should a richer categorical
construction be added.

## 4. Unification target

The intended relation map should be recorded as two branches from shared
Peirce/operator data, with a separate conditional bridge between them only if
its carrier map is constructed and proved:

```text
PeirceSpine / PeirceDefectBridge
        │ define Φ, J, V, Σ, D_P, F_P
        ├── [open connection construction]
        │       ▼
        │  Matrix exterior curvature
        │       │ Bianchi + self-duality
        │       ▼
        │  Yang–Mills equation
        │
        └── finite spectral-action identities
                    │ star-preserving stage maps
                    ▼
             tensor-tower Limit
                    ├── trace/coercivity transfer
                    ├── Higgs/tetraktys transfer
                    └── conditional BdG amplification
```

No arrow from the Yang–Mills equation to the spectral-action owner is asserted
by the inspected theorems. Establishing such an arrow requires an explicit
trace/curvature map and its hypotheses; shared Peirce notation is not enough.

The finite QFT scaffold should attach as a **separate conditional branch**:

```text
finite algebraic data + explicit state/positivity/reconstruction witnesses
        ▼
FiniteYangMillsBridge
```

A future theorem may connect this branch to `Limit`, but only after defining
and proving transport of the state, trace, positivity, and reconstruction
structures.

## 5. Required bridge theorem contracts

The source audit changes the priority of this section: several proposed
contracts below are already proved, while the remaining “connection bridge”
currently assumes its key compatibility equation. Do not create another
conjunction theorem or repeat a theorem under a new name. First distinguish
the closed implications from the missing construction.

### 5.1 Closed contracts: reuse, do not reimplement

**Self-dual curvature implies the Yang–Mills equation** is already provided by
`YangMillsSelfDualInstantonBridge.self_dual_solves_yang_mills`: from
`isSelfDualCurvature star F` and `covariantDerivative A d F = 0` it proves
`covariantDerivative A d (matrixHodgeStar star F) = 0`. The anti-self-dual
version is also present. This is an implication conditional on Bianchi; it
does not construct a connection satisfying either hypothesis.

**Peirce curvature identification under an explicit compatibility premise**
is already provided by
`SelfDualConnectionCurvatureYangMillsBridge.peirce_defect_connection_curvature_and_yang_mills_bridge`.
Its premise is exactly
`matrixExteriorDerivative d A_conn = peirceGradingDeriv P A_conn`; after that
premise, the curvature equality follows by unfolding the two definitions.
The `d = 0` specialization is also proved. These results close a conditional
algebraic identity, not the construction of a nontrivial differential
connection or a self-dual solution.

**Finite-stage compatibility and transport** are already proved for the
specific `Cl11TensorTowerLimit` tower, including
`stageEmbed_intertwines_two_sheeted_tetraktys`,
`ofStage_intertwines_two_sheeted_tetraktys`, and
`ofStage_bond_two_sheeted_tetraktys`. The direct-limit representative equation
is supplied by `directLimitOf_bondMap` and used throughout
`PeirceTetraktysColimitCoercivity`. A new generic version is justified only if
it proves additional naturality for an operation not covered by those results.

### 5.2 Actual missing bridge: construct compatible connection data

The remaining issue is not the substitution proof above. It is to construct
data for which its compatibility premise holds for mathematical reasons.
`matrixExteriorDerivative d` applies one coefficient endomorphism entrywise;
`peirceGradingDeriv P` is the matrix-level inner commutator `P X - X P`.
In the owner files and consumers inspected for this plan, no map or theorem
identifies these operations. This is a bounded source-search result, not a
claim that no such construction exists anywhere in the repository. Equality
on one chosen `A_conn` is a possible extra equation, but it does not follow
from `P * P = P`, and it is not a naturality theorem. A kernel-checked finite
witness now records the stronger carrier-level obstruction in
`PeirceToMatrixConnectionCarrierMap.no_universal_peirceExteriorDerivative_compatibility`:
for any coefficient endomorphism with `d 1 = 0`, entrywise differentiation and
`[E₀₀, ·]` cannot agree on every `2 × 2` matrix over an exterior algebra. This
rules out a universal substitution, but does not rule out a deliberately
constructed map or a compatibility equation on one selected connection.

The next theorem contract must therefore start with an explicit construction,
not take this equality as a hypothesis:

1. Specify the source differential graded algebra, its differential `d`,
   connection form, and the target representation/map. Keep the Peirce
   commutator as a separate operation unless a proved intertwining law relates
   it to `d`.
2. Prove the map preserves multiplication and the connection data, then prove
   the curvature comparison by expanding both curvatures. If the intended
   model instead uses the Peirce inner derivation as its differential, first
   check the differential laws before adopting that model. In fact, for
   idempotent `P`,
   `[P,[P,X]] = P X - 2 P X P + X P`; on `P = diag(1,0)` and `X = E₀₁` this
   equals `E₀₁`, so this commutator is not square-zero in general and cannot
   itself be used as a cochain differential. Canonical finite-operator owners
   prove the corresponding tripotency/cube law (`PeirceFrechetOperatorArchetypes.cutDerivation_cube_eq_self`
   and `LieJordan.peirce_lie_cube`), not nilpotency.
3. State whether the result is an ordinary matrix-valued exterior connection,
   a Peirce-algebra connection, or only a one-element identity. The last case
   is not a carrier-level soldering.
4. Only after constructing the connection data, apply the existing separate
   self-dual/Bianchi implication. A nontrivial solution claim also requires
   exhibiting the connection and proving its self-duality and Bianchi premises.

A deeper owner search found several genuine differential constructions, but no
replacement for this missing matrix-exterior compatibility map:

- `PeirceGradedSuperderivations.differentialPlus` and `differentialMinus` are
  graded square-zero maps built from the odd Peirce corners and an explicit
  parity involution; they are not `matrixExteriorDerivative d` on coefficient
  forms. Their definitions and square-zero proofs are in
  `lean/InfoGeometry/OperatorAlgebra/PeirceGradedSuperderivations.lean`.
- `PeirceSpine.CentralizerDifferential.centralizerDifferentialHom_comp_self`
  makes `superDerivPhi` square-zero only on the `genV`-centralizer subtype.
  This is a real restricted carrier, not a square-zero law for the ambient
  inner commutator or for the exterior-algebra coefficient differential; see
  `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CentralizerDifferential.lean`.
- `PeirceFrechetOperatorArchetypes.cutDerivation` is a continuous inner
  derivation and has the cube law; `PeirceProjectedConnection` supplies a
  projected connection and its curvature on a Peirce right ideal. Neither
  declares a map into `Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)` satisfying
  the compatibility premise above. The owners are
  `lean/InfoGeometry/Canonical/PeirceFrechetOperatorArchetypes.lean` and
  `lean/InfoGeometry/OperatorAlgebra/PeirceProjectedConnection.lean`.
- `Topology.PeirceDifferentialForm` and
  `Topology.PeirceBoundaryCochainComplex` provide genuine finite/de Rham and
  discrete square-zero differentials on chart/cochain carriers, respectively,
  but no representation of `genPhi` or `peirceGradingDeriv` into those carriers.
  Their owners are `lean/InfoGeometry/Topology/PeirceDifferentialForm.lean` and
  `lean/InfoGeometry/Topology/PeirceBoundaryCochainComplex.lean`.

Therefore these owners are candidate ingredients for the next construction
only; citing any one of them as the missing bridge would conflate carriers or
silently assume the required map.

This is the **first open mathematical gate**. If no differential-compatible
representation exists for the intended Peirce data, record the obstruction and
keep the Peirce Maurer–Cartan theorem and exterior Yang–Mills theorem as related
but separate results. Do not discharge the gap by adding the compatibility
equation to the theorem hypotheses and calling it a bridge.

A further conditional obstruction is now kernel-checked in
`PeirceGradedSuperderivations.squareZero_differential_not_Peirce_commutator_on_nonzero_odd`.
For any associative ring, a square-zero Leibniz differential `d` that kills an
idempotent `P` cannot satisfy `d X = P * X - X * P` for a nonzero element `X`
whose two diagonal Peirce corners vanish (`P * X * P = 0` and
`(1 - P) * X * (1 - P) = 0`). Indeed, differentiating the proposed equality
again gives `[P,[P,X]] = 0`, while the off-diagonal hypotheses and
`P * P = P` give `[P,[P,X]] = X`. This strengthens the matrix-unit
counterexample above for closed projections and Peirce-odd data. It does not
exclude a differential-compatible map when `d P ≠ 0`, nor does it construct
connection data in the exterior-algebra carrier. The next task remains to
choose the actual differential graded carrier and prove a nontrivial map with
the required compatibility, if such data exist.

The conditional obstruction is now also specialized and kernel-checked on the
actual carrier in
`PeirceToMatrixConnectionCarrierMap.closed_cut_compatibility_forces_genPhi_zero`.
Here `matrixExteriorDerivativeHom d` is the additive componentwise lift to
`Matrix (Fin n) (Fin n) (ExteriorAlgebra R V)`. If this lift is square-zero and
Leibniz, `d P = 0`, and its value on `genPhi P A C` equals the Peirce
commutator, then `genPhi P A C = 0`. Thus this proposed compatibility cannot
serve as the missing soldering for a nonzero connection with a closed cut. The
remaining immediate mathematical problem is to construct and verify a
nontrivial differential-compatible representation with `d P ≠ 0`, or to
specify a different total differential for which the Peirce connection is
compatible. Neither construction is currently proved. There is an additional
typing-level algebraic issue to preserve: `ExteriorGradedDerivationBridge`
encodes the graded Leibniz sign, whereas the current matrix specialization
assumes ordinary Leibniz for the componentwise map on the entire matrix ring.
That assumption has not been shown for an exterior differential and should not
be used as evidence that the obstruction has already been instantiated to the
de Rham carrier. The new abstract local obstruction
`squareZero_local_differential_not_Peirce_commutator_on_nonzero_odd` is intended
to reduce this mismatch: for an even cut and an odd connection it requires only
the two cut/connection product rules actually used in the proof. Its compiler
check passed in `PeirceGradedSuperderivations.lean`. The matrix/exterior
specialization `graded_closed_cut_local_compatibility_forces_genPhi_zero` also
passes the file check, taking the local product rules explicitly. More
substantively, `graded_exterior_closed_cut_compatibility_forces_genPhi_zero`
now derives those rules from `ExteriorDifferentialData`, degree-zero
homogeneity of `P`, and degree-one homogeneity of `genPhi P A C`. Thus for the
actual componentwise exterior differential, a closed idempotent cut and the
proposed commutator compatibility force `genPhi P A C = 0`; global ordinary
Leibniz on the matrix ring is not needed.

The immediate degree-typing obstruction is separately formalized by
`degree_shift_peirce_compatibility_forces_both_sides_zero`: if the componentwise
differential output is entrywise degree two and the Peirce commutator output is
entrywise degree one, equality forces both matrices to vanish. The proof uses
the exterior algebra's direct-sum grading, so this is a genuine carrier
separation result. It remains conditional for generic `ExteriorDifferentialData`,
which provides graded Leibniz and square-zero but does not state that `d` raises
homogeneous degree; the selected typed Maxwell carrier supplies that law in the
following result.

That degree-raising law is now derived from the existing typed Maxwell carrier
in `ZornMaxwellFormsDegreeBridge.typed_differential_raises_degree_one`: the
operator `d₁` lands in homogeneous degree two and `d₁_value` identifies its
value with the underlying differential. The matrix result
`typed_maxwell_peirce_compatibility_is_zero` then proves the full obstruction:
for an idempotent degree-zero cut `P`, degree-one `genPhi P A C`, and the
proposed equality with the Peirce commutator, `genPhi P A C = 0`. The proof
derives degree two on the differential side and degree one on the commutator
side using the exterior algebra grading; it does not assume `d P = 0`. Thus a
nonzero soldering cannot satisfy this equation on the selected typed Maxwell
carrier, even with a non-closed cut. The remaining option is to define a
different, explicitly typed total differential/compatibility equation (or a
different carrier) that actually transports the Peirce parity differential.
No such construction is currently proved.

The next source-side carrier step is now proved in
`PeirceSpine.CentralizerDifferential`: `centralizerOddLeft` and
`centralizerOddRight` define the even-subring actions on the odd centralizer.
`centralizerOdd_bimodule_laws` proves both units, both associative action laws,
and commutation of left and right actions; `centralizerOdd_actions_additive`
proves additivity in the algebra and module arguments. Thus the odd component
is an actual additive bimodule over the even algebra, and
`centralizerDifferential_even_leibniz` supplies the underlying derivation law.
The typed map `centralizerEvenBimoduleDeriv` and theorem
`centralizerEvenBimoduleDeriv_leibniz` strengthen this to the literal
bimodule-valued Leibniz equation, expressed using both actions. This completes
the source-side algebra/bimodule/derivation package. It still
does not create the selected representation into matrix-valued exterior forms,
or prove the differential-intertwining equation on a nonzero connection
generator; that remains the immediate geometric soldering problem.

The left action is also bundled as the explicit ring morphism
`centralizerOddLeftRepresentation : centralizerEvenSubring →+*
Module.End ℤ (centralizerParityOdd ...)`; its evaluation theorem identifies
the represented operator with left multiplication. This is a proved
representation of the even algebra on the odd carrier. It is not yet a
representation into `Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V)` and cannot
discharge the geometric soldering contract above.

The next carrier connection is now proved in
`PeirceSpine.UniversalNoncommutativeOneForms` and
`PeirceSpine.CentralizerDifferential`. For a ring `A`, the universal
first-order form carrier is the kernel of the multiplication map
`A ⊗[ℤ] A → A`, with `dᵤ(a) = 1 ⊗ a - a ⊗ 1`. Taking
`A = centralizerEvenSubring ...`, the actual left action and the
`centralizerEvenBimoduleDeriv` define the balanced pairing
`a ⊗ b ↦ a • d(b)`. Its restriction to the multiplication kernel gives
`centralizerUniversalFormEvaluation`, and
`centralizerUniversalFormEvaluation_differential` proves that evaluation of
`dᵤ(a)` recovers the Peirce derivation `d(a)`. This is a concrete soldering
between the existing Peirce derivation and the universal noncommutative
one-form carrier. It is source-specific; no claim is made that it induces a
map to the matrix/exterior connection carrier.

The universal calculus now has its generation and product laws explicitly
proved. `differential_mul` decomposes `dᵤ(a * b)` into the tensors representing
`a · dᵤ b` and `(dᵤ a) · b`; `tensor_normalForm_mem_span` and
`oneForms_mem_span` prove inside the kernel subtype that the forms
`a · dᵤ b` span the full multiplication kernel. Consequently,
`oneForms_addHom_ext` proves uniqueness: additive maps out of universal
one-forms agreeing on all `a · dᵤ b` are equal. The new
`centralizerUniversalFormEvaluation_product` states that evaluating this
universal differential on a product recovers the two actual Peirce bimodule
actions in the even-to-odd Leibniz rule. This completes the source-side
first-order factorization structure; its remaining limitation is still the
absence of a map from the odd Peirce bimodule to ordinary matrix-valued
exterior one-forms.

The generator-level evaluation is now explicit as well:
`centralizerUniversalFormEvaluation_leftDifferential` proves that evaluation
of `X · dᵤ(Y)` is exactly the left Peirce action `X · d(Y)`. Its proof uses
the universal tensor identity
`tensorAddHom_leftDifferentialTensor`; the correction term evaluates to zero
because `centralizerEvenBimoduleDeriv_one` proves `d(1) = 0`. Thus the map
from universal one-forms to the odd Peirce bimodule is identified on the
standard left generators, in addition to respecting differentials and the
product Leibniz split. This closes the source-side universal-form evaluation
gap. It does not construct a map from the odd Peirce carrier to the ordinary
matrix-valued exterior one-form carrier, so the geometric soldering problem
stated above remains open.

The earlier source-side extension was checked by the four commands below.
For the latest generator-evaluation addition, the universal-form target was
rebuilt first, then the centralizer file was checked. The centralizer check
initially found that its imported `.olean` predated the new universal lemma;
after the targeted dependency build, the owner check passed. The updated
centralizer owner build also passed, as recorded below.

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CentralizerDifferential.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential
```

The universal-form build completed in 1,045 jobs. The centralizer build
completed in 3,104 jobs and replayed dependencies with existing linter
warnings. These are targeted builds only.

Validation performed for this step:
`python3 tools/infra/run_locked_lean.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/UniversalNoncommutativeOneForms.lean`,
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms`,
`python3 tools/infra/run_locked_lean.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CentralizerDifferential.lean`, and
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceSpine.CentralizerDifferential`.
Both targeted owner builds completed successfully. The latter replay emitted
warnings in existing dependencies (`Supercharge`, `Core.PeirceDecomposition`,
`SteinbergBraidDefectSpine`, and `PeirceGradedSuperderivations`); no warning was
reported for either target owner. This is targeted validation, not a full
repository build or clean-warning claim.

The bounded owner search also found a genuinely degree-typed comparison lane
in `OperatorAlgebra.DerivationDifferentialForms`: its Chevalley--Eilenberg maps
have distinct types `A → C¹(K.L,A) → C²(K.L,A)`. This does not yet solder to
the Peirce source: `centralizerDifferentialHom` is an endomorphism of a
`genV`-centralizer subring and obeys a parity-twisted Leibniz rule, while the
CE differential is induced by a Lie action by ordinary derivations. The
missing construction is concrete: choose a Lie lane and coefficient
representation for which a map from the Peirce centralizer into the CE
zero-/one-form complex intertwines multiplication, parity, and differential.
No such action, map, or intertwining theorem was found in the bounded search of
the canonical and operator-algebra owners; this is a scoped search result, not
a repository-wide absence claim.

The Peirce source carrier now has one additional proved law in
`PeirceSpine.CentralizerDifferential.superDerivPhi_twisted_leibniz` (mirrored
in the `src/` lane):
`dΦ (X * Y) = dΦ X * Y + parityConj X * dΦ Y`. Together with the existing
square-zero restriction to the `genV` centralizer, this supplies the
source-side twisted Leibniz identity. It does **not** yet construct a
degree-resolved DGA, an exterior-form representation, or an intertwiner to
`matrixExteriorDerivative`; those remain open. The next concrete contract is
to construct a map from this parity-involutive differential carrier into the
selected form carrier and prove multiplication and differential compatibility.
The canonical owner now proves that `parityConj` preserves the `genV`
centralizer and that the restricted square-zero differential is odd under this
involution; its generic Peirce proof is
`PeirceGradedSuperderivations.differentialPhi_parity_odd`, with the centralizer
restriction in `PeirceSpine.CentralizerDifferential.centralizerDifferential_parity_odd`.
The existing `metricCentralizer` carrier is now a unital `Subring`, with
multiplicative closure supplied by `genV_centralizer_mul`; its canonical
subring inclusion is therefore an actual ring morphism into the ambient
operator algebra. The restricted differential is retained as an additive map
on the underlying subgroup and satisfies the actual
parity-twisted product rule in `centralizerDifferential_mul`. Together with
`centralizerDifferentialHom_comp_self`, these give a concrete associative
algebra carrier with an involution, an odd square-zero additive operator, and
its graded Leibniz law. This is the source-side Z/2 differential-algebra
structure; it is not a cohomologically graded DGA and is not a map to exterior
forms. The additive cohomology consumer now explicitly uses
`(metricCentralizer P A C).toAddSubgroup`, preserving its carrier while
enriching the operator algebra structure.

The source differential is now also typed on the parity eigensubgroups:
`centralizerParityEven` and `centralizerParityOdd`, with arrows
`centralizerDifferentialEvenToOdd` and `centralizerDifferentialOddToEven`.
`centralizerParityComplex_square_zero` proves both two-step composites vanish.
This gives an actual two-periodic complex on those subgroups without asserting
that every centralizer element splits into even and odd parts; such a direct
sum decomposition would need additional hypotheses in general characteristic.
The next source-side structure is now explicit in
`PeirceSpine.CentralizerDifferential.centralizerEvenSubring`: the parity-fixed
centralizer is a subring, and
`centralizerDifferential_even_leibniz` proves that the Peirce differential
restricts to an ordinary derivation on this even algebra with values in the odd
centralizer component. This identifies the precise degree-zero/degree-one
algebraic interface a geometric soldering must preserve. It is not yet a map
to `C¹` or to the matrix/exterior carrier.

The next soldering target must be specialized, not quantified over arbitrary
`B`: the existing form carrier is
`Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V)` with componentwise
`matrixExteriorDerivative`, while `centralizerDifferential` is an operator
commutator-derived map on a centralizer subtype. The owner
`PeirceToMatrixConnectionCarrierMap.no_universal_peirceExteriorDerivative_compatibility`
already refutes universal equality on that matrix/exterior carrier. Therefore
the next contract is a selected representation of the centralizer algebra into
the matrix/exterior connection carrier, together with a single explicit
intertwining equation on the chosen connection generator. The source-side
algebraic laws are now available, including the even-subring derivation law,
but no such nontrivial representation or compatibility has yet been
constructed. The previously proved obstruction still rules out using the
ambient Peirce commutator as a square-zero differential on closed off-diagonal
elements.

### 5.3 Hestenes–Krein and analytic-colimit gap ledger

This is the immediate extension path requested for the plan. It uses the
existing real doubled Krein, Hestenes phase, and colimit results as inputs and
does not replace the noncommutative matrix/exterior connection by scalar or
diagonal data. The rows are proposed theorem contracts, not results already
proved. Their dependencies form the following acyclic order:

```text
HK0 carrier and conjugation convention
  ├── HK1 finite-stage Krein/star/DGA-compatible bonds
  │     ├── HK2 finite-stage curvature and Bianchi transport
  │     └── HK3 finite-stage bilingual analyticity of the connection map
  └── HK4 select and instantiate the relevant colimit universal property
       (or construct a richer one if required)
HK1 + HK2 + HK4 ──> HK5 descend Krein/operator/connection/curvature data
HK3 + HK4 + HK5 ──> HK6 analytic limit theorem, only for a topological colimit
HK2 + self-duality + Bianchi ──> existing conditional YM implication
HK5 + trace positivity + uniform bounds ──> coercivity transfer contracts
```

The proposed identifiers below are planning labels, not declarations already
present in Lean. Fix their concrete signatures only after HK0 chooses the
carrier and conjugation convention:

| Contract | Proposed lemma/theorem target | Required conclusion |
|---|---|---|
| HK0 | `realification_preserves_kreinInner` | For a specified realification and Dirac operation, prove transport of the signed pairing and prove the induced adjoint agrees with `kreinAdjoint`; do not identify Dirac conjugation itself with `J` without a separate theorem. |
| HK1 | `stageBond_isKreinDGAHom` | Each bond preserves multiplication, unit, star, `J`, grading, signed pairing, and the differential. |
| HK2 | `stageBond_curvature` / `stageBianchi_transport` | Connection curvature and covariant Bianchi data agree after each bond. |
| HK3 | `stageConnection_bilingualAnalyticAt` | The real phase derivative and calibrated Hestenes compatibility hold for the actual stage connection map. |
| HK4 | `yangMillsDiagram_colimit` | Instantiate existing `ModuleCat ℝ`/`RingCat` universal-property owners for the selected diagram, or construct and verify a universal property in the richer category actually required (such as star-algebras or DGAs). |
| HK5 | `colimit_curvature_readback` / `colimit_kreinInner_readback` | Curvature and the Krein pairing are representative-independent and read back to every stage. |
| HK6 | `limitConnection_analyticAt` | Under stated convergence/completeness hypotheses, the limit connection has the compatible limit derivative. |
| HK7 | `limitSelfDual_connection_solves_YangMills` | The constructed limit curvature satisfies self-duality and Bianchi, then the existing implication applies. |

These names intentionally do not encode the hoped-for theorem as an axiom or a
structure field. In particular, HK0, HK1, and HK4 require constructions and
proofs, and HK7 is unavailable until their carrier-level consequences are
established.

**HK0 — Fix the real Krein carrier and adjunction.** Specify the stage carrier,
fundamental symmetry `J`, signed product `[x,y] = ⟪Jx,y⟫`, and induced Krein
adjoint `A♯ = J A† J`. For a doubled real carrier, reuse
`DoubledSpace`, `KreinSpace.kreinInner`, and `KreinSpace.kreinAdjoint`; record
the equivalent positive-sheet-minus-negative-sheet formula. Prove the
realification map from the chosen noncommutative operator/matrix carrier is
linear, injective where required, and transports the *specified* signed
pairing, star/conjugation, and operator action. Define the Dirac conjugation
operation and its induced adjoint explicitly; prove its relation to the
fundamental symmetry `J` rather than identifying the two by notation. A
complex-to-real coordinate split is not by itself a Krein isometry. Keep the Hilbert product as the auxiliary
positive topology and the Krein product as the signed geometric pairing.
For the existing doubled-space phase, the Hestenes clock is
`clockAxis = modular_j ∘ spectral_epsilon`; identify this with the intended
Dirac/complex structure by a proved intertwining theorem, rather than by
notation alone.

**HK1 — Build the finite-stage system in the actual Yang–Mills carrier.** For
each stage `n`, define the noncommutative operator algebra and its connection
module/DGA, with the same coefficient algebra, matrix size, grading, star, and
differential conventions as the matrix/exterior Yang–Mills owner. Define
continuous-linear bonds `bₙ` and prove:

- `bₙ (x * y) = bₙ x * bₙ y`, `bₙ 1 = 1`, and `bₙ (star x) = star (bₙ x)`;
- preservation of `J` / the Dirac-conjugation involution and
  `[bₙx,bₙy] = [x,y]` for the Krein form when the maps are asserted to be
  Krein isometries;
- grading and differential compatibility, including
  `dₙ₊₁ (bₙ x) = bₙ (dₙ x)`; and
- transport of the connection form, not just arbitrary algebra elements.

These must be genuine hypotheses proved for the chosen tower. Do not infer
Krein-isometry from star preservation, or DGA compatibility from a ring
homomorphism. Reuse the already proved star-ring naturality for Peirce
polynomials where its hypotheses apply.

**HK2 — Prove curvature and Bianchi are natural under those maps.** With the
chosen graded multiplication and differential, state curvature in the actual
connection carrier (for example `Fₙ = dₙ Aₙ + Aₙ ∧ Aₙ`, with signs fixed by
the owner convention). Prove `bₙ Fₙ = Fₙ₊₁` from HK1, then prove the covariant
differential transports and the Bianchi identity at each stage. Separately,
construct any proposed identification with Peirce curvature. The current
Peirce/exterior bridge assumes equality of `matrixExteriorDerivative d A_conn`
and `peirceGradingDeriv P A_conn`; HK2 must derive that equality from a
defined map and compatible differential, or explicitly leave the lanes
unidentified. Check the degree/type of both sides before attempting this:
an exterior differential changes form degree, whereas an inner commutator
does not automatically do so.

**HK3 — Prove bilingual analyticity for the connection and curvature maps at
finite stages.** Fix the phase operator on the realified parameter/tangent
space and the target phase induced by the Krein/Dirac convention, using the
existing `clockPhaseStructure` only after HK0 identifies its `clockAxis` with
the intended operator. For each
stage, establish an `AnalyticAt ℂ` theorem when the stage actually has a
complex normed structure, or directly provide `CauchyAnalyticAt` if the
available structure is only real phase-linear. Then construct the matching
`BilingualAnalyticAt` data by proving its `CauchyHestenesCompatibility` for the
calibrated geometric form; do not fill the compatibility field by assumption.
Prove the derivative chain rule for the connection-to-curvature map and its
compatibility with `bₙ`. Existing continuous-linear stage maps are already
Cauchy-analytic, and existing operator-orbit analyticity is reusable; the
missing target is the nonlinear connection/curvature construction and its
geometric calibration. A closed calibrated form does not imply a Yang–Mills
equation or a global integral theorem unless the corresponding backend and
hypotheses are supplied.

**HK4 — Select and instantiate the relevant colimit universal property.**
Existing generic categorical infrastructure means the first missing step is
to identify the actual Yang--Mills diagram and instantiate its universal
property, not to restate a generic colimit theorem. There are distinct
targets, and each theorem must choose one:

1. For a purely algebraic operator result, use the filtered `ModuleCat ℝ`
   colimit for the underlying real modules and prove that the Yang–Mills
   operations descend, or construct a colimit in an appropriate category of
   star-algebras/DGAs. Existing `HestenesKreinFilteredColimitBridge` and
   `HestenesKreinBilingualFilteredColimitBridge` descend compatible operators
   through a real-module colimit; `HestenesKreinBilingualColimitBridge`
   descends regular bilateral actions through an actual filtered `RingCat`
   colimit; and `PeirceTwoSheetKreinColimitBridge` descends the Peirce
   involution and sheet exchange on its real-module carrier. Instantiate the
   appropriate owner for the selected Yang--Mills diagram. None supplies the
   needed exterior-DGA or star-ring connection colimit.
2. For an analytic result, construct a complete real normed target and the
   compatible continuous-linear cone maps, prove a colimit/universal property
   in the selected normed category, and establish whether the topology is the
   intended inductive-limit topology. `HestenesKreinCone` assumes that target
   and maps; its compatibility lemmas alone do not prove the universal
   property, density, injectivity, or completion.

Do not call an arbitrary compatible cone a colimit. If the selected owner’s
universal property is not instantiated for the Yang--Mills diagram, state
only cone-level or stage-readback compatibility. The module, ring, and Peirce
colimits must not be silently identified with one another or with a normed
completion.

**HK5 — Descend the full operator geometry and Yang–Mills data.** Prove that
the quotient/colimit identifications respect `star`, Krein fundamental
symmetry and product, products/commutators, grading, differential, connection,
curvature, and Hodge operator. Derive stage readback and representative
independence for each operation. For a categorical colimit, use its actual
universal property; for an algebraic direct-limit quotient, prove the needed
equivalence relation is a congruence and the operations descend. The current
Peirce tensor-tower direct limit and generic two-sheeted star-ring cone are
different carriers; no identification with the Hestenes doubled cone is
asserted here.

**HK6 — State the analytic limit theorem at the level actually constructed.**
First prove stagewise analytic functions and derivatives are compatible with
the bonding maps, using a genuine `BilingualAnalyticAt` datum and the
Hestenes form calibration. Then prove the limit map is differentiable/analytic
and its derivative is the compatible limit of stage derivatives. Specify the
topology and convergence mode (locally uniform convergence of maps and
derivatives, or a direct universal property for continuous-linear maps) and
prove the required completeness and uniform estimates. Algebraic filtered
colimits carry no automatic analytic structure; finite-stage
`CauchyAnalyticAt` and a chosen complete cone are insufficient on their own.

**HK7 — Connect to the existing Yang–Mills implication and coercivity branch.**
After HK2/HK5 identify the actual curvature and covariant derivative, prove
self-duality and Bianchi for the constructed connection before invoking
`self_dual_solves_yang_mills`. Then, separately, define a scalar-valued trace
or state on the chosen target, prove positivity on the relevant operator
squares, prove finite-stage lower bounds with a uniform constant, and prove
that the selected colimit construction transports those bounds. A
`B`-valued trace identity or a Krein-signed square does not establish
order-theoretic positivity. The positive Hilbert norm and the indefinite
Krein form have different roles and neither can silently replace the other.

The finite partial results to reuse are therefore: Hestenes/Krein split
quaternion identities; compatible endomorphism transport through the genuine
module colimit; Cauchy analyticity of supplied continuous-linear bonds and
cone maps; stage readout invariance under supplied compatibility; and the
operator-valued complex analytic orbit/form results. The unresolved central
gap is the construction of a single Yang–Mills DGA/connection tower equipped
with the specified real Krein/Dirac conjugation, compatible analytic structure,
and a proved inductive-colimit target carrying those same structures.

### 5.4 Further transport contracts, only where coverage is missing

**Naturality audit.** Compare `genPhi`, `genJ`, `genV`, `genSig`, the Peirce
Maurer–Cartan curvature, and the Peirce covariant derivative against the
existing stage and colimit lemmas. Add only uncovered cases, with the exact
source and target maps in the theorem statement. Do not promise preservation
under an arbitrary star-ring homomorphism when the operation depends on extra
structure (for example, a differential, trace, order, or Hodge star) not
preserved by that homomorphism.

**Trace/coercivity audit.** Existing colimit inequalities are conditional.
Keep five separate obligations: (i) define a trace on the actual limit,
(ii) prove compatibility with finite normalized traces, (iii) prove positivity
of that trace on the relevant squares, (iv) establish the finite-stage lower
bound and its uniformity, and (v) prove the descent theorem applies to the
chosen cofinal family. An assumed linear extension alone does not establish
positivity or uniqueness of a trace extension.

**Finite QFT promotion boundary.** A bridge from `FiniteYangMillsBridge` to
`Limit` remains open and must explicitly construct or transport:

- a compatible family of finite states or functionals;
- preservation of each KMS-like and OS-like relation actually used;
- preservation of positivity and nonzero normalization;
- an extension of the state/trace to the target with proved properties;
- a reconstruction theorem on the target, if a limit QFT is claimed.

The constructor `FiniteYangMillsBridge.ofExpectationSeedFromLogDet` receives
`hJointKernel`, `hCommOrthogonal`, `hΩ_nonzero`, and `hΩ_posTime` as arguments.
It constructs the `FiniteYangMillsBridge` record and derives its positive gap
from `hCoercive`; it does not derive those state/QFT witnesses from log-det
coercivity. Until a transport theorem is supplied, classify this lane as a
conditional finite package and the colimit promotion as open.

## 6. Migration plan for the two source lanes

### Phase 0 — protect the baseline

The current worktree is heavily dirty and partly staged. Do not merge or
rewrite broad files during migration. First record exact source hashes and
separate:

- committed canonical owners under `lean/`;
- staged canonical changes;
- modified `src/` owners;
- generated/cache artifacts.

### Phase 1 — canonical vocabulary

Use `PeirceDefectBridge` and `PeirceSpine` as the single owner for `Φ`, `J`,
`V`, `Σ`, and the Peirce derivatives. Remove or avoid parallel definitions in
new work.

### Phase 2 — promote only unique `src/` results

Audit `src/InfoGeometry/Canonical/YangMillsLaneIsomorphisms.lean` and
`src/InfoGeometry/Synthesis/NoncommutativeYangMillsHiggsCausalPoset.lean`.
Promote unique, theorem-safe results into focused canonical owners. The current
`yang_mills_all_lanes_master_isomorphism_synthesis` should be treated as an
integration/audit theorem: its name suggests an isomorphism, but its type is a
conjunction of identities rather than a carrier equivalence. Rename only after
checking all consumers; until then, document the mismatch and do not cite it as
an isomorphism.

### Phase 3 — connect the spectral action

Make the finite spectral-action owner consume the canonical curvature bridge.
Do not make it redefine Peirce curvature or infer order-theoretic positivity
from a `B`-valued trace identity.

### Phase 4 — connect the tensor tower

Use `Cl11TensorTowerLimit` and `PeirceTetraktysColimitCoercivity` for the
concrete matrix tower. Keep `InductiveStarColimitCone`/`TowerColimit` as a
generic channel construction unless an explicit equivalence with the tensor
limit is proved.

### Phase 5 — isolate physical claims

Keep finite QFT, analytic completion, continuum PDE, and physical mass-gap
claims in separate modules with explicit `[bucket_2_conditional]` or
`[bucket_3_open_debt]` status.

## 7. Validation plan

Before validation, confirm that no compiler or Lake process is active and obey
the shared build lock. The following commands are planned, not reported as
already run for this document:

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/OperatorAlgebra/PeirceDefectBridge.lean

python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Canonical/SelfDualConnectionCurvatureYangMillsBridge.lean

python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Canonical/PeirceTetraktysColimitCoercivity.lean

python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.PeirceTetraktysColimitCoercivity

python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Algebra.NoncommutativeYangMillsHiggsSpectralAction
```

For the separate `src/` lane, use the source-lane build route only after the
canonical lane is stable. Validation must separately record:

- narrow Lean compilation;
- selected Lake build surface;
- warnings;
- placeholder scan;
- axiom dependencies;
- semantic-vacuity findings;
- whether the result is finite, conditional, algebraic-direct-limit, or
  categorical/analytic.

A green narrow build must not be reported as a whole-repository certificate.

### 7.1 Incremental validation record

The first open-gate result was checked independently with:

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Canonical/PeirceToMatrixConnectionCarrierMap.lean
```

This exited successfully. The only reported diagnostics were the existing
`LeanArchitect` local-change warning and a simplifier linter warning. No full
Lake build or whole-repository validation was run. The checked theorem is
`PeirceToMatrixConnectionCarrierMap.no_universal_peirceExteriorDerivative_compatibility`;
its scope is the impossibility of universal equality on the explicit `2 × 2`
carrier, not construction of the selected connection data still required by
HK2/HK7.

For this plan specifically, validation is not complete until the cited owner
names and theorem contracts are checked against the current checkout. Record
the revision used, command exit status, and warnings separately. A source hash
or successful compilation does not prove that a docstring's physical
interpretation or a proposed cross-carrier map is mathematically faithful.

### 7.2 Correctly typed compatibility on the canonical inclusion

The degree-zero-to-degree-one equation
`d_ext (f a) = g (d_P a)` was tested on the canonical inclusion in the concrete
`2 × 2` matrix/exterior carrier. It cannot provide a nontrivial soldering there:
for the constant cut `P = E₀₀`, the entrywise exterior differential kills `P`,
while `superDerivPhi P A C P` records the two Peirce off-diagonal connection
corners. The new owner theorem
`PeirceToMatrixConnectionCarrierMap.identity_representation_cut_compatibility_forces_genPhi_zero`
proves that compatibility on this single even generator forces
`genPhi P A C = 0`. This is a stronger obstruction than the previous
ill-typed comparison on `genPhi`: it applies to the correctly typed equation,
but only for the identity representation and this cut.

Incremental validation for that theorem on the current worktree:

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Canonical/PeirceToMatrixConnectionCarrierMap.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap
```

Both commands exited successfully. The file check reported the repository's
`LeanArchitect` local-change warning. The owner build completed successfully
after replaying dependencies and reported existing linter warnings in
dependencies and the existing `simpa` linter warning in this owner. This is a
targeted owner build, not a whole-repository build.

### 7.3 Moving-cut representation over the affine-line coefficient ring

The canonical-inclusion obstruction is bypassed by changing the coefficient
carrier and the cut together. The owner
`PeirceToMatrixConnectionCarrierMap` now defines the ring representation
`movingSheetRepHom : (ℝ × ℝ) →+* Matrix (Fin 2) (Fin 2) (Polynomial ℝ)` with

```text
f(a,b) = [[a, (b-a) X], [0,b]] = U diag(a,b) U⁻¹,
U = [[1,X],[0,1]].
```

Its first primitive idempotent is the moving cut
`P = f(1,0) = [[1,-X],[0,0]]`. With connection corner
`A = [[0,1],[0,0]]`, the owner proves, for every `(a,b)`,

```text
derivative (f(a,b)) = A * f(a,b) - f(a,b) * A
                     = superDerivPhi P A 0 (f(a,b)).
```

It separately proves `P * P = P` and `derivative P ≠ 0`. Thus this is an
actual nontrivial representation with a differential-intertwining theorem on
its entire two-sheet image; it does not assume compatibility as a field. This
is the algebraic soldering model that the constant canonical inclusion could
not provide.

The owner now packages the affine-line forms as the pair
`AffineLineMatrixForm = M₂(ℝ[X]) × M₂(ℝ[X])`, with the components interpreted
as coefficients of `1` and `dX`. Its product is
`(A₀,A₁)(B₀,B₁) = (A₀B₀, A₀B₁ + A₁B₀)`, so products of two `dX` terms vanish.
The owner proves associativity, a unit, additive laws, distributivity,
`d² = 0`, and the graded Leibniz rule using the degree involution
`(A₀,A₁) ↦ (A₀,-A₁)`. The representation embeds into degree zero;
`affineLineFormD_movingSheetRep` identifies its differential with the
degree-one image of `superDerivPhi`, and
`affineLineFormD_movingSheetRep_leibniz` proves compatibility with the
represented multiplication and induced one-form bimodule actions.

This closes the finite affine-line graded-carrier soldering into the explicit
coefficient extension
`AffineExteriorCoeff = Polynomial ℝ ⊗[ℝ] ExteriorAlgebra ℝ ℝ`. The map
`affinePairToExteriorCoeff` sends `(p,q)` to `p ⊗ 1 + q ⊗ dX`; it preserves
the affine-line product and intertwines the pair differential with the
polynomial-factor differential followed by multiplication by `dX`. Its
entrywise matrix lift preserves addition and multiplication and commutes with
the componentwise differential. The previously checked curvature expression
`dA + A*A` is transported by
`affineLineMatrixToExteriorCoeff_curvature`. A unit-preservation theorem has
now been added; it would complete the unital algebra-map laws once its pending
Lean check succeeds. The new theorem
`movingSheetRep_tensor_differential_eq_connection_commutator` states the
transport of the existing nonzero moving-sheet derivative/connection identity
into this matrix-valued tensor carrier. The follow-up
`movingSheetRep_tensor_differential_eq_target_bimodule_commutator` states its
stronger target-side formula using left and right multiplication by the
degree-zero connection image; its proof uses the map's additive inverse,
subtraction, and multiplication laws.
The tensor differential has also been given a square-zero proof by induction
over the full tensor carrier, together with its componentwise matrix lift.
These declarations and the moving-sheet commutator transports have passed the
locked file check and the targeted owner build.

This establishes a real lower-dimensional soldering, but its poset node must
not be conflated with the two-coordinate carrier. Write
`C₁ = Polynomial ℝ ⊗[ℝ] ExteriorAlgebra ℝ ℝ` and
`C₂ = MvPolynomial (Fin 2) ℝ ⊗[ℝ] ExteriorAlgebra ℝ (Fin 2 → ℝ)`. The source
map `affineLineMatrixToExteriorCoeff` lands in `C₁`; its source differential
is the one-variable derivative paired with the single form `dX`, whose square
is zero. The proposed nonzero-curvature construction instead lives in `C₂`,
where `dx * dy` can be nonzero. Thus the causal chain is
`AffineLineMatrixForm → C₁ → C₂ → (C₂, d₂, grading) → Bianchi on C₂`.
The owner `AffineExteriorTwoCoordinateSoldering.lean` defines the
`C₁ → C₂` algebra map and an explicit retraction `C₂ → C₁`. It proves the
coefficient map and its entrywise two-by-two matrix lift are injective, the
matrix lift preserves multiplication, and both coefficient and matrix maps
intertwine their componentwise differentials. The square-zero law for the
target matrix differential follows entrywise from
`polynomialExteriorDifferential_fin2_sq_zero`. The arbitrary matrix expression
`dA + A * A` is transported by an exact curvature equation. These statements
passed both the locked single-file check and targeted Lake build.

The transported affine-line one-form connection is still flat: its source
curvature vanishes and the soldering map carries that zero to `C₂`. Thus the
new map proves a genuine split differential-algebra embedding and curvature
compatibility, but does not provide the required nonzero two-coordinate
curvature witness. The next missing theorem is the graded Leibniz law for
`d₂` on homogeneous exterior components, followed by an explicit connection
in `C₂` with nonzero curvature and a Bianchi theorem on that same carrier.

The map is
`S = Algebra.TensorProduct.map α β`, where
`α : Polynomial ℝ →ₐ[ℝ] MvPolynomial (Fin 2) ℝ` sends the polynomial variable
to `MvPolynomial.X 0`, and `β` is `ExteriorAlgebra.map ℓ₀` for the linear map
`ℓ₀ r = Pi.single 0 r`. Its differential square must commute on every pure
tensor `p ⊗ a`:
`S (affineExteriorCoeffD (p ⊗ a)) =
  polynomialExteriorDifferential (S (p ⊗ a))`.
After expanding the two definitions, the coefficient obligations are
`pderiv 0 (α p) = α (Polynomial.derivative p)` and
`pderiv 1 (α p) = 0`; the exterior obligation is
`β (affineExteriorDX * a) = ι (Pi.single 0 1) * β a`.
The tensor-product induction principle then extends this equality from pure
tensors to all of `C₁`. This specifies the missing morphism theorem without
assuming that `S` is injective or that it maps the second coordinate form.

The remaining carrier gap is precise: this target is a polynomial/exterior
tensor product, while the existing curvature and Bianchi owners use
`ExteriorAlgebra R V` with an `R`-linear differential. There is no proved
algebra equivalence or DGA morphism from the tensor target to those owners, and
the tensor differential has not yet been packaged with their graded Bianchi
contract. The next theorem must either establish that carrier-level DGA
equivalence (including grading and differential compatibility), or generalize
the curvature/Bianchi interface to this tensor coefficient algebra and prove
its graded Leibniz and Bianchi laws. The present result transports a finite
affine-line curvature expression only; it does not establish Bianchi
transport, self-duality, a four-dimensional Yang–Mills field, or a continuum
result.

There is a sharper obstruction inside the affine-line model itself. The source
curvature theorem `affineLineConnection_one_form_curvature_vanishes` states
that every genuine one-form connection `A₁ dX` has zero curvature: the
differential vanishes on degree one and `(dX)∧(dX)=0`. This declaration has
been added to the owner but is still awaiting the locked Lean check. Therefore
the next mathematical step is not to force this one-generator carrier into a
nontrivial Yang–Mills curvature theorem. It is to construct a carrier with at
least two independent one-form generators, equip it with a square-zero graded
Leibniz differential, and exhibit a concrete connection whose curvature is
nonzero. The Bianchi interface must then be generalized to that enriched
carrier; a direct grading-preserving DGA map to the existing exterior carrier
cannot transport the polynomial coordinate differential.

The existing endpoint is source-identified: `GradedConnectionBianchiBridge`
consumes `ExteriorDifferentialData R V`, and
`ZornMaxwellFormsDegreeBridge.typedMaxwellExteriorDifferentialData` assembles
that package from `FormDifferentialLaplacianData` and
`TypedMaxwellOperators`. Those structures carry square-zero and graded
Leibniz laws as fields; they do not construct those laws from the affine tensor
carrier. A plain grading-preserving algebra map into the existing
`ExteriorAlgebra ℝ V` is not a viable soldering: polynomial zero-forms would
map to degree-zero scalars, and the ℝ-linear target differential kills those
scalars, so it cannot preserve `dX ≠ 0`. The viable next construction is to
enrich the Bianchi carrier itself with polynomial coefficients (and prove its
graded Leibniz and square-zero laws), or to prove Bianchi directly on a
multi-generator polynomial-form carrier. It must also exhibit nonzero
curvature; a map that only sends one-form generators into the one-generator
affine-line model cannot do so.

The minimal next carrier is already present and should be reused:
`InfoGeometry.Twistor.RealSupertwistor.SuperWave (Fin 2) (Fin 2 → ℝ)` is
definitionally `C₂ = MvPolynomial (Fin 2) ℝ ⊗[ℝ] ExteriorAlgebra ℝ (Fin 2 → ℝ)`.
Its owner `lean/InfoGeometry/Twistor/RealSupertwistorOperators.lean` constructs
the tensor algebra and proves the lifted boson/fermion actions and CAR/CCR
relations. The source now defines `polynomialExteriorDifferential` on this
carrier as
`d₂ = ∑ i, bosonLift (annihilate i) * fermionCreate (Pi.single i 1)` and states
its simple-tensor action in `polynomialExteriorDifferential_tmul`:
`d₂ (p ⊗ a) = ∑ i, pderiv i p ⊗ (ι (Pi.single i 1) * a)`. The component
identities needed for `d₂² = 0` are owned already:
`RealPolynomialCCR.annihilate_commute`,
`RealSupertwistor.boson_fermion_commute`,
`RealSupertwistor.fermionCreate_sq_zero`, and
`KahlerAtiyahCartanForms.wedgeOperator_anticommutator_zero`. They imply the
summands of `d₂` anticommute. The source now packages these steps in
`polynomialExteriorDifferentialTerm_anticommutes`,
`polynomialExteriorDifferentialTerm_sq_zero`, and the two-coordinate theorem
`polynomialExteriorDifferential_fin2_sq_zero`. These differential and
nonvanishing declarations passed the targeted owner build. The
graded Leibniz proof must use homogeneous degree in the exterior factor to move
each creation operator across a form. A constant matrix connection
`A = E₀₁*dx + E₁₀*dy` has the candidate curvature expression
`F = dA + A*A = (E₀₀ - E₁₁)*(dx*dy)`. Nonzero curvature requires proving
nonvanishing on the actual tensor carrier, not just on the exterior factor.
The source-grounded exterior-factor proof uses the already imported
`contraction_wedge_CAR`: contraction by the first coordinate covector sends
`dx * dy` to `dy`, and `ExteriorAlgebra.ι_eq_zero_iff` proves `dy ≠ 0`.
The candidate theorem `coordinateExteriorWedge_ne_zero` now records this
argument in `RealSupertwistorOperators.lean`, pending the owner check. The
source now also defines `polynomialExteriorAugmentation`, the tensor lift of
polynomial evaluation at zero and the identity on the exterior factor, and uses
it in the theorem `coordinateOneForm_mul_ne_zero`. This proves the needed
tensor nonvanishing. Finally read off the `(0,0)` entry of `F`.

For graded Leibniz, use a carrier grading predicate on `C₂` defined as the
`ℝ`-span of `p ⊗ a` with `a` in the existing degree-`k` exterior submodule.
The generator commutation needed in the simple-tensor calculation is exactly
the finite-word identity `ExteriorAlgebra.ι_mul_ιMulti_anticomm`; extend it
from exterior words to their span, prove graded Leibniz first for pairs of
simple tensors using `polynomialExteriorDifferential_tmul` and the polynomial
derivative Leibniz law, then extend in both variables using the tensor-product
spanning theorem. This defines an honest grading on the polynomial/exterior
carrier; it does not identify that carrier with the exterior-only owner.

The completed theorem contracts are: (1) square-zero for `d₂`; (2)
nonvanishing of the coordinate exterior wedge and its lift to the tensor
carrier; and (3) split-injective `C₁ → C₂` coefficient and matrix soldering
with differential and curvature transport. The remaining contracts are: (4)
instantiate the two-coordinate matrix connection and prove its curvature
equality and nonvanishing by entry readout; (5) prove graded Leibniz on
homogeneous exterior components and use it with square-zero for Bianchi on
this carrier. The two-coordinate matrix connection contract is now closed in
`AffineExteriorTwoCoordinateSoldering.lean`: its off-diagonal entries are the
actual polynomial/exterior one-forms `dx` and `dy`; its componentwise
differential vanishes; and its curvature is nonzero, detected in entry
`(0,0)` by `coordinateOneForm_mul_ne_zero`. This gives a finite
matrix-valued curvature witness on `C₂`, not a connection transported from
the moving Peirce owner. The remaining contracts are graded Leibniz on
homogeneous exterior components and its use with square-zero for Bianchi on
this carrier, plus Peirce-to-`C₂` representation transport. The
coefficient-side lemma `affinePlane_partial_derivatives_commute` has now been
added as an auxiliary fact. The source also contains the generic matrix
calculation `affinePlaneConnectionMatrix_sq` and the conditional implication
`affinePlaneConnectionMatrix_sq_ne_zero`. These are algebraic lemmas for
arbitrary coefficients `dx dy : B`; they do **not** instantiate the matrix
connection over `C₂`. The `SuperWave` carrier has two exterior generators,
their wedge is proved nonzero, and the differential and coefficient soldering
are kernel-checked. The concrete connection above is a carrier witness, not a
connection transported from the moving Peirce owner; that representation
soldering is a subsequent theorem.

The target's current differential contract makes this mismatch substantive:
`ExteriorDifferentialData.d` is a `Module.End R` and hence is `R`-linear. The
owner theorem
`linear_exterior_differential_kills_base_scalar` proves that any such
differential with `d 1 = 0` kills every `algebraMap R (ExteriorAlgebra R V) r`.
The companion theorem `no_scalar_polynomial_coordinate_chain_map` now proves
that a unital chain map cannot send `X` to such a scalar while intertwining
`Polynomial.derivative` with `d`.
Consequently taking `R = Polynomial ℝ` in that owner cannot realize the desired
`dX ↦ dX`; the polynomial coordinate is a base scalar and is forced to have
zero differential. The constant-linear tensor extension and affine-line
coefficient map now address this obstruction. Compatibility with the existing
exterior-only DGA owners remains open, as stated above; the affine-line model
should not be described as already soldered to those owners.

The moving-cut owner was validated incrementally on the current worktree with:

```bash
python3 tools/infra/run_locked_lean.py \
  lean/InfoGeometry/Canonical/PeirceToMatrixConnectionCarrierMap.lean
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock \
  InfoGeometry.Canonical.PeirceToMatrixConnectionCarrierMap
```

Both commands exited successfully for the moving-cut representation revision.
The file check reported the existing `LeanArchitect` local-change warning and
the owner’s existing `simpa` linter warning. The targeted owner build completed
successfully (8,995 jobs); replay also reported warnings in existing
dependencies. After the affine-line form carrier was added, the single-file
locked check and targeted owner build both passed (the owner build completed
with 8,995 jobs, including cached dependency replay); warnings were the
existing owner warning and simp warnings in the new distributivity proofs,
along with dependency warnings. The additional no-go lemma
`linear_exterior_differential_kills_base_scalar` then passed the locked
single-file check and the targeted owner build (8,995 jobs). For the current
tensor extension and curvature-transport increment, the locked single-file
command and explicit target build both exited successfully. The exact commands
were `python3 tools/infra/run_locked_lean.py
lean/InfoGeometry/Twistor/AffineExteriorTwoCoordinateSoldering.lean` and
`python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock
InfoGeometry.Twistor.AffineExteriorTwoCoordinateSoldering`. The file check
reported two unused-simp-argument warnings. The Lake build completed with
9,003 jobs, including dependency replay, and reported warnings in dependencies.
This is an explicit single-module build, not whole-repository coverage. The
new results do not close the graded Leibniz, nonzero-curvature connection,
same-carrier Bianchi, or Peirce-to-`C₂` representation-transport obligations.

## 8. Final truth boundary

The inspected owner declarations support these finite and conditional claims:

> Peirce/two-sheet operator identities hold in their stated associative-ring
> carriers; the matrix/exterior self-dual implication is conditional on the
> displayed self-duality and Bianchi equations; the finite spectral-action
> owner proves algebraic trace/square identities; and selected compatible
> operator identities and inequalities transport through explicit towers and
> the concrete algebraic tensor direct limit under their stated hypotheses.

This is a source-scope summary, not a fresh compiler or axiom-audit result.

It does **not** currently support the stronger statement that the continuum
four-dimensional quantum Yang–Mills theory exists, has a rigorously constructed
positive physical mass gap, or satisfies the full Clay/Wightman formulation.

Those claims remain `[bucket_3_open_debt]` until the missing analytic carriers,
state constructions, positivity theorems, and continuum maps are formalized.
