# Streams 1/3 claim-versus-theorem acceptance review

Task #16; reviewer `theorem_scope_review`; 2026-10-24.

## Verdict and evidence boundary

**Accept the precise algebraic statements; reject promotion to the advertised geometric/analytic/exceptional completion.** The current headers correctly narrow most historical names. The remaining principal-bundle, cotangent-bundle, curvature, KMS-modular-theory and E6/F4 rhetoric is not the type of either stream's theorem or registered claim.

This is source review, not a new compiler verdict. No build, compiler, test, gate, commit, dependency change, or existing-file edit was performed. The only new output is this report. `AGENTS.md`, the canonical pipeline, hive commandments, deep-search protocol, categorical map, and the relevant check-workflow guidance were consulted. The worktree was already extensively staged/dirty; nothing was reverted.

The parent receipt `docs/REFLEXIVE_FLOW_KLEIN_COMPLETION_VERIFICATION.md` reports a serialized umbrella build and 621-declaration/14-owner strict replay. I also **read** `/tmp/reflexive-unified-axioms-final2.log`: it records the two current stream hashes below, 193 and 155 clean declarations respectively, allowed-axiom checking, `STALE_OLEANS []`, and `SOURCE_DRIFT_AFTER []`. Current SHA-256 values match that historical log for both streams, JordanAssociatorRing, TracialCARDensity, ZornColorGL31Obstruction and the rational regression owner. This is matching prior evidence, not an independently rerun check or whole-repository certification. Companion `Audit.lean` files contain `#print axioms` commands, not an additional semantic proof or a fresh run receipt.

Earlier `docs/GRASSMANNIAN_CYCLOTOMIC_SCOPE_AUDIT.json` describes a historical snapshot with no orbit quotient. That particular absence observation is stale: the current stream has `unitOrbitQuotientEquiv`, and a separate, actively changing owner now has a native stabilizer quotient. Do not copy the earlier absence sentence into acceptance prose.

## Pinned carriers, imports and naming convention

Below `G.` means `InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability.`; `U.` means `InfoGeometry.Canonical.UnifiedGeometryOperatorSignificance.`. Declaration names below with those prefixes are fully qualified by this convention.

- Stream 1: associative unital `Ring A`; trace statements take an additive homomorphism `τ : A →+ G` into an additive commutative group and explicit cyclicity. Matrix realization is `Matrix (Fin 2) (Fin 2) ℤ`.
- Stream 3: associative `Ring A`; central scalar weights use `[CommRing R] [Algebra R A]`. Only the geometric-pair predicate and the master theorem need `[StarRing A]`. Jordan product is **unnormalized**, `xy + yx`; bracket is `xy - yx`.
- Both import `Mathlib`, `Meta/ArchetypePipeline`, `Meta/EpistemicCompilerChain`, and `Meta/MetaEpistemicCompiler`. Stream 1 also imports/reuses `Core/PeirceDecomposition.peirce_decomposition`; Stream 3 imports/reuses `Core/JordanAssociatorRing` and its `InfoGeometry.Core.JordanAssociator.symm_operator_commutator`.
- Actual consumers found include `Canonical/ReflexiveNilpotentFlows` (Stream 1), `Canonical/ReflexiveWeightedTrace` (Stream 3), `Canonical/IdempotentOrbitContracts` (via the flow owner), both audit modules, and `Canonical/All`. These are algebraic developments, not evidence that a node name changes its proposition.

## Stream 1: exact acceptance contract

| Claim area | Actual declarations and assumptions | Accepted scope / limit |
|---|---|---|
| Principal bundle / Grassmannian | `G.principal_bundle_grassmannian_orbit`, using idempotent `P₀`, `g_inv*g=1`, `k*k_inv=1`, and `k*P₀=P₀*k` | Conjunction of conjugated idempotency, right stabilizer invariance, and left covariance. The last identity only uses associativity and does not require `h_inv` to be an inverse. This theorem does not construct a principal bundle or local trivializations. |
| Actual unit orbit | `G.unitOrbitMap P g = g*P*g⁻¹`; `G.unitOrbitSetoid P = Setoid.ker (unitOrbitMap P)`; `G.unitOrbitQuotientEquiv` | Exact set-theoretic equivalence `Quotient (unitOrbitSetoid P) ≃ Set.range (unitOrbitMap P)`, obtained from `Setoid.quotientKerEquivRange`. The declaration is **not** named `unitOrbitQuotientEquivRange`. |
| Fibres/stabilizer | `G.unitOrbitMap_eq_self_iff`, `G.unitOrbitMap_fiber_iff`, `G.unitOrbitMap_idempotent` | Equal images iff the relative unit `h⁻¹*g` fixes `P`; fixing iff commuting with `P`. Only one conjugacy orbit is parameterized. `G.mat2Z_zero_orbit_not_all_idempotents` explicitly excludes all-idempotents surjectivity for the zero reference point. |
| Tangent/cotangent/normal labels | `G.normal_tangent_cotangent_bundle_split`, `G.normalBundlePart_eq_self_iff`, `G.normalBundlePart_idempotent` | Opposite square-zero Peirce corners, their sum with the diagonal part, grading signs, and diagonal mixed commutator. The diagonal projection fixes exactly the centralizer of `P`. No bundle duality or differential-geometric connection is in this type. |
| Coadjoint/curvature language | `G.trace_coadjoint_invariance`, `G.adjoint_coadjoint_cubic_law`, `G.matrix_trace_coadjoint_and_cubic_law` | Cyclic additive pairing cancellation, `ad_P³(X)=ad_P(X)`, and corner weights `0,-1,+1`. The trace may be zero/degenerate. No minimal-polynomial equality, coadjoint-orbit symplectic structure, or curvature tensor is supplied. |
| Cyclotomic laws | `G.cyclotomic_and_orientability_master` assumes `d²=B²=0`, `dBd=d`, `BdB=B` | With `Δ=dB+Bd`, `Γ=dB-Bd`, proves `Γ²=Δ`, `J₄²+Δ=0`, `J₄⁴=Δ`, `ω₃²+ω₃+Δ=0`, `ω₃³=Δ`, `η₆²-η₆+Δ=0`, `η₆³=-Δ`, `η₆⁶=Δ`. The constant is support identity, not automatically ambient `1`; no primitivity or exact order in arbitrary characteristic. |
| Phi2 | `G.phi2_active_residual`, `G.phi2_active_eq_zero_iff`, `G.mat2Z_involution_not_phi2` | `Γ+Δ=2 • (dB)`, hence Phi2 vanishes iff that right side is zero. `Γ²=Δ` is **t²−1**, not Phi2(t)=t+1. The integer matrix regression has `Γ²=1` but `Γ+1≠0`. |
| Orientability/reflection | `G.reflection_conjugates_grading`, `G.reflection_swaps_positive_support`, `G.reflection_swaps_generators`, `G.ambientReflectionUnit` | Support/grading sandwiches and an actual ambient involutive unit `d+B+(1−Δ)`. Neither Spin/Pin membership, star-adjoint partial isometry, nor topological orientability follows. |

The matrix witnesses are genuine noncommuting examples of the abstract ring equations, not substitutes for a geometric carrier. `G.matG_inverse_laws`, `G.matGUnit`, `G.matKUnit`, and `G.matKUnit_fixes_reference` now explicitly supply the actual two-sided units instead of relying on suggestive inverse names.

## Stream 3: exact acceptance contract

1. `U.kantorTripleDefect_eq_nilpotent_residual` proves the two factorizations `X−XDX = X(1−DX) = (1−XD)X`. There is no Drazin or nilpotency premise/conclusion. The historical identifier must not be read as nilpotency of the residual.
2. `U.cartanAnomaly_anticommutes_spectralInvolution` and `U.offDiag_reconstructs_from_cartanAnomaly` need only idempotency of `P_D`; `P_M` is arbitrary. They prove anticommutation and off-diagonal recovery. The definition docstring calling `P_M` an “orthogonal projection” is not a binder. In characteristic two anticommutation does not produce two separated sign eigenspaces.
3. `U.IsGeometricPeircePair d B` **assumes** square-zero, both reflexive-inverse equations, and self-adjointness of `dB` and `Bd`. It does not construct the pair from an arbitrary square-zero element and does not assert `B=star d`. `U.projPlus_idem`, `U.projMinus_idem`, `U.projHarmonic_idem`, `U.projHarmonic_orthog`, and `U.star_projHarmonic` supply an algebraic orthogonal projection decomposition under those assumptions. This is not a Hodge PDE/existence theorem.
4. `U.ehresmannCurvature = dB−Bd`, `U.hodgeLaplacian = dB+Bd`, and `U.kahlerStructure = d−B` are expressions. Their bracket and polynomial laws are genuine; the names do not introduce a connection, a Laplace operator on forms, or a Kähler manifold. `U.trialityOperator_quad_law` and `U.trialityOperator_cube` give support-relative Phi3/cubic equations, not exceptional triality.
5. `U.bruhat_triple_product`, `U.bruhatWeylReflection_mul_inv`, and the three `U.bruhatWeylReflection_conj_*` lemmas give a three-shear factorization, an inverse product, and support/generator exchange. The separate flow owner already has `InfoGeometry.Canonical.ReflexiveNilpotentFlows.weylUnit`, `inverse_mul_weyl`, and `weyl_fourth`; the expressions agree by unfolding. Do not propose a new two-sided-unit/fourth-power lemma as if absent. Order divides four, and a Klein relation does not imply a faithful deck representation.
6. `U.kmsModularWeight u v d B = u² • Bd + v² • dB`; `U.kmsModularWeight_intertwines_d` and `_B` prove cross-multiplied support balance for arbitrary commutative-ring scalars, including zero. No positivity, normalization, inverse density, state, real-time flow, or holomorphic strip occurs in these statements. Calling them analytic KMS modular theory overstates their type.
7. Correct order is retained throughout: `U.jordanAssociator_eq_double_lieBracket S T X` states `jordanAssociator T X S = lieBracket (lieBracket S T) X`. Its proof rewrites through `U.jordanProd_commutator_eq_associator` and directly reuses `InfoGeometry.Core.JordanAssociator.symm_operator_commutator`. The master theorem and `U.pillar4JordanCartanE6` carry the same corrected order. No E6/F4 carrier or isomorphism is part of this associative-envelope identity.
8. `U.five_pillar_geometry_operator_synthesis` packages those equations under the explicit geometric-pair assumption, together with arbitrary scalars and Jordan inputs. Several self-adjointness conclusions are direct projections of that assumption; the other algebraic consequences are proved. This is a conditional algebraic theorem, not proof of the assumptions' universal existence.

**Residual prose that still invites overreading:** Stream 3's `mat2Z_five_pillar_witness` docstring says “verification of all five pillars”, “Tits–Bruhat–Moufang inversion”, and “KMS modular intertwining”. Its seven conjuncts contain noncommutation, idempotency, anticommutation, the shear identity, one support exchange, and one integer-weight identity; there is no Jordan or full star-pair conjunct. Prefer “selected noncommutative matrix specializations of the algebraic identities.” Similarly Stream 1's `cyclotomic3Op`/`4Op`/`6Op` docstrings say “third/fourth/sixth-order”; read them as annihilating-polynomial/power-law labels, not exact order. Section titles such as “Breakthrough”, “Geometric–Operator Synthesis”, “Certified Archetype”, and historical node names should not override the explicit header disclaimers.

## What the TypedArchetype/compiler layer actually certifies

Read owners: `Meta/ArchetypePipeline`, `Meta/EpistemicCompilerChain`, `Meta/MetaEpistemicCompiler`, `Causal/ProofCarryingSchedule`, `Causal/FiniteDependencyCompiler`, and readiness/schedule definitions in `Causal/FiniteDependencySchedule`.

`TypedArchetype Input .proved` requires `evidence : ∀ x, claim x`; `TypedArchetype.discharge` simply extracts it. The type does not validate the interpretation of `name : Name`, `phase : Nat`, or the prose label; it does not itself rule out a vacuous claim. Here the inputs are inhabited and the registered equations are concrete, so `Unit` is not an empty-input vacuity.

`#register_archetype` rejects a `.proved` declaration using `sorryAx`, but only **warns** about other unapproved axioms. `#audit_archetype` computes/transitively collects axioms and logs `isSound`; it is a diagnostic command, not a theorem that the prose is true and not an unconditional hard-fail gate. The strict historical replay is separate evidence.

The ten exact registered claim scopes are:

| Registered declaration | Input and exact content summary |
|---|---|
| `G.arch1HomogeneousBundleOrbit` | Every integer-matrix unit: orbit idempotency and invariance under the fixed `matKUnit`; not the entire quotient/fibre theorem. |
| `G.arch2PeirceNilpotentTangentSplit` | Every integer matrix: decomposition and both corner squares zero. |
| `G.arch3AdjointCoadjointCubicLaw` | Every integer matrix: cubic adjoint and zero bracket on the normal part; **no trace functional occurs in this claim**, despite its “Tracial Coadjoint Pairing” docstring. |
| `G.arch4CyclotomicActiveSupport` | One fixed integer matrix pair: Phi3/Phi4/Phi6 equations with constant `1`. |
| `G.arch5DiracOrientabilityReversal` | One fixed pair: grading reversal and positive-support swap. |
| `U.pillar1NonNormalCalculus` | Every integer matrix pair: one defect factorization and anomaly anticommutation against fixed `matPD`. |
| `U.pillar2HodgeDiracKahler` | One fixed pair: partition of unity, one grading bracket, Phi4 support equation. |
| `U.pillar3BruhatKmsModular` | Every integer scalar pair: three-shear equation and only the `d` weighted-support equation. |
| `U.pillar4JordanCartanE6` | Every integer matrix triple: Jordan-operator commutator/associator equality and corrected double bracket; no exceptional structure. |
| `U.pillar5UnifiedSynthesis` | One fixed pair: noncommutation and one support-exchange equation; **not the entire `five_pillar_geometry_operator_synthesis` theorem**. |

Each stream defines a five-element inductive type, an explicit `prerequisites` table, and `a ≤ b` by subset inclusion of those tables. `ProofRules statement` is `∀ target, (∀ prerequisite, prerequisite < target → statement prerequisite) → statement target`. **Both `G.grassmannianArchetypeRules` and `U.unifiedPillarRules` begin `intro target _` and discard prerequisite evidence.** Each branch discharges an already-proved archetype independently. For example Stream 3's Jordan node requires no earlier Peirce theorem, while its declared poset orders that node after the Peirce node.

`G.grassmannian_cyclotomic_executable_certified_compilation` and `U.unified_five_pillar_executable_certified_compilation` prove the executable list compiler succeeds, produces a valid duplicate-free complete five-node schedule with the stated pairwise order property, and all **selected statement-map propositions** hold. The generic compiler chooses ready nodes from a supplied finite order; it does not inspect Lean declaration bodies or infer dependency edges. Thus “valid schedule for a manually declared poset plus supplied proofs” is accurate. “Compiler extracted/certified the actual causal dependency DAG of these mathematical breakthroughs” is not established. `UnifiedPillarArchetype.branches_incomparable` is a decidable fact about the table, not proof-theoretic independence.

## Reuse discovered beyond the two stream files

These observations prevent false absence/novelty claims; they do not broaden the two stream theorems.

- `Canonical/IdempotentOrbitContracts.lean` now defines a local conjugation action, `InfoGeometry.Canonical.IdempotentOrbitContracts.quotientEquivOrbit : (Aˣ ⧸ MulAction.stabilizer Aˣ p) ≃ MulAction.orbit Aˣ p`, `stabilizer_iff_commute`, and `orbit_eq_existing_range`. It also has `tangent_split`, `tangent_horizontal_lift` (the explicit lift is `vp−pv`), `generator_ambiguity`, `completeCornerUnit`, and `cyclotomic_pair_recovers_transvection`. This source changed during review; its snapshot hash is below. It is outside the matching 14-owner replay receipt, so its fresh verification belongs to the parent, not this report. It still explicitly disclaims a topological principal bundle.
- `Core/PeirceMatrixPerfectPairing.lean` already constructs native range submodules, `InfoGeometry.Core.PeirceDecomposition.oppositeCornerTracePairing_isPerfPair`, `oppositeCornerTraceDualEquiv`, and `existsUnique_trace_representative` for finite full matrices over a field and an idempotent. Hence “no opposite-corner duality anywhere” would be wrong. This is finite algebraic duality, not a global cotangent-bundle construction.
- `SuperGrassmannian/GraphIdempotentDirections.lean` has `InfoGeometry.SuperGrassmannian.GraphIdempotentDirections.idempotentDirectionsEquiv` between `Hom(M,N) × Hom(N,M)` and first-order idempotent directions. `graphProjector_difference` and `range_complementProjector` distinguish image-moving directions from complement-moving directions. Thus identifying the whole idempotent-orbit tangent with a single Grassmannian graph direction is an additional error, not repaired by naming the other corner “cotangent”.
- `Canonical/ReflexiveWeightedTrace.lean` already proves `InfoGeometry.Canonical.ReflexiveNilpotentFlows.cyclic_weighted_balance`, `cyclic_support_balance_d`, and `cyclic_support_balance_B`; it explicitly consumes Stream 3's intertwining lemmas. The obvious next trace-readout lemma is not missing.
- `OperatorAlgebra/TracialCARDensity.lean` constructs the actual linear functional `InfoGeometry.OperatorAlgebra.TracialCARDensity.weighted`, and proves `divisionFreeKMS`, `density_divisionFreeKMS`, `eigenproductKMS`, `annihilatorKMS`, `creatorKMS`, and `joint_covariance`. Those are algebraic cyclic boundary laws, not assumed positive normalized GNS states.
- The repository also has genuinely further carrier constructions: I read `Canonical/FiniteSeedRepresentedKMS.lean`, including `InfoGeometry.Canonical.FiniteSeedRepresentedKMS.finiteSeed_representedVacuumTwistedCyclic`. It transports a finite Hermitian Gibbs seed through actual algebraic direct limits and the represented C-star closure, using previously constructed compatible states and dense readback. Its own header correctly disclaims an analytic KMS-strip theorem. It is not a consequence included in the Stream 3 schedule. No blanket absence of global states, represented closures, modular developments, or categorical infrastructure is asserted here.
- `Canonical/TensorTowerColimit.lean` was read: `psi_comp_iota_seq` proves compatibility from the given cone equation; `protected_states_survive_colimit` is nonvanishing transport under a kernel-lifting hypothesis. These existing transport owners must be reused at their exact types. Neither file names nor the infrastructure map justify upgrading this particular theorem to a universal-property theorem.
- Exceptional-owner search found independent Albert/Freudenthal/G2 developments. The inspected `Exceptional/AlbertDerivationsF4.lean` contains an actual abstract `bracket_is_derivation` theorem, while its named dimension split is arithmetic on defined natural numbers, not a `finrank` identification. This bounded observation does not dismiss the other exceptional owners or claim repository-wide absence of exceptional constructions. They are not the carrier of `U.pillar4JordanCartanE6`.

## Existing obstructions: do not reprove or overgeneralize

- `InfoGeometry.Canonical.ReflexiveKleinKernelRegression.reversed_jordan_bracket_false` and `local_jordan_associator_nonzero` already give rational matrix counterexamples. The latter has unnormalized value `−2d≠0` even for the square-zero reflexive pair. `InfoGeometry.Core.JordanAssociator.symm_associator_square_zero_inner_inverse` proves the general `−2d` formula using only `d²=0` and `dbd=d`.
- `InfoGeometry.Core.JordanAssociator.symm_operator_reversed_bracket_iff` already characterizes exactly when the wrong sign happens to agree: `Commute (2 • (s*t−t*s)) x`. Do not duplicate a proposed sign-criterion lemma.
- The exact qualified obstruction head is **`InfoGeometry.Algebra.ZornColorOperatorCoordinates.not_faithful_gl31_with_CAR_odd`**, owned by `Algebra/ZornColorGL31Obstruction.lean` (the filename is not its namespace). Over a nontrivial commutative ring, an R-linear map from native `SuperMatrix 3 1 R` into native Zorn `Op R`, sending the entire odd component into the specified raw CAR `oddPart` and preserving homogeneous brackets, is not injective. It does not exclude other odd images or all gl(3|1) representations. Proof uses `gl31_odd_bracket_noncentral` against central CAR odd brackets.
- `InfoGeometry.Canonical.ReflexiveNilpotentFlows.reflexiveKleinRep_nontrivial_kernel` and `reflexiveKleinRep_not_injective` exhibit the nontrivial fourth power of the presented glide in the kernel for every scalar unit. Grading reversal or a Klein relation cannot be promoted to faithful deck geometry.

## Smallest next step and real blockers

**No new mathematical lemma is justified as missing by this review.** All tempting small steps inspected—stabilizer quotient, formal tangent lift, opposite-corner trace duality, weighted cyclic readout, ambient Weyl unit/fourth power, Jordan sign correction and nonzero local associator—already have owner declarations. Do not dispatch duplicate implementations.

The smallest useful acceptance repair is prose/scope alignment, not a new theorem: replace “all five pillars certified” with “the five displayed finite claim-map propositions and a schedule for the declared poset”, and preserve the current explicit algebraic disclaimers. If actual declaration-dependency certification is required, the missing item in **these two schedule contracts** is a map from nodes to relevant declarations plus a checked relation between the chosen edges and real proof dependencies; the present `ProofRules` cannot furnish that interpretation. This is an explicit local contract gap, not a repository-wide claim that DAG infrastructure is absent.

There is no newly demonstrated algebraic blocker to accepting the two pinned stream owners. The blockers to the stronger user narrative are semantic and sometimes concrete refutations: Phi2 confusion, reversed Jordan sign, vanishing-all-local-associators, raw-CAR faithful gl(3|1), and faithful Klein representation cannot be accepted. Principal-bundle local triviality, differential-geometric tangent/cotangent and curvature identifications, analytic modular theory, and exceptional Lie-algebra identification require their own precisely typed carriers/maps and evidence, not another conjunction wrapper.

### Truthful replacement acceptance summary

> Streams 1 and 3 establish associative-ring conjugation and Peirce identities, support-relative Phi3/Phi4/Phi6 laws (with Phi2 explicitly distinguished), noncommuting matrix realizations, conditional star-support decomposition, three-shear support exchange, algebraic weighted-support balance, and the correctly ordered Jordan-operator identity. Their finite compiler theorems certify a complete valid schedule for declared five-node partial orders and the explicitly selected matrix claims. They do not by themselves establish principal bundles, global tangent/cotangent geometry, connection curvature, analytic KMS/Tomita theory, or E6/F4 closure. Existing independent quotient, duality, colimit/state and obstruction owners are retained and reused at their exact scopes.

## Snapshot hashes

Observed HEAD: `d716c2504a4cf21015982248a0860644904239ec`. Paths below are relative to `lean/InfoGeometry/`; hashes are SHA-256 of worktree bytes, not claims about committed provenance. The actively changing `IdempotentOrbitContracts` is explicitly a point-in-time observation.

```text
5b1cf7001141e56805777d1feac9b9e034f6dc3e14809f9bea40478891548fca  Canonical/GrassmannianBundleCyclotomicOrientability.lean
ff632db5c4c77a2a1dfb66b6ff08f681e8a628e29aa7bfe9d8d86ee36eadf112  Canonical/GrassmannianBundleCyclotomicOrientabilityAudit.lean
7a0c76b7d2ea4f4c2ba503ff994933e63653486432098775861426c84fcb0d2b  Canonical/UnifiedGeometryOperatorSignificance.lean
7b11854fd71be247fb2d6657ae573d8faac31a30a20e57ebbc86d33de628177e  Canonical/UnifiedGeometryOperatorSignificanceAudit.lean
474909c504e7501e5b55c85c19fa0481a8f92cf87ea3f79d180a08e5377c743d  Canonical/ReflexiveKleinKernelRegression.lean
342ecc89d74e977ccf6d4ae6b4ccd1ed8c94e20e1f30762723a14d250ebbfad7  Canonical/IdempotentOrbitContracts.lean
baa2447391902c9f1702c3f03faad43b14ed5d3602c99294b8763311ea022563  Canonical/ReflexiveWeightedTrace.lean
a464813d8111a734e7c8e5729af69492d7db63051cd15fef530aaa45edb33ec6  Canonical/FiniteSeedRepresentedKMS.lean
0ef61b4bcb868ad97ed6d6d832fae3de88e0d4d7b9f32e81fc69816e9f2ab813  Core/PeirceDecomposition.lean
9c0796e7eb84e684769a7fa658bf1c1faf90ea199e7bcfba28c4ab70e62d6f62  Core/PeirceMatrixPerfectPairing.lean
10e0b1f9b942ab7cbb56f2fdf602cbeb56db9cd15eeec53e03bac6e2912c66c3  Core/JordanAssociatorRing.lean
9fa4bc5abdfa1462a5b03401c1c0dba774eb951340ee88ef168accfb4d13d5ad  Meta/ArchetypePipeline.lean
14e6f94ec573acf8cea7d9d848dca9013c39f56137d15a6a12a0f955a313951b  Meta/EpistemicCompilerChain.lean
6c2c97082d40c2bbab489dd9703cbe7cc3271c216d2d4c68b8a463bb06cb9269  Meta/MetaEpistemicCompiler.lean
437ebb28df5f21c9322cd16e7d87db8ee2fc20b2a18631434cec85c271708892  Causal/ProofCarryingSchedule.lean
e6c3318f628469f9ca05f2be80a10d867a3f41b813c1ce8cf59ec5a0b2c4cebb  Causal/FiniteDependencyCompiler.lean
99f53bb0b3799116bb1e20e96787a561bb33f32d8c695eda0434945e32e25908  Causal/FiniteDependencySchedule.lean
6734a0e8dfeca118bfded0a477c4bc85873bee401db8ab1e3a70c3b31124af16  OperatorAlgebra/TracialCARDensity.lean
1ff76078bfb2300d589f5e0cdf1804de98ab49dc7407f3488454ae34523e3ed1  Algebra/ZornColorGL31Obstruction.lean
```

Search/evidence scope: repo-owned Lean symbol/import/consumer and related-carrier searches; complete reading of both stream owners, companions, directly reused Peirce/Jordan/meta owners and the named bounded related owners. External mirrors and graph exports were not used as proof evidence. No repository-wide absence claim or new verification result is made.
