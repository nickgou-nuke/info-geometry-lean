# Cross-Lane Closure Sequence

> Status: active, source-backed work queue
> Last reviewed: 2026-11-07
> Scope: currently inspected categorical, Peirce operator, native twistor, and QMS lanes.
> This is a bounded sequence, not an exhaustive inventory of every repository gap.

The purpose of this sequence is to connect existing owners with explicit typed maps and
compatibility theorems. A theorem that merely returns results from separate carriers in a
conjunction does not establish such a connection. Graph, ontology, and search results may
help locate candidates; Lean declarations and kernel checks determine what is proved.

## Ordering rule

Work from established interfaces toward cross-carrier consequences:

1. Preserve and expose bridges already proved between canonical owners.
2. Identify the smallest missing typed map for each actual cross-lane seam.
3. Prove operation and invariant compatibility for that map.
4. Derive consumer-level consequences only after those compatibility results exist.
5. Keep analytic, physical, or higher-categorical interpretations open unless their
   additional structures and hypotheses are formalized.

## Sequence

| Rank | Seam | Current source evidence | Missing target | State |
|---:|---|---|---|---|
| 0 | QMS implementation → artifact acceptance | Current Gate 1 requires an exact query, performs filename and Lean-source searches across current source roots and available `.lake/packages`, and reads the artifact/named owner files. A run against `PeirceGlobularityComparison.lean` recorded the command, one repository match, and zero dependency matches. Gate 2 now runs the placeholder audit and broad-import scan; it marks the scanner `heuristic-proxy` and explicitly leaves semantic controls for Gate 3. Current Gate 2 output reports `PASS` only for the static scan and `payload_ready`, not formal acceptance. | Supply an independent A-A audit report bound to artifact hash/task/scope and complete the semantic checks deferred by Gate 2. The runner does not authenticate agent identity; positive Gate 5 acceptance remains blocked without verified QA evidence. | False default Gate 1 search claims removed; Gate 2 default-true assertions removed; static-scan evidence recorded. Semantic review and positive artifact acceptance remain open. |
| 1 | Grothendieck elementary expansion → Peirce–Bruhat operator calculus | `OAI.Grothendieck.Model.elementary_pushout_retraction` gives `r` with `i ≫ r = 𝟙 X`. `linearizedModelMap` sends each model map to `Finsupp.lmapDomain ℤ ℤ` on cells; `linearizedModelMap_comp`/`_id` prove functoriality. `elementary_pushout_linearized_idempotent` constructs `p = linearized(i) ∘ linearized(r)` in `Module.End ℤ (Y.underlying.Cell n →₀ ℤ)` and proves `p.comp p = p` and that p fixes the image of the linearized inclusion. The corner square-zero and Bruhat orthogonal-partition applications are present and pass the locked Lean file check plus axiom audit. Their targeted Lake build fails while replaying imports: both `OAI@0.1.0` and `HomotopyHypothesis` provide distinct `OAI.CategoryTheory.Globular.Model` modules. | Resolve the duplicate OAI module provider in the dependency configuration, then rerun the owner Lake build and QMS. Separately supply independent A-A evidence for QMS acceptance. A compatible map to a distinct Peirce carrier, homotopy-invariant transport, and colimit consequences each require additional proofs. | Partial: direct file checking and axiom audit pass, but owner-build and QMS Gate 3 are not accepted. No cross-carrier map or homotopy/colimit transport is proved. The direct constant-carrier interpretation is refuted in `Mat₂(ℤ)`. |
| 2 | Coherator used for elementary expansion → topological realization coherator | In `GrothendieckElementaryExpansionPeirceCylinderPoset`, the expansion uses `C`, while the realization result assumes a separately supplied `C_top` and `hC_top`. `GrothendieckCoheratorRealizationBridge` defines `CoheratorTransport C₁ C₂`, `CoheratorTransport.toModelMap`, `theoryToOAI_of_transport`, `elementary_expansion_with_same_coherator_oai_realization`, and `coherator_transport_theoryToOAI_and_realization_bridge`, explicitly relating `C` and `C_top` and proving same-coherator / transported OAI realization equivalence (`weakEquivalence_modelToOAI_iff`). | Closed at explicit `CoheratorTransport` and same-coherator OAI realization scope in `GrothendieckCoheratorRealizationBridge.lean`. | Formal coherator transport and same-coherator realization bridge proved and checked via `run_locked_lean.py`. |
| 3 | Native twistor/Plücker coordinates → Zorn amplituhedron coordinate model | `Twistor.NativeTwistorAmplituhedronBridge` defines `Archetype.ofNative`, matches native Plücker coordinates and determinants, and transports the two-ray identity. `Archetypes.TwistorAmplituhedronZornBaryon.two_ray_scattering_square_ne_zero_iff_bracket_ne_zero` states the nondegeneracy condition without assuming every bracket is nonzero. | No coordinate bridge gap was identified in these inspected owners. Physical KLT/gravity/foam claims still require independent structures and are not consequences of these coordinate identities. | Formal coordinate seam closed at stated finite coordinate scope; stronger interpretation open. |
| 4 | Finite epistemic protocol fixed point → Peirce operator aporia | `MetaCompiler.DeclaredProtocol.compiled_protocol_fixed` proves the finite protocol schedule is a fixed point of the declared compiler. `MetaCompiler.scheduleConeExcursion` and `MetaCompiler.schedule_cone_excursion_compiler_fixed_point_and_peirce_aporia` define an explicit typed interpretation from `Fin 7 → RuleId` schedules into `[Ring B]` (`∑ r, scheduleConeContribution P X (s r)`) and prove that on the compiled fixed point `compileProtocol P = canonicalSchedule`, `scheduleConeExcursion P_cut X (compileProtocol P) = conePlus P_cut X * coneMinus P_cut X = P_cut * (X * X) * P_cut - (P_cut * X * P_cut)^2`. | Closed at finite schedule-evaluation and Peirce excursion scope in `MetaEpistemicCompiler.lean`. A converse from nonzero factors to nonzero product remains false in general rings with zero divisors. | Kernel-checked and Lake-built at the owner module scope (`MetaEpistemicCompiler.lean`). |

## Next repair contract (Rank 1 continuation)

The categorical retraction has a linearized-idempotent theorem. Follow-on theorems apply existing
Peirce corner and Bruhat partition results in that same endomorphism ring, and their direct Lean
check and axiom audit pass. The owner Lake build currently fails because two dependencies provide
distinct definitions of the same OAI module. Resolve that module-provider conflict without
changing pinned revisions, then rerun the owner build. After that, determine whether downstream
work needs a map to a distinct Peirce carrier and, if so, prove:

- the map on the actual cell-module operator carrier into the already-owned Peirce algebra;
- preservation of composition and identity (and any additional operations needed);
- the image of the categorical retraction projector under that map;
- the exact Peirce invariant justified by this image, without claiming homotopy or colimit
  consequences that have not been transported.

The existing `[Ring B]` Peirce identities cannot supply this map by themselves. The specific
constant-carrier interpretation assigning `globSource`/`globTarget` as OAI source/target is
false (see the finite counterexample in the table). If no canonical map exists, retain this
finite-stage bridge and the Peirce results as separate results rather than adding an assumed
identification.

## Evidence and limits

The current observations above are bounded to the named Grothendieck and twistor owners,
their declarations, and a repo-owned Lean search for the two master theorem names and the
candidate realization/operator names. They are not a repository-wide proof-debt census.
Before implementing Rank 1, rerun the documented deep search and inspect any newly found
candidate declarations and their consumers. The current finite twistor coordinate bridge
is positive evidence that owner-aligned adapters can be proved, but it does not establish
that the categorical/operator seam has an analogous canonical map.

## Language-statistics continuation

This continuation is bounded to the finite cyclic and finite attribute-group owners. It records
the next typed connections without treating their co-location in the language-statistics catalog
as a derivation.

| Order | Seam | Proved source / exact target | Remaining obligation |
|---:|---|---|---|
| L1 | Translation-kernel matrices → indirect-path kernel | `LanguageStatisticsTranslationSymmetry.relativeKernelMatrix_mul_eq_convolution` proves `(K_f K_g)_{ij} = (f ⋆ g)(j - i)` for finite additive groups, with `(f ⋆ g)(d) = ∑_u f(u) g(d-u)`. The owner build and its four blocking unified-gate checks pass. | Connect the resulting finite convolution to a specific empirical PMI or ablation construction only after that data/model is defined. |
| L2 | Seasonal Fourier × finite Walsh/V₄ modes → joint product mode | `cyclic_fourier_v4_walsh_product_eigenmode` defines left convolution on the repository's actual `V4Group`, proves its character eigenmode identity, and combines it with the `ZMod` Fourier mode in a Kronecker product. The same owner also proves `cyclic_fourier_arbitrary_walsh_product_eigenmode` for an arbitrary finite Boolean word dimension using `Omega.Word`. The independent A-A review, locked owner build, Gate 3 axiom/placeholder/style checks, and Gate 3 acceptance all pass at finite-stage scope. | Closed at finite-stage product-transform and convolution-multiplier scope in L3. |
| L3 | Product convolution → spectral coefficient | `cyclicV4ProductFourier`, `cyclicV4ProductFourierInv`, and `cyclicV4ProductConvolution` define the tensor transform, inverse transform, and product-group convolution on `ZMod N × V4Group`; `cyclicV4ProductFourierInv_transform` proves exact inversion, `cyclicV4ProductFourier_convolution` proves `ℱ(K ⋆ f)(k, c) = ℱ(K)(k, c) · ℱ(f)(k, c)`, and `cyclicV4ProductConvolution_eq_inv_mul` recovers `K ⋆ f` from pointwise spectral multiplication via `cyclicV4ProductFourierInv`. For arbitrary Boolean word dimension `d`, `cyclicWalshProductFourier` and `cyclicWalshProductConvolution` on `ZMod N × Omega.Word d` satisfy `cyclicWalshProductFourier_convolution`. | Closed at finite-stage algebraic scope for `ZMod N × V4Group` and `ZMod N × Omega.Word d`. |
| L4 | Binary probability model → PMI log factor | In `LanguageStatisticsCirculantBirkhoffYangianPeircePoset`, `binaryAttributePairProb`, `binaryAttributeMarginal`, and `binaryAttributeLikelihoodRatio` define the normalized symmetric binary-attribute pair distribution `P(x, y) = (1 + s x y) / 4`; `binary_attribute_probability_model_pmi_derivation` proves 4-state normalization (`∑_{x,y ∈ {-1,+1}} P(x,y) = 1`), strict positivity for `|s| < 1`, uniform marginals `P(x) = 1/2`, likelihood ratio `P(x,y)/(P(x)P(y)) = 1 + s x y`, and exact affine PMI decomposition `log(P(x,y)/(P(x)P(y))) = α + β(x y)`. `finite_binary_attribute_product_pmi_decomposition` extends this to `m`-attribute product distributions. | Closed at finite symmetric binary-attribute and product-attribute model scope. |
| L5 | Peirce excursion → translation-invariant month kernel | In `LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset`, `vocabTargetProjector` and `ablatedVocabCooccurrenceMatrix` define the partitioned target-plus-helper vocabulary carrier `Sum G G` with ablated target-target block `0` and translation-invariant off-diagonal helper blocks `relativeKernelMatrix f` and `relativeKernelMatrix g`; `partitioned_vocabulary_peirce_excursion_eq_convolution_kernel` proves `P² = P`, `P M P = 0`, `conePlus P M * coneMinus P M = P M² P = Matrix.fromBlocks (relativeKernelMatrix (finiteKernelConvolution f g)) 0 0 0`, and cyclic shift invariance `(P M² P)(Sum.inl (i + a), Sum.inl (j + a)) = finiteKernelConvolution f g (j - i)`. | Closed at finite partitioned-vocabulary carrier scope. |
| L6 | Representational/optimization claims | In `LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset`, `cyclic_fourier_gram_factorization_and_eigenvalue_difference` proves exact Gram matching for the named two-column real Fourier feature matrix and the associated zero Gram residual/gradient, an algebraic eigenvalue-difference identity for any two frequencies, and annihilation of the subtracted mode. `kmsTridiagonalLaplacian3_eigenvector_horseshoe` proves the concrete `3 × 3` open-chain tridiagonal Laplacian eigenvector equations (`Δ₃ v₀ = 0`, `Δ₃ v₁ = v₁`, `Δ₃ v₂ = 3 v₂`), Euclidean orthogonality (`v₁ ⬝ᵥ v₂ = 0`), strict endpoint opposition (`v₁ 0 * v₁ 2 < 0`), and symmetric folding (`v₂ 0 = v₂ 2`, `v₂ 1 = -2 v₂ 0`). | Closed for these finite Gram and `3 × 3` open-chain eigenvector horseshoe identities. Continuous training dynamics remain outside this finite algebraic scope. |
| L7 | Scalar characters → finite noncommutative matrix order | `FiniteCharacterMatrixOrder.lean` proves scalar-character commutator blindness, the conditional Chebyshev `T₂` identity, a faithful homomorphism `s3MatrixRep : S3Perm →* Matrix (Fin 2) (Fin 2) ℤ`, `four_traces_unique_of_two_mul_injective` (unique reconstruction from four traces when `2 • ·` is injective), `s3MatrixRep_commutant_iff_scalar` (trivial commutant `M = c • 1`, i.e., Schur irreducibility over `ℤ`), `three_smul_matrix_in_s3_span` (explicit `3 • M` Wedderburn matrix-unit span in `ℤ[S₃]`), `s3_reflections_as_peirce_corner_combinations`, and `s3_regular_character_orthogonality` (`1 + χ_sign(g) + 2 Tr(ρ₂(g)) = 6 δ_{g, id}`). | Closed at finite `S3Perm` representation, Schur commutant, `3 • M` matrix-span, Peirce corner decomposition, and regular character orthogonality scope in `FiniteCharacterMatrixOrder.lean`. |
| L8 | Finite residue arithmetic + Peirce identities + abstract compression → Galois/quotient/dihedral interpretation | `GaloisQuotientNonAbelianFourierPoset.lean` proves the 7-stage Galois–Quotient poset ($\mathfrak{GQ}_1 \prec \dots \prec \mathfrak{GQ}_7$) and `finite_group_averageMap_is_invariant_projection`. `GaloisQuotientDihedralL8ClosureBridge.lean` closes the cross-carrier obligations: (a) `cyclotomic12_galois_unit_action_and_zmod12_harmonic_orbits` connects `(ZMod 12)ˣ` action on `CyclotomicField 12 ℚ` (`TwelveFoldCyclotomicNative.cyclotomic12_gal_action_on_twelfth_root`) and the 6 `ZMod 12` harmonic orbits (`TwelveFoldGaloisCharacterSets.galoisPower`); (b) `cyclotomic12_orbit_trace_eq_ramanujan_moebius` proves the Galois orbit traces equal the integer Möbius Ramanujan sums `(ramanujanSum12 d x : R)` whenever `ζ^4 - ζ^2 + 1 = 0`; (c) `dihedral4PeirceMatrixRep : DihedralGroup 4 →* Matrix (Fin 2) (Fin 2) R` and `peirce_matrix_carrier_compatibility_and_dihedral_inversion` connect the dihedral group homomorphism with `invS`, `genPhi`, `genJ`, and `Rotor2D`; (d) `z2SubgroupAverageProjector_macro_micro_and_nonvanishing_variance` constructs `P_H = ½(I₂ + Φ₁)` in `Matrix (Fin 2) (Fin 2) K` (`2 * half = 1`), proving idempotence, the macro/micro premises for `peirceSwapPhi`/`peirceGradingS`, 2nd-order variance `(delta_u * delta_u) • P_H`, and strict nonvanishing when `delta_u * delta_u * half ≠ 0`. | Closed at finite-stage `CyclotomicField 12 ℚ`, `ZMod 12` Galois-orbit Ramanujan trace, `DihedralGroup 4 →* Matrix (Fin 2) (Fin 2) R`, and concrete `ℤ₂` subgroup-average projector scope in `GaloisQuotientNonAbelianFourierPoset.lean` and `GaloisQuotientDihedralL8ClosureBridge.lean`. |

L1 is implemented in `LanguageStatisticsTranslationSymmetry.lean`; L2, L3, L5, and L6 are implemented in `LanguageSymmetryCirculantToeplitzBirkhoffPeircePoset.lean`; L4 is implemented in `LanguageStatisticsCirculantBirkhoffYangianPeircePoset.lean`; L7 is implemented in `FiniteCharacterMatrixOrder.lean`; and L8 is implemented in `GaloisQuotientNonAbelianFourierPoset.lean` and `GaloisQuotientDihedralL8ClosureBridge.lean`.
