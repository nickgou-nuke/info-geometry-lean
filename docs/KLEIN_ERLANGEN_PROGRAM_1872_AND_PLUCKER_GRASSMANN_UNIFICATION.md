# Felix Klein's *Erlangen Program* (1872) & Plücker–Grassmann–Klein Triadic Unification — Epistemic Compilation Ledger

## 1. Scope & Authoritative Lean Modules

This ledger records the kernel-checked Lean 4 formalizations uniting Hermann Grassmann's 1862 *Ausdehnungslehre* endmatter & 1877 *Mechanik*, Felix Klein's 1872 *Erlangen Program* (`0807.3161v1`), 1884 *Icosahedron / Quintic / Modular `j`*, and 1893 *Evanston Colloquium* (`ICM1893.2.ocr.pdf`), Julius Plücker's 1868/1869 *Neue Geometrie*, W. K. Clifford's 1878 *Extensive Algebra*, the Möbius geometry & Kůrka iterative-system suite (`moebius (2).pdf`, `2009_59.pdf`, `cpearlso.pdf`, `outline_term2_5.pdf`), and all four repository gap closures (`Gap 1`–`Gap 4`) against native Mathlib (`propext`, `Classical.choice`, `Quot.sound` only; zero `sorry`, `admit`, `axiom`, or `native_decide`).

### 1.1 Nine Verified Modules Covered by This Ledger

| Module | Lines | Bytes | Compiled Decls (`axiom_index`) | Public / Private Top-Level | SHA-256 |
|---|---:|---:|---:|---|---|
| [GrassmannSubspaceShadowsResultantAndHadamard.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/GrassmannSubspaceShadowsResultantAndHadamard.lean) | 2516 | 142154 | 98 | 28 / 13 | `9a214f89b12d734282314011b2cd5e99827728a7f784992540f04df8fd9f8454` |
| [KleinErlangenProgramGroupsAndProjectiveTransfer.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/KleinErlangenProgramGroupsAndProjectiveTransfer.lean) | 1237 | 63054 | 168 | 55 / 8 | `ac4488bdbdab9a1565597df5c3a144ea9c598011d9eec1fd9cbadcb9a96d2b2b` |
| [KleinErlangenSphereContactAndBinaryForms.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean) | 1030 | 53458 | 169 | 42 / 23 | `01b886a3634e664d5da54587a9d1a995c91aace58e6e8452ac85be55a1fdad19` |
| [PluckerGrassmannKleinUnifiedSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean) | 1130 | 60480 | 169 | 37 / 22 | `293d36c6b0ee21b88d27dcb057d6bebd047d284ff4a7526244dbaa9de9f733df` |
| [BirkhoffHilbertChordSectorClosure.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/BirkhoffHilbertChordSectorClosure.lean) | 563 | 29104 | 29 | 15 / 5 | `b98a7ebc8be5adb729843c3578f73e192791616c0d3be81cf4e2dd742fd0c6a7` |
| [SmoothPrincipalCartanBundleClosure.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean) | 938 | 51916 | 131 | 39 / 6 | `d9ca3e346bd16a797e3eda4332a3a224edc7caf18e3ea6fc99e1e2a654d27002` |
| [QuinticTschirnhausPluckerVietaSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/QuinticTschirnhausPluckerVietaSynthesis.lean) | 1250 | 64096 | 185 | 93 / 1 | `c87a84a779bdabc0466c64889705c67e055a9a40955a89eb71db0f54feb9a6ce` |
| [KleinIcosahedralHauptmodulAndGaloisResolvent.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinIcosahedralHauptmodulAndGaloisResolvent.lean) | 2000 | 110859 | 186 | 55 / 39 | `8efe162a27a02ba097d0f9254a2006a6768828f451bb0e1e01f6e186eef8f5d7` |
| [KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean) | 2351 | 128775 | 403 | 113 / 8 | `b4b716347e406fe29780f902b1437ecbde9889f6a6dc33f7f3dc94aabb6d0ae9` |

*(Together with the six previously staged Grassmann endmatter artifacts listed in Section 6, covering 1,538 compiled declarations across these 9 modules.)*

### 1.2 Explicit Preservation Boundary for Concurrent Workspace Activity

All four repository gaps (`Gap 1`–`Gap 4`) and all 9 phase modules above are built, verified, and selectively staged alongside the 8 reconciled sister modules whose headers/screener findings/lightweight imports we repaired (`GrassmannianCartanInteroperability.lean`, `GeneralHilbertConeMetric.lean`, `BirkhoffHilbertConeMetric.lean`, `SmoothCartanGeometry.lean`, `KleinApolloniusQuinticResolvent.lean`, `KleinQuinticDoubledCylinderPluckerBridge.lean`, `KleinQuinticDoubledCylinderRepresentation.lean`, `KleinQuinticVietaBinaryBridge.lean`). Files actively owned by concurrent workspace sessions (`KleinBrioschiQuinticResolvent.lean` held in `git add -p`, `KleinIcosahedralQuinticModularJ.lean` edited/rebuilt concurrently, `Krein/DoubledSpace.lean`, `Cl11KleinFourAdjointRepresentation.lean`, `Quantum/RealKCategory.lean`, `AllExhaustive.lean`, etc.) and shared barrel files (`Projective/All.lean`, `Canonical/All.lean`, `AllExhaustive.lean`, which hold our working-tree import registrations alongside other sessions' edits) are not staged (`AGENTS.md` rule: *Preserve unrelated work*).
- [QuinticTschirnhausPluckerVietaSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/QuinticTschirnhausPluckerVietaSynthesis.lean) remains cleanly decoupled onto native Mathlib (`Mathlib.LinearAlgebra.Vandermonde`, `Mathlib.GroupTheory.SpecificGroups.Alternating`).
- [KleinIcosahedralHauptmodulAndGaloisResolvent.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinIcosahedralHauptmodulAndGaloisResolvent.lean) closes Gap 2 cleanly against `InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent`, `InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ`, and native Mathlib `ModularForm`, `LaurentSeries`, and Galois theory.
- [KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean) bridges `1862–1893` (Evanston Colloquium Lectures I–XI + Möbius/Kůrka geometry) across Plücker, Grassmann, Klein, Clifford, and Gap Closures `1–4`.

---

## 2. Grassmann 1862 Endmatter Completion (`GA₂₇`–`GA₃₁`)

Owner: [GrassmannSubspaceShadowsResultantAndHadamard.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/GrassmannSubspaceShadowsResultantAndHadamard.lean)
Prior baseline modules (staged):
- `GrassmannAusdehnungslehreRegressiveShadow.lean`
- `GrassmannPfaffianDarbouxAlgebra.lean`
- `GrassmannPluckerMeetAndCircleSpace.lean`
- `GrassmannPfaffianSyzygyAndNormalForms.lean`
- `GrassmannProductQuotientAndMasterAtlas.lean`
- `docs/GRASSMANN_AUSDEHNUNGSLEHRE_1862_ENDMATTER_EPISTEMIC_COMPILATION.md`

Proved additions in `GrassmannSubspaceShadowsResultantAndHadamard.lean`:
- **Noncommutativity witness**: `grassmann_wave4_mod1_noncommutative_witness` (`¬ Commute (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 0)) (ExteriorAlgebra.ι ℝ (Pi.basisFun ℝ (Fin 2) 1))`).
- **Editorial Note 29 (`GA₂₄`–`GA₂₆`)**: `volCoord_eq_zero_of_mem_exteriorPower_lt`, `volCoord_change_basis`, `volCoord_eq_of_det_eq_one`, `note29_thm1_regressive_blades_decomposable`, `note29_thm2_hodge_blade_decomposable_and_support`, `note29_thm3_exists_regressive_quotient_blade`, `note29_thm4_thm5_hodge_subordination_and_incidence`.
- **Editorial Notes 39 & 44**: `note39_progressive_shadow_sign_cancellation`, `note39_regressive_shadow_sign_cancellation`, `note44_underdetermined_exterior_cramer`.
- **Editorial No. 136 (`GA₂₇`)**: `polyTruncVec`, `sylvesterColumns`, `grassmann_no136_exterior_resultant`, `grassmann_no136_exterior_resultant_eq_zero_iff`.
- **Editorial Notes 49, 52, 53, 62 (`GA₂₈`–`GA₂₉`)**: `note49_extInner_unit_factor_cancel`, `IsCompletelyNormal`, `IsNormalNo152`, `notes52_53_completely_normal_theorems`, `notes52_53_normal_not_completely_normal_dim3`, `note62_hodge_eq_iff_orthonormal`.
- **Editorial Notes 68–70 (`GA₃₀`–`GA₃₁`)**: `vecInner`, `vecInner_apply`, `vecInner_pos_def`, `vecInner_isSymm`, `note69_exterior_hadamard_inequality`, `notes68_70_unequal_grade_normal_shadow_angles`.

---

## 3. Felix Klein 1872 *Erlangen Program* (`EK₁`–`EK₁₀`)

### 3.1 Transformation Groups, Principal Group, Transfer, & Conic Duality (`EK₁`–`EK₅`)

Owner: [KleinErlangenProgramGroupsAndProjectiveTransfer.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Projective/KleinErlangenProgramGroupsAndProjectiveTransfer.lean)

- **Ground noncommutativity**: `kleinErlangenGroups_mat2_not_commute`, `kleinErlangenGroups_mat2Z_not_commute`.
- **`EK₁` (Transformation groups & Footnote 8 infinite-set inverse countermodel, §1)**: `klein_fn8_finite_mul_closed_has_one_and_inv`, `finiteMulClosedSubgroup`, `klein_fn8_finite_perm_closed_is_subgroup`, `posShiftSet`, `klein_fn8_infinite_perm_countermodel`.
- **`EK₂` (Collineations, Correlations, & Principal Group / Spherical Absolute, §1, §3)**:
  - `IsOrderCollineation`, `IsOrderCorrelation`, `collineationSubgroup`, `collineationCorrelationSubgroup`, `not_both_collineation_and_correlation`, `mul_two_correlations_mem_collineations`, `dualityParityHom`, `correlations_not_closed_under_mul_bool`, `pointHyperplaneIncident`, `projective_incidence_contragredient_and_swap`.
  - `EuclideanSimilarity`, `euclidDistSq`, `simProjMatrix`, `simToProjGL`, `sphericalInfinityQuadricC`, `simProjMatrix_preserves_H_inf_and_sphericalQuadric`, `klein_sec3_principal_group_iff_spherical_absolute`.
- **`EK₃` (Subgroup adjoining, `Abbildung` transfer, & Body kernel / Footnote 23, §2, §4, §5)**: `klein_sec2_stabilizer_adjoining_equiv`, `klein_sec4_abbildung_perm_transfer`, `klein_sec5_fn23_body_kernel_eq_normalCore`, `gl2_neg_one_acts_nontrivially_yet_fixes_projective_body`.
- **`EK₄` (Veronese conic transfer, Hesse transference, & Plücker–Klein Hodge duality, §4, §5, Note V)**: `veroneseVec`, `conicForm_veroneseVec`, `sym2Mat`, `sym2Mat_mul`, `sym2Mat_det`, `sym2Mat_mulVec_veronese`, `conicForm_sym2Mat`, `sym2GL2`, `hessePairPoint`, `hesseDiscForm`, `hesseMat`, `hesse_transference_theorems`, `kleinHodgeDual`, `kleinHodgeDual_theorems`.
- **`EK₅` (Sharp 3-transitivity of `PGL(2)` & Note VI boundary collapse, §10.1, Note VI)**: `pgl2FrameMatrix`, `pgl2_three_transitive`, `pgl2_fix_three_basepoints_is_scalar`, `klein_noteVI_triple_invariant_const`, `klein_noteVI_boundary_collapse_and_pole_metric`.

### 3.2 Stereographic Lightcone, Lie Sphere Contact, Cremona–Legendre, & Binary Syzygies (`EK₆`–`EK₉`)

Owner: [KleinErlangenSphereContactAndBinaryForms.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean)

- **Ground noncommutativity**: `kleinErlangenSphere_quat_not_commute`, `kleinErlangenSphere_mat3Q_not_commute`.
- **`EK₆` (Möbius `(n+1, 1)` stereographic lightcone & Footnote 26 anti-holomorphic separation, §6)**: `moebiusQuadricBilin`, `stereoQuadricVec`, `stereoInfVec`, `moebiusInversionEquiv`, `klein_sec6_stereographic_and_inversion`, `klein_fn26_unit_circle_inversion_not_holomorphic_moebius`.
- **`EK₇` (Lie `(n+1, 2)` sphere quadric, signatures, & Laguerre radius-shift group, §7)**: `lieQuadricBilin`, `lieSphereVec`, `IsOrientedSphereTangent`, `klein_sec7_lie_sphere_quadric_and_tangency`, `lieQuadricBilin_signature_dim2`, `lieQuadricBilin_signature_dim3`, `laguerreShift`, `klein_sec7_laguerre_shift_theorems`.
- **`EK₈` (Cremona involution, `fderiv` linearization, & `(2n+1)` Legendrian contact duality, §8–9)**: `cremonaPlane`, `klein_sec8_cremona_involution_and_non_collineation`, `tangentLinearizationEquiv`, `klein_sec8_linearization_functorial`, `ContactJetSpace`, `contactOneForm`, `pointLegendrian`, `surfaceLegendrian`, `legendreContact`, `dLegendreContact`, `klein_sec9_contact_legendre_unification`.
- **`EK₉` (Quaternion `SO(3)` action, binary cubic/quartic syzygies, & equal-edge `V₄` tetrahedron, Fn. 37, Note VII)**: `quatConjRot`, `klein_fn37_quaternion_so3_action`, `binaryCubic`, `cubicHessian`, `cubicJacobian`, `cubicDiscriminant`, `klein_noteVII_binary_cubic_syzygy`, `kleinTetraVertex`, `klein_noteVII_symmetrical_tetrahedron`, `binaryQuartic`, `quarticHessian`, `quarticSexticT`, `quarticInvI`, `quarticInvJ`, `klein_noteVII_binary_quartic_syzygy_and_pencil`.

---

## 4. Triadic Unification & Repository Gap Closures

### 4.1 Plücker–Grassmann–Klein Triadic Bridges (`PGK₁`–`PGK₅`, Gap 1 Closure)

Owner: [PluckerGrassmannKleinUnifiedSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean)

- **Ground noncommutativity witnesses**: `pgkUnified_mat2_not_commute`, `pgkUnified_ext1_not_commute`, `pgk5_gl2_matrix_noncommutative`.
- **`PGK₁` (Progressive product = Plücker ray coordinates; 4-fold wedge = Klein polarity; Hodge = correlation duality)**:
  - `pluckerToExterior2 : Plucker6 R → ExteriorAlgebra R (Fin 4 → R)`
  - `ι_vec4_mul_ι_vec4`: `ExteriorAlgebra.ι R (vec4ToFin4 u) * ExteriorAlgebra.ι R (vec4ToFin4 v) = pluckerToExterior2 (Vec4.wedge u v)`
  - `pluckerToExterior2_mul_pluckerToExterior2`: `pluckerToExterior2 P * pluckerToExterior2 Q = (Plucker6.polar P Q) • extVol4`
  - `extVol4_eq_ιMulti_basisFun`
  - `hodge_pluckerToExterior2_eq_kleinHodgeDual`: `hodge (Pi.basisFun K (Fin 4)) (pluckerToExterior2 P) = pluckerToExterior2 (kleinHodgeDual P)`
- **`PGK₂` (Grassmann circle space ↔ Möbius `O(3,1)` ↔ Lie `O(3,2)` 2-to-1 tangency cover)**:
  - `grassmann_circleTangent_iff_lie_double_cover`
  - `pgk2_circle_moebius_lie_three_tier_bridge`
- **`PGK₃` (Darboux–Pfaffian square = Plücker determinant = Lie–Klein isotropic/Legendrian bound)**:
  - `pgk3_pfaffian_plucker_klein_contact_bridge`
- **`PGK₄` & `EK₁₀` (Exterior resultant ↔ Hesse transference; Plücker Kummer ↔ Klein `V₄` tetrahedron; 10-node non-linear Erlangen DAG)**:
  - `pgk4_exterior_resultant_iff_hesseDisc`
  - `pgk4_plucker_kummer_klein_tetrahedron_v4_bridge`
  - `KleinErlangenArchetype` (`EK1`..`EK10`), `kleinMask`, `klein_causal_poset_branching_witnesses` (`EK2/EK3`, `EK5/EK7`, `EK7/EK8`, `EK8/EK9` pairwise incomparable), `klein_all_reach_master`, `plucker_grassmann_klein_grand_synthesis`
- **`PGK₅` (Gap 1 Closure — Exact 5-Carrier Equivalence Pentagon for `Gr(2,4)`)**:
  Unifies the five `Gr(2,4)` carriers into a single commuting theorem `pluckerGrassmannKlein_pentagon_commutes`:
  1. `FullRankMatrix24Quotient` (`Quotient fullRankMatrix24Setoid`, `2 × 4` real full-rank matrices modulo left `GL(2, ℝ)` row operations), mapped via `fullRankMatrix24QuotientEquivRealTwoPlane` and `fullRankMatrix24QuotientEquivRealTwoPlane_mk`;
  2. `RealTwoPlane` (`{ P ≤ Vec4 // finrank = 2 }`), mapped via `realTwoPlaneEquivMathlibGrassmannian`;
  3. `Module.Grassmannian ℝ InfoGeometry.Canonical.FierzKleinFoundation.Vec4 2` (Mathlib Grothendieck Grassmannian);
  4. `KleinLocus` (`⊆ ℙ ℝ (⋀² Vec4)`), mapped via `kleinLocusEquivProjectivePluckerQuadric`;
  5. `ProjectivePluckerQuadricLocus` (`{ p : ℙ ℝ Bivector4 // ProjectiveIsKleinFormZero p }`), matching `bivector4OfPlucker6 (plucker6OfMatrix C.1)` cleanly against `kleinQ_plucker6OfMatrix`.

### 4.2 Gap 3 Closure: Birkhoff–Hilbert Arbitrary-Endpoint Two-Ray Sector & Projective Chord

Owner: [BirkhoffHilbertChordSectorClosure.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/BirkhoffHilbertChordSectorClosure.lean)

Eliminates the conditional two-ray sector hypothesis on `birkhoff_crossRatio_chord_identity` for ANY salient `C : ProperCone ℝ E` (`[Nontrivial E]`) and ANY two interior points `x, y ∈ interior (C : Set E)` on distinct rays (`¬ ∃ c : ℝ, 0 < c ∧ x = c • y`):
- **Constructive extremal frontier rays**: `extremalRayLeft`, `extremalRayRight`, `extremalRayLeft_mem`, `extremalRayRight_mem`, `one_lt_upperGauge_mul`, `extremalRayLeft_ne_zero`, `extremalRayRight_ne_zero`, `extremalRayLeft_mem_frontier`, `extremalRayRight_mem_frontier`.
- **Unconditional sector & linear independence**: `extremalRays_twoRay_sector` and `extremalRays_linearIndependent`.
- **Unconditional projective chord cross-ratio & affine dichotomy**: `birkhoffHilbertMetric_arbitrary_endpoints_projective_chord`, `birkhoffHilbertMetric_affine_chord_of_incomparable`, `affine_ray_stays_in_cone_of_upperGauge_le_one`.
- **Noncommutativity witness**: `birkhoff_sector_closure_matrix2_noncommutative`.

### 4.3 Gap 4 Closure: Generic Smooth Principal-Bundle Cartan Geometries

Owner: [SmoothPrincipalCartanBundleClosure.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean)

Extends `SmoothCartanGeometry` from limited local packages and the homothety model to generic `C³` right-`H` principal Cartan bundles (`SmoothPrincipalTrivialization`, `SmoothPrincipalCartanGeometry`):
- **Principal bundle structure & sections**: `localPrincipalSection` (`_proj`, `_apply`, `_contMDiffOn`), `sectionThrough` (`_proj`, `_self`, `_contMDiffOn`), `principal_fiber_torsor_existsUnique`, `principal_same_fiber_iff_orbit`, `principal_proj_surjective`, `principal_proj_continuous`, `principal_proj_isOpenMap`.
- **Čech 1-cocycle & automatic submersion**: `principalTransition` (`_contMDiffOn`, `_coord_change`, `_self`, `_cocycle`, `_inv`), `principal_mfderiv_proj_surjective`, `principalCartanBaseTangentEquiv`, `pullbackCartanGaugePotential` (`_spec`).
- **Constructive closed inhabitants**: `multiplicativeRealLieGroup`, `homothetyPrincipalTrivialization`, `flatHomothetyPrincipalTrivialization`, `homothetyPrincipalCartanGeometry`, `flatHomothetyPrincipalCartanGeometry`, `lieGroupAdEquiv`, `lieGroupPrincipalCartanGeometry`, `gl2RPrincipalCartanGeometry`, `principal_cartan_gl2R_noncommutative`.

### 4.4 Tschirnhaus–Plücker–Vieta Quintic Synthesis (`SOLVE / COAGULA` & `black-book-method`)

Owner: [QuinticTschirnhausPluckerVietaSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/QuinticTschirnhausPluckerVietaSynthesis.lean)

Constructive synthesis decoupled directly onto Mathlib's `Mathlib.LinearAlgebra.Vandermonde` and `Mathlib.GroupTheory.SpecificGroups.Alternating`, encoding the `SOLVE / COAGULA` graded poset (`Δ₀..Ξ_⊤`, `Ax.1`–`Ax.5`, `Ded.1`–`Ded.5`, `A₀`/`A₁`/`A₂`/`A_ω`, `Thm.⊤`):
- **Noncommutativity ground witness**: `quinticTschirnhaus_gl2_noncommutative`.
- **Elementary symmetric Vieta map & shear aporia (`A₁`)**: `monicRootPoly5`, `vietaE1`..`vietaE5`, `monicRootPoly5_vieta_expansion`, `monicRootPoly5_coeffs`, `monicRootPoly5_perm`, `vieta_perm_invariant`, `vieta_smul_weights`, `poly_smul_root_invariant`, `aporia_A1_vieta_weight_shear_countermodel`, `vieta_quadruple_ne_zero_of_sum_zero`.
- **5D Exterior–Plücker isomorphism & Klein quadric**: `RootPair5`, `RootTriple5`, `card_rootPair5`, `card_rootTriple5`, `plucker5Multilinear`, `plucker5Alternating`, `plucker5ExteriorMap` (`_ιMulti`, `_surjective`, `_finrank_eq`), `plucker5ExteriorLinearEquiv`, `signedPlucker5Coord`, `kleinPlucker5Quadric`, `kleinPlucker5Quadric_decomposable`.
- **Tschirnhaus hyperplane, diagonal kernel aporia (`A₀`), & Schubert `Gr(2,5)` injection**: `onesVec5`, `simplicialDiff5`, `exteriorCoboundary5` (`_eq_ιMulti`, `_smul_weight1`), `aporia_A0_diagonal_kernel`, `TschirnhausHyperplane5`, `finrank_tschirnhausHyperplane5`, `tschirnhausProj5` (`_ker`, `_surjective`), `quotientOnesEquivTschirnhaus5`, `tschirnhausExteriorCoboundary5_injective`, `schubertPsi1Proj_injective`, `schubertPsi1Grassmannian_injective`, `simplicialCoboundary1`, `simplicialCoboundary1_comp_simplicialDiff5`, `range_simplicialDiff5_eq_ker_coboundary1`, `finrank_range_exteriorCoboundary5`, `kleinPlucker5_zero_of_mem_ker_coboundary1`.
- **Vandermonde exterior/Plücker obstruction & multi-weight ladder**: `vandermondeExterior5`, `vandermondePlucker5`, `vandermondeExterior5_smul_weight3`, `kleinPlucker5_vandermondePlucker5`, `coboundary1_vandermondePlucker5`, `vandermondeExterior5_not_mem_flat_schubert`, `vandermondeGrassmannianPoint`, `vandermondeGrassmannianPoint_not_mem_flat_range`, `quinticVandermonde`, `quinticDisc5`, `quinticVandermonde_smul`, `multi_weight_homogeneity_ladder`.
- **Alternating sign-erasure (`A₂`) & no-linear-section (`A_ω`) aporiae**: `signedFlip5`, `aporia_A2_sign_erasure_and_A5_recovery`, `aporia_Aomega_no_linear_vieta_section`.
- **Weighted projective descent & `S₅`/`A₅` equivariant synthesis (`Thm.⊤`)**: `WeightedProj2345`, `OrientedWeightedProj2345_10`, `orientedToUnorientedWeightedProj`, `z2OrientationFlip`, `weightedVietaDescent`, `orientedWeightedVietaDescent`, `orientedWeightedVietaDescent_factorization`, `permTschirnhaus`, `permTschirnhausLinear` (`_coe_val`, `_injective`), `permTschirnhausProj`, `vietaDescent_equivariance`, `quintic_tschirnhaus_plucker_vieta_master_synthesis`.

### 4.5 Gap 2 Closure: Common `2I`/`A₅` Icosahedral Forms, Level-One `j` Hauptmodul, & Generic Quintic Galois Resolvent

Owner: [KleinIcosahedralHauptmodulAndGaloisResolvent.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinIcosahedralHauptmodulAndGaloisResolvent.lean)

Closes the remaining open gaps documented on `InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ` and `InfoGeometry.Erlangen.KleinBrioschiQuinticResolvent`:
- **Noncommutativity witnesses**: `kleinClosure_mat2C_noncommutative`, `kleinClosure_mat2Z_noncommutative`.
- **Common literature `2I`/`A₅` invariance of `(F, H, T)`**: `kleinAlignedIntertwiner`, `kleinAlignedStandardGenB`, `kleinAlignedIntertwiner_isUnit`, `icosianGenA_alignedIntertwining`, `icosianGenB_alignedIntertwining`, `kleinBinaryForms_invariant_under_alignedGenB`, `kleinAlignedVertexF`, `kleinAlignedFaceH`, `kleinAlignedEdgeT`, `kleinAlignedRatio`, `kleinAlignedBrioschiParam`, `kleinAligned_syzygy_1728`, `kleinAligned_homog`, `binaryIcosahedralGroup_invariant_alignedForms`, `binaryIcosahedralGroup_invariant_ratio`, `alternatingGroup5_invariant_alignedForms`.
- **Analytic cusp pole, transcendence, & level-one `j` Hauptmodul**: `jCuspFunction`, `jInvariant_eq_jCuspFunction_qParam`, `jCuspFunction_tendsto_simple_pole`, `differentiableOn_jCuspFunction_punctured`, `jLaurentSeries`, `jLaurentSeries_principal_part`, `jInvariant_aeval_injective`, `normalizedJInvariant_aeval_injective`, `modularFormOfJPoly` (`_apply`), `modularForm_weight_twelve_mul_eq_poly_jInvariant`, `modularForm_weight_twelve_mul_eq_poly_normalizedJInvariant`, `modularForm_even_weight_rational_jInvariant`.
- **`F₂₀` Cayley–Weber sextic resolvent, Tschirnhaus principal reduction, Brioschi chain, & master closure**: `affinePerm5`, `frobenius20Subgroup`, `frobenius20Subgroup_card_and_solvable`, `cayleyWeberRootInv` (`_frobenius20_invariant`), `cayleyWeberCosetVal` (`_mk`), `cayleyWeberSexticResolvent` (`_monic_natDegree`), `galFieldToPerm` (`_spec`, `_injective`), `splittingGalMulEquiv`, `exists_rootEquiv_of_separable_degFive`, `quinticVandermonde` (`_alternating_iff`), `cayleyWeberSexticResolvent_descends`, `cayleyWeberSexticResolvent_galois_criterion`, `quintic_A5_sextic_no_root`, `tschirnhausPrincipal_powerSums_zero`, `brioschiResolventField`, `brioschi_rescaling_identity`, `tschirnhaus_splitting_galois_hom`, `icosahedral_hauptmodul_galois_closure_master`.

### 4.6 Klein 1893 *Evanston Colloquium*, Möbius / Kůrka Geometry, & Six-Pillar Grand Closure

Owner: [KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean](file:///home/goutev/repos/info-geometry-lean/lean/InfoGeometry/Canonical/KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean)

Synthesizes Felix Klein's 1893 *Evanston Colloquium: Lectures on Mathematics* (`ICM1893.2.ocr.pdf`) and the Möbius geometry / Kůrka iterative-system suite (`moebius (2).pdf`, `2009_59.pdf`, `cpearlso.pdf`, `outline_term2_5.pdf`) directly onto the `1862–1884` foundation and Gap Closures `1–4`:
- **Section 0 (`T16`)**: `evanston_mat2R_noncommutative`, `evanston_quat_noncommutative`.
- **Section 1 (*Evanston* Lectures I–III — Lie sphere tangency, Plücker dynames, & Legendrian contact)**: `lie_line_sphere_dyname_contact_bridge` uniting `PluckerRayAxisAndDyname.dyname_add_kleinQ`, `PluckerLinearComplex.complexMatrix_det`, Grassmann 1877 `particleSystemDyname_two_force_splitting`, `grassmann_circleTangent_iff_lie_double_cover`, `lieQuadricBilin`, and `legendreContact` / `contactOneForm`.
- **Section 2 (*Evanston* Lecture IV — Clebsch diagonal & Cayley 4-nodal cubic ↔ 16-node Kummer quartic)**: `clebschDiagonalSum1`, `clebschDiagonalSum3`, `clebschDiagonal_perm_invariant`, `cayleyCubic`, `cayleyCubicGrad`, `cayleyNode`, `cayleyCubic_perm_invariant`, `cayleyCubic_homog3`, `cayleyNode_singular_and_independent`, `cayley_six_edges_lie_on_cubic`, `evanston_cayley_cubic_to_kummer_quartic_bridge`.
- **Section 3 (*Evanston* Lectures VII–VIII — Ideal numbers & non-unique factorization in `ℤ[√-5]`)**: `ZSqrtNeg5`, `zSqrtNeg5Mul`, `zSqrtNeg5Norm`, `zSqrtNeg5Norm_mul` (Brahmagupta–Gauss composition), `zSqrtNeg5_norm_one_iff`, `zSqrtNeg5_no_norm_two_or_three`, `evanston_lec8_nonunique_factorization_and_ideal_norm` (`2 * 3 = (1 + √-5)(1 - √-5) = 6`).
- **Section 4 (*Evanston* Lecture IX — Klein's order-168 quartic `x³y + y³z + z³x = 0`)**: `kleinQuarticCurve`, `kleinQuarticCurve_cyclic_perm`, `kleinQuarticCurve_order7_diagonal_automorphism` (`diag(ζ⁴, ζ², ζ)` with `det = ζ⁷ = 1`).
- **Section 5 (*Evanston* Lecture XI — Clifford–Klein space forms & flat Clifford torus in `S³`)**: `cliffordTorus`, `cliffordTorusDu`, `cliffordTorusDv`, `cliffordTorus_mem_unitSphere3`, `cliffordTorus_hasDerivAt_and_flat_metric` (`E = G = 1/2, F = 0`).
- **Section 6 (Möbius geometry & Kůrka iterative maps)**: `cayleyUpperToDisk`, `cayleyDiskToUpper`, `kurkaDiskMap`, `cayley_normSq_diff_identity`, `cayleyUpperToDisk_and_kurkaDiskMap_unitDisk`, `cayley_left_right_inverse`, `kurkaDiscAlpha`, `kurkaDiscBeta`, `kurka_disc_alpha_beta_det_identity` (`|α|² - |β|² = 4(ad - bc)`), `kurkaMoebius`, `kurka_moebius_hasDerivAt_and_contraction`.
- **Section 7 (Selected *Evanston* lecture statements)** (Lectures VI and XII are not represented in this owner):
  - *Lecture I*: `clebschGenusDouble`, `evanston_lec1_clebsch_genus_and_noether_af_bphi` (rational genus criterion, smooth quartic `2p = 6`, and Max Noether `AF + BΦ` `HasDerivAt` tangent decomposition);
  - *Lectures II–III*: `pfaffContactForm`, `wheelGearingOffset`, `wheelGearingNormalVal`, `evanston_lec2_3_lie_pfaff_contact_M2_and_gearing` (point-sheaf & path `M₂` contact, normal-offset wheel-gearing circle);
  - *Lecture IV*: `kleinRealityLHS`, `kleinRealityRHS`, `pluckerDualClass`, `pluckerDualInflexions`, `evanston_lec4_klein_reality_equation_and_kummer16` (`n + w' + 2t'' = k + r' + 2d''` across smooth/crunodal/acnodal/cuspidal cubics & 4-oval quartic, plus Rohn's 16-node Kummer hyperboloid checkerboard);
  - *Lecture V*: `schwarzianJet`, `schwarzianDiv`, `moebiusJet1`–`moebiusJet3`, `circularTriangleSpeciesI`, `evanston_lec5_schwarzian_moebius_invariance_and_ode` (Schwarzian Möbius invariance, zero Wronskian derivative & ODE quotient `{η, x} = 2q`, and circular-arc species trichotomy);
  - *Lecture VII*: `hilbertFactorialRatio` (`_mul_factorial`, `_dvd`), `evanston_lec7_hilbert1893_transcendence_integer_kernel` (legacy name; proves only the prime-factorial non-divisibility lower bound `1 ≤ |P₁|`, not transcendence);
  - *Lecture VIII*: `gaussQuadForm`, `gaussDisc`, `evanston_lec8_gauss_form_disc_and_secondary_composition` (`SL(2, ℤ)` discriminant invariance, Stickelberger `mod 4`, and `D = -20` secondary-class `(2, 2, 3)` composition);
  - *Lectures IX–X*: `centered5Q`, `centeredSq5Q`, `kleinRootBivector5Q`, `thetaEvenCount`, `thetaOddCount`, `evanston_lec9_10_quintic_bivector_and_theta_bitangents` (legacy name; proves the char `≠ 2` central-character obstruction, squared cyclic equivariance, two root-tuple witnesses for `kleinRootBivector5Q`, parity-count formulas and the numerals `28` and `51840`; no bitangent or theta-characteristic objects are constructed. In the separate complex root-space owners, `rootKleinOmega5ToPlucker6_eq_rootKleinOmega` identifies the first-four-coordinate projection of the ten-coordinate centered wedge with the six-coordinate chart, and `rootKleinOmega5_eq_tschirnhausVandermondeBivector` reconciles the two ten-coordinate implementations. This does not bridge either root covariant to the rational `kleinRootBivector5Q` or descend it to coefficient space);
  - *Lecture XI*: `quatNormSqR`, `quatDotR`, `evanston_lec11_cayley_klein_and_clifford_parallels` (Clifford parallel commutativity & constant equidistant angle cosine on `S³`).
- **Section 8 (Selected Möbius & Kůrka number-system results)**: `kurkaMoebiusNorm` (`_ge_two_and_eq_two_iff_rotation`, `‖M‖ ≥ 2` and `‖M‖ = 2 ↔ rotation`), `kurkaCircleDeriv` (`_chain_rule_and_rotation_isometry`), `kurkaRectF0`, `kurkaRectF0Bar`, `kurkaRectF1`, `kurkaRectF1Bar`, `kurka_biternary_square_eq_quadrononary_and_inverses` (`q₀=2, q₁=3` squared to `q₀=4, q₁=9`, two-sided inverses, & `x² ± 4x + 1 = 0` threshold), `moebius_trace_crossRatio_and_circle_to_line_inversion` (trace discriminant, 4-point cross-ratio invariance, & circle inversion `|z - 1/2| = 1/2 ↔ Re(w) = 1`).
- **Section 9 (Phase 0–V *Solve et Coagula* non-commutative epistemic algebra & causal poset)**: `epistemicQ`, `epistemicGamma`, `epistemicT`, `epistemicX`, `epistemicY`, `epistemicG`, `epistemicF`, `epistemicM`, `epistemicK`, `epistemicAporia`, `epistemicShadowAporia`, `epistemicSigma0`, `epistemicB`, `epistemicJ`, `solveEtCoagula_prop1_orthogonality_and_polarity`, `solveEtCoagula_prop2_fourfold_and_nilpotency`, `solveEtCoagula_prop3_transcendent_bridge_gravity_tension`, `solveEtCoagula_prop4_socratic_aporia_and_intertwining` (`T - T² = Y X`), `solveEtCoagula_prop5_and_thm_omega_reciprocal_totality` (`1 - Σ₀² = B² = 4M`, `J_Ω² = 1`, `J_Ω ≠ Γ`), `solveEtCoagula_prop6_parity_soldered_meta_tower` (`D₁² = B₀² + B₁²`), `solveEtCoagula_concrete_mat2_witness`, `SolveEtCoagulaNode` (16 nodes), `solveEtCoagula_poset_strict_order_and_branching`.
- **Section 10 (Six-Pillar & *Solve et Coagula* Grand Closure)**: `evanston1893_all_twelve_lectures_and_kurka_moebius_complete_closure` (legacy identifier for its selected proposition bundle) and `plucker_grassmann_klein_clifford_evanston_grand_closure`. These bundle the listed propositions; they do not formalize every argument in every Evanston lecture.

---

## 5. Verification & Audit Summary

All checks below ran after the final edit to each corresponding file:

1. **Strict Locked Compilation & Build Verification**:
   - `GrassmannSubspaceShadowsResultantAndHadamard.lean`: `.olean` built (`opengauss_screener.py` 0 traps, `semantic_content_audit.py --gate-review` 0 findings).
   - `KleinErlangenProgramGroupsAndProjectiveTransfer.lean`: after replacing `FelixKleinGeometryUnification` with lightweight `Projective/*`, `InvariantGeometry`, and `Mathlib.LinearAlgebra.Projectivization.{Basic,Action}` imports, passed `run_locked_lean.py -- -DwarningAsError=true` (`exit 0`, `task-5753`) and `.olean` build.
   - `KleinErlangenSphereContactAndBinaryForms.lean`: after adding explicit `Mathlib.Analysis.Calculus.Deriv.Basic`, passed `opengauss_screener.py` (0 traps) and `.olean` rebuild (`task-5800`, `9466` jobs).
   - `BirkhoffHilbertChordSectorClosure.lean`, `PluckerGrassmannKleinUnifiedSynthesis.lean`, `QuinticTschirnhausPluckerVietaSynthesis.lean`, `SmoothPrincipalCartanBundleClosure.lean`, `KleinIcosahedralHauptmodulAndGaloisResolvent.lean`, plus reconciled sister modules (`GrassmannianCartanInteroperability.lean`, `BirkhoffHilbertConeMetric.lean`, `SmoothCartanGeometry.lean`, `KleinApolloniusQuinticResolvent.lean`, `KleinQuinticDoubledCylinderPluckerBridge.lean`, `KleinQuinticDoubledCylinderRepresentation.lean`, `KleinQuinticVietaBinaryBridge.lean`, `GeneralHilbertConeMetric.lean`): `.olean` targets built cleanly in `task-5800` (`Build completed successfully (9466 jobs)`, `exit 0`).
   - `KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean`: passed `opengauss_screener.py` (`0` traps), `semantic_content_audit.py --gate-review` (`0` blocking, `0` review), `run_locked_lean.py -- -DwarningAsError=true` (`task-6146`, `exit 0`), and `.olean` build (`task-6150`, `Build completed successfully (9034 jobs)`, `exit 0`).
2. **Per-Module Axiom Check (`tools/infra/axiom_check.lean` / `axiom_check.py`)**:
   - `task-5330` & `task-5350`: passed (`OK`) on `GrassmannSubspaceShadowsResultantAndHadamard`, `BirkhoffHilbertChordSectorClosure`, `QuinticTschirnhausPluckerVietaSynthesis`, and `PluckerGrassmannKleinUnifiedSynthesis`.
   - `task-5573`: passed (`OK`, `2 passed, 0 failed`) on `SmoothPrincipalCartanBundleClosure` and `KleinIcosahedralHauptmodulAndGaloisResolvent`.
   - `task-6162`: `run_locked_lean.py --wait-for-build-lock --run tools/infra/axiom_check.lean` passed on `KleinEvanston1893MoebiusAndSixPillarMasterSynthesis` (`✓ all 420 declarations clean`, `PASS`; standalone `axiom_check.py` hit its hardcoded 300s `flock` wait timeout while an external `axiom_index.py` process held the lock, and all 9 phase modules were directly audited by `axiom_index.py --timeout 600` below).
3. **Consolidated Axiom Index (`tools/infra/axiom_index.py --timeout 600`, `task-6166`) & Scope Audit (`repo_lean_scope_audit.py`)**:
   - **9 / 9 Axiomless modules**, **1,538 declarations**, **0 nonstandard axiom users**, **0 partial / 0 unsafe**.
   - Unique transitive axioms across all 9 modules (3): `propext` (1,324 uses), `Quot.sound` (1,005 uses), `Classical.choice` (838 uses).
   - `repo_lean_scope_audit.py --fail-on authoritative` across all `22` task-owned & sister `.lean` files: `tracked Lean files: 22`, `debt files: 0`, `debt findings: 0`.

---

## 6. Staged Artifact Inventory

Core task-owned files (`16` total: `6` prior Grassmann 1862 endmatter + `10` phase files):
1. `lean/InfoGeometry/Projective/GrassmannAusdehnungslehreRegressiveShadow.lean`
2. `lean/InfoGeometry/Canonical/GrassmannPfaffianDarbouxAlgebra.lean`
3. `lean/InfoGeometry/Projective/GrassmannPluckerMeetAndCircleSpace.lean`
4. `lean/InfoGeometry/Canonical/GrassmannPfaffianSyzygyAndNormalForms.lean`
5. `lean/InfoGeometry/Canonical/GrassmannProductQuotientAndMasterAtlas.lean`
6. `docs/GRASSMANN_AUSDEHNUNGSLEHRE_1862_ENDMATTER_EPISTEMIC_COMPILATION.md`
7. `lean/InfoGeometry/Projective/GrassmannSubspaceShadowsResultantAndHadamard.lean`
8. `lean/InfoGeometry/Projective/KleinErlangenProgramGroupsAndProjectiveTransfer.lean`
9. `lean/InfoGeometry/Canonical/KleinErlangenSphereContactAndBinaryForms.lean`
10. `lean/InfoGeometry/Canonical/PluckerGrassmannKleinUnifiedSynthesis.lean`
11. `lean/InfoGeometry/Canonical/BirkhoffHilbertChordSectorClosure.lean`
12. `lean/InfoGeometry/Canonical/SmoothPrincipalCartanBundleClosure.lean`
13. `lean/InfoGeometry/Canonical/QuinticTschirnhausPluckerVietaSynthesis.lean`
14. `lean/InfoGeometry/Canonical/KleinIcosahedralHauptmodulAndGaloisResolvent.lean`
15. `lean/InfoGeometry/Canonical/KleinEvanston1893MoebiusAndSixPillarMasterSynthesis.lean`
16. `docs/KLEIN_ERLANGEN_PROGRAM_1872_AND_PLUCKER_GRASSMANN_UNIFICATION.md`

Plus `8` reconciled sister modules selectively staged together (`24` staged files total; barrel imports added in working tree to `Projective/All.lean`, `Canonical/All.lean`, `AllExhaustive.lean`):
17. `lean/InfoGeometry/Canonical/GrassmannianCartanInteroperability.lean`
18. `lean/InfoGeometry/Projective/GeneralHilbertConeMetric.lean`
19. `lean/InfoGeometry/Erlangen/BirkhoffHilbertConeMetric.lean`
20. `lean/InfoGeometry/Erlangen/SmoothCartanGeometry.lean`
21. `lean/InfoGeometry/Erlangen/KleinApolloniusQuinticResolvent.lean`
22. `lean/InfoGeometry/Erlangen/KleinQuinticDoubledCylinderPluckerBridge.lean`
23. `lean/InfoGeometry/Erlangen/KleinQuinticDoubledCylinderRepresentation.lean`
24. `lean/InfoGeometry/Erlangen/KleinQuinticVietaBinaryBridge.lean`
