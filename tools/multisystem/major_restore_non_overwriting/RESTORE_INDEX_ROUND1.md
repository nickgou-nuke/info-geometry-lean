# Major restore / non-overwriting index (round 1)

Scope: recover incidentally lost code from archives/chats/backups/fragments without overwriting live owner files.

Policy followed:
- no overwriting of live owner files
- recovery-first and context-first
- small Lean files / reusable lemmas
- no duplicate owner packets when a stronger live file already exists
- subagent-style sandbox discipline: only new artifacts under a non-canonical recovery path

Artifacts generated in this round:
- `scratch_recovery_inventory.json`
- `scratch_recovery_context_map.json`
- `RESTORE_INDEX_ROUND1.md`

## 1. High-confidence recovery surfaces found

Repo-local:
- `archive/scratch_recovery/` — 85 Lean recovery fragments
- `archive/` also contains scratch/sandbox witness material

Hermes local state:
- `~/.hermes/state.db`
- `~/.hermes/sessions/request_dump_*.json`
- `~/.hermes/checkpoints/store/...`

Codex local state:
- `~/.codex/sessions/**/*.jsonl`
- `~/.codex/history.jsonl`
- `~/.codex/logs_2.sqlite`
- `~/.codex/state_5.sqlite`

Antigravity/Gemini local state:
- `~/.gemini/antigravity-cli/history.jsonl`
- `~/.gemini/history/...`

## 2. Archive fragments already integrated live

These should NOT be rewritten as new owner files. The honest restore action is to point at the live owner surface and, if needed later, extract reusable lemmas from the live file rather than resurrect duplicate archive code.

### 2.1 Split Majorana prime gas
Archive fragment:
- `archive/scratch_recovery/sandbox_split_gas.lean`

Live owner already exists:
- `lean/InfoGeometry/Arithmetic/SplitMajoranaPrimeGas.lean`

Verified live hits include:
- `namespace InfoGeometry.Arithmetic.SplitMajoranaPrimeGas`
- `structure SplitPrimeCAR`
- `theorem Pi_eq_one_sub_two_N`
- blueprint registrations in `lean/InfoGeometry/auto_blueprints.lean`

Conclusion:
- restored live already
- do not duplicate

### 2.2 Bogoliubov / Hamiltonian RG flow bridge
Archive fragment:
- `archive/scratch_recovery/sandbox_hamiltonian.lean`

Live owner already exists under the honest name:
- `lean/InfoGeometry/Canonical/BogoliubovRGFlowBridge.lean`

Verified live hits include:
- `structure BogoliubovRGFlowBridge`
- `def rg_fixed_point_is_pure_bogoliubov_flow`

Conclusion:
- restored live under canonicalized file name
- do not recreate `SandboxHamiltonian`

### 2.3 Jordan-Wigner / Cantor representation bridge
Archive fragment:
- `archive/scratch_recovery/test_hom_proofs2.lean`

Live owner already exists:
- `lean/InfoGeometry/Canonical/JordanWignerCantorRepresentation.lean`

Verified live hits include:
- `def idxEquivCantorAddress`
- canonical orientation lemmas
- algebra-hom based complexification/reindexing corridor stronger than the old scratch `complexifyMat` snippet

External session evidence also points to this lane as already genuinely integrated:
- `~/.gemini/antigravity-cli/history.jsonl` lines around 387-390 mention the finite bridge / Cantor operator equivalence as a completed live step.

Conclusion:
- restored live in stronger form
- do not duplicate the scratch file

### 2.4 Asano induction / multiaffine step
Archive fragment:
- `archive/scratch_recovery/sandbox_asano_induction.lean`

Live owner already exists:
- `lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean`

Verified live hits include:
- `theorem multiaffine_2var_expansion`
- `def splitEval`
- `def toTwoVar`
- the inductive-step target around the Asano forbidden set

Conclusion:
- at least the core recovered mathematics is already live
- do not duplicate

### 2.5 Moore-Penrose closed-range existence package
Archive fragment:
- `archive/scratch_recovery/sandbox_mp_authoritative.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Singular/MoorePenrose.lean`
- adjacent lane `lean/InfoGeometry/Singular/MoorePenroseAdjoint.lean`

Conclusion:
- live owner exists; archive likely preserves an intermediate or alternate package shape
- compare later only if a live gap is identified
- no duplicate file now

### 2.6 Drazin existence/uniqueness package
Archive fragment:
- `archive/scratch_recovery/sandbox_drazin_test.lean`

Live owner already exists:
- `lean/InfoGeometry/Singular/Drazin.lean`
- adjacent lanes `DrazinAdjoint.lean`, `DrazinGreen.lean`

Verified live hits include:
- `theorem Drazin_unique`
- `theorem exists_drazinInverse_global`
- `theorem drazinInverse_spec`

Conclusion:
- restored live already
- do not duplicate

### 2.7 Complex bounded operator / matrix bridge
Archive fragment:
- `archive/scratch_recovery/sandbox_ultimate_cbo.lean`

Live owner already exists:
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`

Verified live hits include:
- `namespace ... CblinfunMatrix`
- `theorem matrixOfOp_adjoint`
- matrix/operator bridge lemmas

Conclusion:
- restored live already
- do not duplicate

### 2.8 Clean CBO substrate / final substrate / MP test wrapper
Archive fragments:
- `archive/scratch_recovery/sandbox_clean_substrate.lean`
- `archive/scratch_recovery/sandbox_final_substrate.lean`
- `archive/scratch_recovery/sandbox_mp_test_full.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`
- `lean/InfoGeometry/Singular/MoorePenrose.lean`

Observed relation:
- `sandbox_clean_substrate.lean` and `sandbox_final_substrate.lean` are smaller precursor versions of the operator/matrix bridge now represented live by the CblinfunMatrix lane.
- `sandbox_mp_test_full.lean` is a wrapper/test-stage around the Moore-Penrose package and points at the authoritative archive variant; the live owner is the stronger `Singular/MoorePenrose.lean` corridor.

Conclusion:
- restored live already in stronger form
- do not duplicate

### 2.9 Conductive MP helper packet
Archive fragment:
- `archive/scratch_recovery/sandbox_conductive_mp.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Singular/MoorePenrose.lean`

Observed relation:
- the archive helper theorems `map_starProjection_ker_orthogonal_fixed` and `exists_restrictedEquiv` are alternate-shape precursor lemmas to the live `mpRestricted` / `mpEquiv` corridor.

Conclusion:
- archive preserves useful historical proof shape
- but the mathematics is already live under stronger owner names
- do not duplicate

### 2.10 Singular regularization / Einstein anomaly packet
Archive fragment:
- `archive/scratch_recovery/sandbox_singular_test.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/Canonical/Singular.lean`
- downstream consumers like `lean/InfoGeometry/Quantum/HestenesKahler.lean`

Observed relation:
- the archive packet's core surfaces already appear live, including:
  - `adjoint_comp_self_isPositive`
  - `star_mul_self_isPositive`
  - `mul_star_self_isPositive`
  - `EinsteinAnomaly`
  - `exists_regularization_pair_of_selfAdjoint_idempotent`
  - `exists_regularization_pair_of_isUnit`
- session evidence also shows downstream build/use of the Einstein-anomaly lane.

Conclusion:
- restored live already in stronger/canonical form
- do not duplicate

### 2.11 Fredholm closure / HilbertDoubled assembly packet
Archive fragment:
- `archive/scratch_recovery/sandbox_fredholm_verification.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/KK/DiracFredholmModule.lean`
- `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
- `lean/InfoGeometry/Krein/HilbertBridge.lean`
- `lean/InfoGeometry/Krein/Clifford.lean`
- `lean/InfoGeometry/Canonical/DrazinSupercharge.lean`
- `lean/InfoGeometry/Canonical/DrazinFredholmBridge.lean`

Observed relation:
- the archive file is a `sorry`-filled assembly attempt over already-live carrier data
- `HilbertDoubled` already has live `KreinGradedModule` and split-`Cl(1,1)` action support
- the Fredholm-facing thin bridge already exists live in `DrazinFredholmBridge`
- no unique proved helper theorem was found in the archive fragment

Conclusion:
- duplicate/incomplete assembly over live owners
- do not duplicate

### 2.12 Hamiltonian flow bridge packet
Archive fragment:
- `archive/scratch_recovery/sandbox_hamiltonian_bridge.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/Canonical/HamiltonianFlowBridge.lean`
- `lean/InfoGeometry/Canonical/GrandCanonicalHamiltonianFlowBridge.lean`
- `lean/InfoGeometry/Dynamics/HamiltonianFlowBridge.lean`

Observed relation:
- the archive namespace is exactly the live namespace `InfoGeometry.Canonical.HamiltonianFlowBridge`
- the archive theorem names `informational_continuum_fusion` and `riemann_weil_wasserstein_identification` are already present live under the same names
- the live owner extends the archive packet with additional bridge readouts such as `majoranaDirac_as_quasilatticeDirac_zero`

Conclusion:
- restored live already, under the same owner namespace and theorem names
- do not duplicate

### 2.13 Split Clifford tower / direct-limit packet
Archive fragments:
- `archive/scratch_recovery/test_clifford.lean`
- `archive/scratch_recovery/test_functor.lean`
- `archive/scratch_recovery/test_comp.lean`
- `archive/scratch_recovery/test_functor_proofs.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/OperatorAlgebra/CliffordInfinityCAR.lean`
- `lean/InfoGeometry/OperatorAlgebra/CliffordInfinityCommutation.lean`
- `lean/InfoGeometry/Canonical/SplitCliffordDirectLimit.lean`
- `lean/InfoGeometry/Topology/CantorCliffordFunctor.lean`
- historical aliases/consumers such as `lean/InfoGeometry/Clifford/CliffordInjectivity.lean` and `lean/InfoGeometry/Clifford/CliffordInclusionInjective.lean`

Observed relation:
- `test_clifford.lean` is essentially restored live in `CliffordInfinityCAR.lean`, including `V_inclusion`, `V_inclusion_is_isometry`, `Cl_bonding_map`, `Cl_bonding_map_of_le`, `Cl_bonding_map_of_le_self`, `Cl_bonding_map_of_le_comp`, `Cl_functor`, and `CliffordInfinity`
- the canonical owner `SplitCliffordDirectLimit.lean` is a stronger modernized direct-limit lane with `splitCliffordStep`, `splitCliffordStep_injective`, `splitCliffordMap`, `splitCliffordDirectedSystem`, and `SplitCliffordInfinity`
- `test_functor.lean` and `test_functor_proofs.lean` are restored live in `CantorCliffordFunctor.lean`, including `V`, `V_inclusion_mn`, `Cl`, `Cl_bonding_map_mn`, `J`, and `CliffordTowerFunctor`
- `test_comp.lean` and `test_functor_proofs.lean` are weaker/probe versions of the same composition and functoriality work; the archive proof probes include `sorry`s where live owner proofs are complete
- additional related but non-owner abstractions exist in `lean/InfoGeometry/Sandbox/CliffordFunctorSandbox/Functor.lean` and `lean/InfoGeometry/Algebra/DirectLimitSuperClosureLemmas.lean`

Conclusion:
- already restored live in exact/historical and stronger canonical forms
- do not duplicate

### 2.14 Real upper-half-plane / Möbius shadow and Möbius-Weyl signature packets
Archive fragments:
- `archive/scratch_recovery/test4_fixed.lean`
- `archive/scratch_recovery/test4.lean`
- `archive/scratch_recovery/temp_moebius.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/Geometry/RealMoebiusAction.lean`
- `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean`
- `lean/InfoGeometry/Arithmetic/MoebiusSignature.lean`
- downstream arithmetic users such as `lean/InfoGeometry/Arithmetic/MasterIdentity.lean`

Observed relation:
- `test4_fixed.lean` is restored live as the real Möbius action/shadow lane: `SL2R`, coordinate accessors, `denomSq`, `realDenomSq_pos`, `moebius`, `toComplex`, and `toComplex_moebius`
- the live real action is stronger than the scratch fragment because it also proves action laws such as `one_smul_real` and `mul_smul_real`
- `temp_moebius.lean` is restored live as `MoebiusSignature.lean`, including `weylToNat`, `weyl_toNat_squarefree`, and `weyl_sign_eq_moebius`

Conclusion:
- already restored live in stronger owner files
- do not duplicate

### 2.15 Grothendieck--Riemann--Roch sandbox packet
Archive fragment:
- `archive/scratch_recovery/test_grr.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/Sandbox/GrothendieckRiemannRoch.lean`
- `lean/InfoGeometry/Sandbox/GRRSandbox.lean`

Observed relation:
- `test_grr.lean` is restored essentially verbatim in `GrothendieckRiemannRoch.lean`, including `K0Group`, `CohomologyRing`, `K0Pushforward`, `CohomologyPushforward`, `ChernCharacter`, `ToddClass`, `GrothendieckRiemannRoch`, and `m2_positroid_todd_class`
- `GRRSandbox.lean` is a related smaller sandbox formulation with `EvenCohomology`, `GRRTheorem`, and the native lemma `grr_preserves_zero`
- the live files explicitly mark general constructive GRR as open debt rather than pretending full theorem closure

Conclusion:
- already restored live as sandbox material
- do not duplicate

### 2.16 D4 triality / Q8 automorphism packet
Archive fragment:
- `archive/scratch_recovery/test_q8_aut.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Topology/D4TrialityQ8Equivalence.lean`

Observed relation:
- the archive namespace `InfoGeometry.Topology.D4Triality` is restored live under the same namespace
- live declarations exactly include `triality_omega`, `triality_omega_order_three`, `triality_sigma`, `triality_sigma_order_two`, and `triality_braiding_relation`
- downstream Q8 context exists in `Q8MonodromySpinorCover.lean`, `Q8ModularFlowBridge.lean`, and `Q8V4SchurBridge.lean`

Conclusion:
- already restored live exactly
- do not duplicate

### 2.17 D-brane matrix factorization packets
Archive fragments:
- `archive/scratch_recovery/test_dbrane.lean`
- `archive/scratch_recovery/test_d4_brane.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/Topology/DBraneMatrixFactorization.lean`
- `lean/InfoGeometry/Topology/D4SingularityDBrane.lean`

Observed relation:
- `test_dbrane.lean` is restored live as `DBraneMatrixFactorization.lean`, including `MatrixFactorization`, `pauli_momentum`, `pauli_adjugate`, and `pauli_is_dbrane_factorization`
- `test_d4_brane.lean` is restored live as `D4SingularityDBrane.lean`, including `D4_superpotential`, `D4MatrixFactorization`, and `d4_factorization_respects_q8`
- both live files are imported by `lean/InfoGeometry/Topology/All.lean`

Conclusion:
- already restored live exactly
- do not duplicate

### 2.18 Kawamura Cuntz/CAR zeta packet
Archive fragment:
- `archive/scratch_recovery/test_kawamura.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Algebra.lean`
- backing carrier: `lean/InfoGeometry/Topology/CuntzCantorSpectralTriple.lean`

Observed relation:
- archive `kawamuraZeta_star` is restored live as `InfoGeometry.Algebra.kawamuraZeta_star`
- archive `kawamuraZeta_mul` claims `ζ(x) * ζ(y) = ζ(x*y)`
- live owner instead proves the corrected theorem `kawamuraZeta_mul_zeta : ζ(x) * ζ(y) = ρ(x*y)`, where `ρ` is the plus-sign Cuntz endomorphism `kawamuraRho`
- the live file continues with reusable small lemmas `kawamuraRho_add`, `kawamuraRho_one`, `kawamuraRho_zero`, and CAR induction theorems

Conclusion:
- corrected live owner supersedes the archive probe
- do not restore the archive `kawamuraZeta_mul` theorem as written, because it overclaims the multiplicativity target
- do not duplicate

### 2.19 Split Clifford inclusion isometry probe
Archive fragment:
- `archive/scratch_recovery/scratch_test_isometry.lean`

Live owner lane already exists:
- `lean/InfoGeometry/OperatorAlgebra/CliffordInfinityCAR.lean`
- stronger/categorical related lane: `lean/InfoGeometry/Topology/CantorCliffordFunctor.lean`

Observed relation:
- the archive fragment contains only `V_inclusion` and `V_inclusion_is_isometry`
- these are already restored live in the Clifford infinity CAR lane and are part of the larger split-Clifford tower/direct-limit restoration recorded above
- the fragment is a smaller extraction/proof probe of the same inclusion-isometry kernel, not a separate missing owner surface

Conclusion:
- already restored live as part of the Clifford tower packet
- do not duplicate

### 2.20 Moore--Penrose closed-range construction packets
Archive fragments:
- `archive/scratch_recovery/sandbox_mp.lean`
- `archive/scratch_recovery/sandbox_mp_final.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Singular/MoorePenrose.lean`
- adapter lane: `lean/InfoGeometry/Singular/MoorePenroseAdjoint.lean`

Observed relation:
- archive fragments contain `IsMoorePenroseInverse` and a Hilbert endomorphism closed-range existence theorem `exists_moorePenroseInverse_of_closedRange`
- the live owner is stronger and smaller-lemma divided: it includes `IsMoorePenroseInverse`, projection lemmas, uniqueness, `IsMoorePenroseInverseCLM`, `mpRestricted`, `mpRestricted_injective`, `mpRestricted_surjective`, `mpEquiv`, constructive `moorePenroseInverse`, `isMoorePenroseInverse_moorePenroseInverse`, and the legacy wrapper `exists_moorePenroseInverse_of_closedRange`
- the live construction generalizes the archive endomorphism-only theorem to rectangular continuous linear maps between Hilbert spaces and then recovers the endomorphism wrapper

Conclusion:
- already restored live in a stronger, reusable, lemma-divided owner
- do not duplicate

### 2.21 Complex bounded-operator finite-matrix verification packet
Archive fragment:
- `archive/scratch_recovery/sandbox_cbo_verification.lean`

Live owner lane already exists:
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean`
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/CblinfunMatrix.lean`

Observed relation:
- archive fragment defines `ketBasis` and a theorem `reproduce_failure` proving `matrixOp (LinearMap.toMatrix ... T.toLinearMap) = T`
- live `CblinfunMatrix.lean` contains the same kernel as clean reusable definitions `ketBasis`, `matrixOfOp`, `matrixOp` and the theorem `matrixOp_matrixOfOp`
- live owner also proves the converse `matrixOfOp_matrixOp`, injectivity, zero/add/id/comp laws, and adjoint compatibility

Conclusion:
- already restored live in a stronger finite-matrix adapter
- do not duplicate

### 2.22 Generic product-carrier injection probes
Archive fragments:
- `archive/scratch_recovery/test_inj.lean`
- `archive/scratch_recovery/test_inj2.lean`
- `archive/scratch_recovery/test_inj3.lean`
- related small probes: `test_equiv.lean`, `test_equiv2.lean`, `test_addcomm*.lean`

Live owner context:
- no domain owner should be created for the scratch `Foo` type
- the pattern is already used concretely in owner code such as `lean/InfoGeometry/Algebra/K0FibonacciRing.lean` via `FibRing.toProd` and `toProd_injective`

Observed relation:
- these archive files are generic Mathlib probes for deriving algebraic structure through an injective map to a product
- they are not lost mathematical physics owner code
- if the pattern is needed later, it should be instantiated for a concrete carrier rather than restored as a parallel `Foo` module

Conclusion:
- throwaway proof probes / reusable method note only
- do not write a recovered Lean owner file

### 2.23 Cantor/Clifford direct-limit bridge packet
Archive fragment:
- `archive/scratch_recovery/test_limit.lean`

Live owner context:
- imports and depends on `lean/InfoGeometry/Clifford/MatToCantorOperator.lean`
- imports and depends on `lean/InfoGeometry/Clifford/RealCantorOpLimit.lean`
- imports and depends on `lean/InfoGeometry/Clifford/Cl11TensorTowerLimit.lean`
- no exact live declarations `fwdHom` / `revHom` were found in the maintained `lean/` tree

Recovered sandbox file:
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/CantorCliffordLimitBridgeRecovered.lean`

Recovered declarations:
- `InfoGeometry.Recovered.CantorCliffordLimitBridge.fwdHom`
- `InfoGeometry.Recovered.CantorCliffordLimitBridge.revHom`

Verification:
- `lake env lean tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/CantorCliffordLimitBridgeRecovered.lean`
- result: exit code 0, with only pre-existing Lake manifest/package warnings

Conclusion:
- genuinely archive-only direct-limit bridge kernel recovered into sandbox form
- live owner files were not overwritten

### 2.24 Bernstein--Sato spectral stability packet
Archive fragment:
- `archive/scratch_recovery/test_spectral.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Sandbox/SpectralStabilitySandbox.lean`

Observed relation:
- archive definitions `BernsteinSato` and `spectral_stability_step` are already present live under the same theorem shape
- live file records the same roots-under-divisibility kernel in a named sandbox owner

Conclusion:
- already restored live
- do not duplicate

### 2.25 Jordan--Wigner Cantor homomorphism proof probe
Archive fragment:
- `archive/scratch_recovery/test_hom_proofs.lean`

Live owner lane already exists / supersedes the probe:
- `lean/InfoGeometry/Canonical/JordanWignerCantorRepresentation.lean`
- supporting lane: `lean/InfoGeometry/Canonical/JordanWignerCelikKocakBridgeNDepth.lean`

Observed relation:
- archive file contains `idxEquivCantorAddress`, `complexifyMat`, and a sorry-bearing `map_mul_proof`
- live owner has completed, stronger declarations: `fin2EquivBool`, `idxEquivCantorAddress`, `complexifyMatrixAlgHom`, `complexMatToMatrix`, `complexMatToCantor`, `complexMatToCantor_map_mul`, and `complexMatToCantor_injective`
- the live surface avoids the archive's local monolithic multiplication proof by packaging complexification/reindexing as algebra homomorphisms

Conclusion:
- archive probe is superseded by completed live owner code
- do not restore the sorry-bearing probe

### 2.26 Multiaffine linearity proof sketch
Archive fragment:
- `archive/scratch_recovery/sandbox_multiaffine_linearity.lean`

Live context:
- related theorem shape is discussed as explicit closure debt in `lean/InfoGeometry/Canonical/LeeYangAsanoDigest.lean`
- no exact live theorem `multiaffine_linearity` was found

Verification of archive fragment:
- `lake env lean archive/scratch_recovery/sandbox_multiaffine_linearity.lean`
- result: failed; unknown constant `Finsupp.prod_eq_prod_univ`, plus a stalled simplification step

Conclusion:
- do not restore as compiling code in this pass
- classify as a useful but incomplete proof sketch for a future isolated lemma task
- future proof task should isolate the single theorem `degreeOf i P ≤ 1 → ∃ a b, ∀ x, eval (Function.update z i x) P = a + b * x`, search current mathlib MvPolynomial APIs, and prove it in a separate file before any owner import

### 2.27 Jordan--Wigner base-case and manual hom probes
Archive fragments:
- `archive/scratch_recovery/test_base_case_eval2.lean`
- `archive/scratch_recovery/test_base_case.lean`
- `archive/scratch_recovery/test_base_case_eval.lean`
- `archive/scratch_recovery/test_manual_hom.lean`

Live owner context:
- `lean/InfoGeometry/Canonical/JordanWignerCantorRepresentation.lean`
- `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`

Observed relation:
- `test_manual_hom.lean` is superseded by the live algebra-hom packaging `complexifyMatrixAlgHom`, `complexMatToMatrix`, `complexMatToCantor`, and `complexMatToCantor_map_mul`
- the base-case archive probes refer to stale names such as `IsJWCantorRepresentation`, `buildCantorRep`, and `complexifyMat` after current owner refactoring
- the live `Cl11TensorTower.lean` still contains a theorem named `buildCantorRep_one_is_jw_rep`, but with explicit `sorry` gaps; the archive proof does not compile against the current owner surface

Verification:
- `lake env lean archive/scratch_recovery/test_base_case_eval2.lean` failed because `IsJWCantorRepresentation` is unknown in the imported namespace/current surface
- `lake env lean archive/scratch_recovery/test_manual_hom.lean` failed because `complexifyMat` is unknown in the current surface

Conclusion:
- do not paste these stale probes into live owners
- classify as stale proof attempts after owner refactor
- if the base-case theorem is prioritized, isolate the current live theorem statement from `Cl11TensorTower.lean` into a fresh minimal proof file and give it as one precise lemma task; do not use the stale archive script directly

### 2.28 Finite matrix dot-product transpose probe
Archive fragment:
- `archive/scratch_recovery/test_dot.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/FiniteMatrix.lean`
- `lean/InfoGeometry/OperatorAlgebra/ComplexBoundedOperators/ExtraJordanNormalForm.lean`

Observed relation:
- archive proves a rational transpose dot-product identity using stale `Matrix.dotProduct`
- live owner has the stronger complex adjoint identity `dotProduct_conjTranspose_mulVec` and adapter theorem `cscalar_prod_adjoint`
- related real transpose identities also appear in Omega local-space quadratic files using current mathlib lemmas `dotProduct_mulVec` and `vecMul_transpose`

Verification:
- `lake env lean archive/scratch_recovery/test_dot.lean` failed because `Matrix.dotProduct` is no longer a valid constant in that namespace/API

Conclusion:
- already live/superseded by stronger finite-matrix adjoint corridor
- do not duplicate stale proof probe

### 2.29 Braid/Yang--Baxter skeleton probe
Archive fragment:
- `archive/scratch_recovery/test_braid.lean`

Live owner lanes already exist:
- `lean/InfoGeometry/GrandUnification/CelikErlangenBraidBridge.lean`
- `lean/InfoGeometry/Categorical/FibonacciBraidedTowerCone.lean`
- `lean/InfoGeometry/Categorical/CelikZ3FibonacciCuntzBoundaryBridge.lean`

Observed relation:
- archive only sketches a `BraidGenerator` structure with comments for `R12`, `R23`, and Yang--Baxter; it contains no theorem
- live files contain theorem-backed finite and categorical Yang--Baxter surfaces, including `yang_baxter_braid_relation`, `fibonacci_yang_baxter_iso`, and finite complex Fibonacci matrix Artin/Yang--Baxter readouts

Conclusion:
- archive is a conceptual sketch, not lost compiling owner code
- do not restore as a parallel structure

### 2.30 Semantic reflector adjunction probe
Archive fragment:
- `archive/scratch_recovery/test_reflector.lean`

Live owner lane already exists:
- `lean/InfoGeometry/Epistemology/SemanticReflector.lean`

Observed relation:
- archive theorem `repaired_type_is_minimal_and_sound` is the same adjunction universal-property idea as live `repaired_type_is_minimal`
- the live owner also provides `repairUnit` and `repairCounit` and has current universe/category annotations

Verification:
- `lake env lean archive/scratch_recovery/test_reflector.lean` failed because the old proof used a `left_inv` orientation that no longer matches the current `Equiv` API; the live file has the corrected proof shape

Conclusion:
- already restored live in corrected form
- do not duplicate

### 2.31 Architecture tag depth diagnostics
Archive fragments:
- `archive/scratch_recovery/check_depth.lean`
- `archive/scratch_recovery/debug_tags.lean`

Live owner context:
- `lean/InfoGeometry/Meta/Architecture.lean`
- `lean/InfoGeometry/Canonical/CasimirWeylDrazinContext.lean`
- generated registry context such as `lean/InfoGeometry/auto_blueprints.lean`

Observed relation:
- these files are local diagnostics for querying `repDepth?` on `CasimirWeylDrazinData`
- they are not theorem-bearing owner files
- the live architecture tagging system already owns the `@[rep_depth ...]` infrastructure and generated blueprint registration

Verification:
- `lake env lean archive/scratch_recovery/check_depth.lean` failed on stale `Lean.importModules` syntax / module-import object notation
- `lake env lean archive/scratch_recovery/debug_tags.lean` failed because `CoreM` was not opened/imported in the current surface

Conclusion:
- diagnostic scripts only; no recovered Lean owner file justified
- if needed later, rewrite as a maintained tool/script rather than owner theorem code

### 2.32 Projective CCR and chiral null-space axiom/check probes
Archive fragments:
- `archive/scratch_recovery/scratch_trace_axiom.lean`
- `archive/scratch_recovery/scratch_axioms.lean`
- `archive/scratch_recovery/scratch_axioms_final.lean`

Live owner context:
- `lean/InfoGeometry/Canonical/ProjectiveCCR.lean`
- `lean/InfoGeometry/Canonical/ChiralNullSpaceBridge.lean`

Observed relation:
- `scratch_trace_axiom.lean` checks the theorem readback `ProjectiveBoundaryPacket.zeroMode.vacuum_eq_one`
- `scratch_axioms*.lean` are `#print axioms` probes, not lost theorem code
- these are audit diagnostics for dependency/axiom surfaces, not independent mathematical kernels

Verification:
- `lake env lean archive/scratch_recovery/scratch_trace_axiom.lean` failed only because the old option `trace.Meta.Tactic.axiom` is no longer recognized; the theorem statement itself reads directly from the live packet field

Conclusion:
- diagnostic/check probes only
- do not restore as owner code
- future axiom audits should use maintained repo-native audit tooling rather than scratch `#print axioms` files

### 2.33 Cantor/Clifford limit ring-equivalence proof sketch
Archive fragment:
- `archive/scratch_recovery/test_limit2.lean`

Live owner context:
- `lean/InfoGeometry/Clifford/RealCantorOpLimit.lean`
- recovered forward/reverse maps already exist in `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/CantorCliffordLimitBridgeRecovered.lean`

Observed relation:
- the archive extends the forward/reverse direct-limit lifts toward a `ringEquiv`
- no exact live `matToCantorLift`, `cantorToMatLift`, or `ringEquiv : Cl11TensorTowerLimit.Limit ≃+* RealCantorOpLimit.Limit` was found in the maintained `lean/` tree
- the forward/reverse lift content was already recovered as `fwdHom` and `revHom`

Verification:
- `lake env lean archive/scratch_recovery/test_limit2.lean` failed because `DirectLimit.induction_on` is stale/unknown; the current repo direct-limit eliminator is the custom `DirectLimit.induction` used by owner files

Conclusion:
- do not restore the non-compiling `ringEquiv` proof as-is
- classify as future isolated lemma work: prove the two inverse laws for the recovered `fwdHom`/`revHom` using the current `DirectLimit.induction` API, then expose a separate imported `RingEquiv` file if the proof checks

### 2.34 Mathlib/API sanity probes
Archive fragments:
- `archive/scratch_recovery/check_identifiers.lean`
- `archive/scratch_recovery/scratch_bh_demo.lean`
- `archive/scratch_recovery/test_limits.lean`
- `archive/scratch_recovery/test_kldiv.lean`
- `archive/scratch_recovery/test_ringhom.lean`
- `archive/scratch_recovery/test_ring_colimit.lean`
- `archive/scratch_recovery/test_leRec.lean`
- `archive/scratch_recovery/test_matrix_alg_hom.lean`
- `archive/scratch_recovery/test_toLin.lean`
- `archive/scratch_recovery/test_basis_map.lean`
- `archive/scratch_recovery/test_basis_reindex.lean`
- `archive/scratch_recovery/test_matrix_reindex.lean`
- `archive/scratch_recovery/test_matrix_to_lin.lean`
- `archive/scratch_recovery/test_toLinAlgHom.lean`
- `archive/scratch_recovery/test_zeta.lean`
- `archive/scratch_recovery/check_mul.lean`
- `archive/scratch_recovery/test_basis.lean`

Observed relation:
- these files are zero-declaration or `example`/`#check` probes for current Mathlib names and APIs
- examples include determinant API checks, continuous-linear-map adjoint names, ring-colimit imports, basis/reindex/toLin probes, KL-divergence imports, zeta imports, and matrix multiplication probes

Verification:
- `lake env lean archive/scratch_recovery/check_identifiers.lean` succeeded and printed current `ContinuousLinearMap.adjoint_inner_left/right` declarations
- `lake env lean archive/scratch_recovery/scratch_bh_demo.lean` succeeded for `Matrix.det_mul` and `Matrix.det_smul`

Conclusion:
- useful historical lookup notes, not lost owner code
- do not create recovered Lean owner files for these probes

### 2.35 Generic additive product-carrier derivation probes
Archive fragments:
- `archive/scratch_recovery/test_addcomm.lean`
- `archive/scratch_recovery/test_addcomm2.lean`
- `archive/scratch_recovery/test_addcomm4.lean`
- `archive/scratch_recovery/test_derive.lean`

Live owner context:
- already covered by the generic product-carrier/injection-probe classification in section 2.22
- concrete owner uses should be instantiated in domain files rather than recovered as a scratch `Foo` type

Observed relation:
- these files manually derive or attempt deriving `AddCommGroup` for a two-field product structure `Foo`
- the mathematical content is simply the standard product additive group structure

Conclusion:
- generic Mathlib/prototype probes only
- do not restore as owner code

### 2.36 Real upper-half-plane algebra normalization probes
Archive fragments:
- `archive/scratch_recovery/test2.lean`
- `archive/scratch_recovery/test3.lean`

Live owner context:
- already covered by section 2.14 real upper-half-plane / Möbius shadow owners
- current owner files include `lean/InfoGeometry/Geometry/RealMoebiusAction.lean` and `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean`

Observed relation:
- both files are unnamed `example` algebra-normalization checks for real Möbius/upper-half-plane coordinate formulas
- `test2.lean` is a denominator/numerator expansion by `ring`
- `test3.lean` is an imaginary-part numerator simplification using determinant hypothesis `a*d - b*c = 1`

Verification:
- `lake env lean archive/scratch_recovery/test2.lean` succeeded, with only unused-variable warnings
- `lake env lean archive/scratch_recovery/test3.lean` succeeded, with only unused-variable warnings

Conclusion:
- useful proof-local arithmetic checks, but not named owner code
- do not create a separate recovered owner file; the named Möbius owner lanes already carry the theorem surfaces

### 2.37 Moore--Penrose and Zorn/Dirac Souriau smoke tests
Archive fragments:
- `archive/scratch_recovery/sandbox_mp_test.lean`
- `archive/scratch_recovery/sandbox_test_zorn.lean`

Live owner context:
- Moore--Penrose already covered by section 2.20 under `lean/InfoGeometry/Singular/MoorePenrose.lean`
- Zorn/Dirac Souriau surfaces live under `lean/InfoGeometry/Canonical/DiracSouriauOperator.lean`

Observed relation:
- `sandbox_mp_test.lean` imports a vanished local scratch module `sandbox_mp_authoritative` and merely smoke-tests the closed-range existence theorem on identity/general operators
- `sandbox_test_zorn.lean` checks instances for `ZornMatrix ℝ`, the `coarseGrain` definitional equation, and `DiracSouriauSector.hasDrazinInverse_of_field`

Verification:
- `lake env lean archive/scratch_recovery/sandbox_mp_test.lean` failed because `sandbox_mp_authoritative` is not a maintained module prefix
- `lake env lean archive/scratch_recovery/sandbox_test_zorn.lean` succeeded

Conclusion:
- smoke tests only; owner content is already live or superseded
- do not restore as owner code

### 2.38 Virasoro local API/change probes
Archive fragments:
- `archive/scratch_recovery/test_change.lean`
- `archive/scratch_recovery/debug_ite.lean`

Live owner context:
- `lean/InfoGeometry/External/Virasoro/CentralExtension.lean`
- `lean/InfoGeometry/External/Virasoro/VirasoroAlgebra.lean`
- `lean/InfoGeometry/OperatorAlgebra/AffineVirasoroBridge.lean`
- related finite/infinite mode bridge declarations in `lean/InfoGeometry/Algebra/FiniteInfiniteModeBridge.lean`

Observed relation:
- `test_change.lean` contains only a comment about a possible `change` target for central-extension simplification
- `debug_ite.lean` is a pretty-printer/debug proof sketch for moving scalar multiplication through an `if` involving a Virasoro central generator

Verification:
- `lake env lean archive/scratch_recovery/test_change.lean` failed because old namespace `CentralExtension` is not current
- `lake env lean archive/scratch_recovery/debug_ite.lean` failed because `VirasoroAlgebra.cgen` is not the current referenced name in that namespace/import surface

Conclusion:
- stale local API/debug probes only
- do not restore as owner code; if needed, isolate the current Virasoro theorem statement from the live owner and prove that precise lemma

### 2.39 Hestenes phase-head square proof sketch
Archive fragment:
- `archive/scratch_recovery/test_phase.lean`

Live owner context:
- `lean/InfoGeometry/Clifford/Cl11TensorTower.lean`
- related first-stage readback in `lean/InfoGeometry/Clifford/Cl11InfiniteCarrier.lean`

Observed relation:
- archive sketches a proof of `hestenesPhaseHead n * hestenesPhaseHead n = -1` for all `n`, with one `sorry` at the tensor-embedding negative/unit preservation step
- live owner currently has `hestenesPhaseBase_sq`, `hestenesPhaseHead`, and `matStageEmbed_mul`; `Cl11InfiniteCarrier.lean` proves the first-stage `phaseAxisStage_sq`

Verification:
- `lake env lean archive/scratch_recovery/test_phase.lean` failed with an unsolved goal at the final embedding/negation step

Conclusion:
- not restored as compiling code
- classify as a future isolated lemma task: prove the general `hestenesPhaseHead` square theorem in a separate minimal file using current `matStageEmbed`/Kronecker API, then import if needed

### 2.40 KK ontology field-name check
Archive fragment:
- `archive/scratch_recovery/sandbox_ontology_check.lean`

Live owner context:
- `lean/InfoGeometry/KK/RealSplitKreinKasparovCycle.lean`
- `lean/InfoGeometry/KK/DiracFredholmModule.lean`
- `lean/InfoGeometry/KK/RealSplitKreinBoundedTransform.lean`

Observed relation:
- the archive tries to construct `RealSplitKreinDiracFredholmModule` with many `sorry`s only to discover current field names
- live primitive owner is `RealSplitKreinKasparovCycle`; `RealSplitKreinDiracFredholmModule` is a canonical abbrev in `DiracFredholmModule.lean`
- current field names include `cl11`, `π`, `ρ`, `π_even`, `ρ_even`, `F`, `F_odd`, `F_skewAdj`, `F_sq_one_compact`, `comm_compact`, `superComm_eps_compact`, and `superComm_J_compact`

Verification:
- `lake env lean archive/scratch_recovery/sandbox_ontology_check.lean` failed because necessary typeclass instances for the proposed abstract carrier were not supplied, in addition to the intentional `sorry`s

Conclusion:
- ontology/field-name diagnostic only, not theorem closure
- do not restore as owner code; use live primitive owner files as the source of truth

## 3. Archive-only or not-yet-mapped candidates

These are the best candidates for future non-overwriting recovery files, because this round did not find a direct stronger live owner surface.

Examples:
- `archive/scratch_recovery/Parafermion.lean` (now recovered into sandbox form)
- `archive/scratch_recovery/sandbox_alghom_verification.lean` (now recovered into sandbox form)
- `archive/scratch_recovery/test_sum_prod.lean` (now recovered into sandbox form as a generic finite-assignment product-sum lemma)

Recovered sandbox files currently include:
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Parafermion/ParafermionCarrierRecovered.lean`
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/ScalarAlgHomRecovered.lean`
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/FiniteAssignmentProductSumRecovered.lean`
- `tools/multisystem/major_restore_non_overwriting/lean/InfoGeometry/Recovered/CantorCliffordLimitBridgeRecovered.lean`

Caution:
- some of these may still be duplicates under renamed live files
- some are probe/test files rather than owner-surface losses
- some contain `sorry` or temporary proof sketches

## 4. Next truthful restoration move

Round 2 should only target the archive-only candidates above.

For each candidate:
1. read the full archive file
2. search the live repo for direct namespace/theorem equivalents
3. if absent, write a NEW recovery file under a non-canonical sandbox path
4. split into small reusable lemmas
5. keep any unresolved theorem as explicit open debt, not a fake closure

Recommended non-canonical destination pattern:
- `tools/multisystem/major_restore_non_overwriting/lean/...Recovered.lean`

## 5. Important boundary

This round is a recovery index, not a claim that all lost code has already been fully reconstructed. It establishes:
- where the recoverable material lives
- which major archive lanes are already live and should not be duplicated
- which archive-only lanes remain candidates for careful reconstruction
