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

## 3. Archive-only or not-yet-mapped candidates

These are the best candidates for future non-overwriting recovery files, because this round did not find a direct stronger live owner surface.

Examples:
- `archive/scratch_recovery/Parafermion.lean` (now recovered into sandbox form)
- `archive/scratch_recovery/sandbox_alghom_verification.lean` (now recovered into sandbox form)

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
