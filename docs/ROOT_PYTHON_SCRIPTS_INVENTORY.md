# Root & Subdirectory Ad-Hoc Python Scripts Inventory (`QMS-INV-PY-001`)

| QMS Metadata Field | Value |
|---|---|
| **Document ID** | `QMS-INV-PY-001` |
| **Governing Plan & SOP** | [`docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md`](file:///home/goutev/repos/info-geometry-lean/docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md) (`QMS-PLAN-PIPE-001` v2.0, Phase 2.1 `CAPA-007`), [`docs/ALCHEMICAL_QMS_SOP.md`](file:///home/goutev/repos/info-geometry-lean/docs/ALCHEMICAL_QMS_SOP.md) (`QMS-SOP-ALC-001` v4.1) |
| **Observed Checkout `HEAD`** | `bd894d16014e7a006c24376399694c272b497733` |
| **Authority Level** | Level 3–4 (`[qms_document_controlled]`) auditing Level 5 workspace scripts |
| **Destructive Action Guard (`CAPA-007`)** | **Read-only inventory by default.** Zero root or subdirectory `.py` scripts may be deleted (`rm`/`git rm`) or moved (`git mv`) without explicit user authorization. |

---

## 1. Executive Summary

An exhaustive repository audit identified **120 ad-hoc `.py` scripts at the repository root** (`118` git-tracked, `2` untracked) and **62 additional `fix_*.py` / `patch_*.py` scripts in active subdirectories** (`proofs/`, `tools/`, `tools/infra/`, `tools/python/`, plus `1` already archived in `archive/scratch_recovery/fix_virasoro.py`):

| Scope | `fix_*.py` | `patch_*.py` | Other Ad-Hoc `.py` | Total Scripts | Git-Tracked | Untracked | Imported by Maintained Tools/Tests | Archival Status |
|---|---:|---:|---:|---:|---:|---:|---|---|
| **Repository Root (`./*.py`)** | 32 | 45 | 43 | **120** | 118 | 2 (`patch.py`, `patch_file.py`) | **0** | **Archived to `archive/root_scripts_2026_11/`** (Phase 2.2, user-approved) |
| **Active Subdirectories (`proofs/`, `tools/**`)** | 54 | 8 | — | **62** | 62 | 0 | **0** | Not archived (still under active use) |
| **Existing Archive (`archive/scratch_recovery/`)** | 1 | 0 | — | **1** | 1 | 0 | **0** | Already archived |

Repository-wide lexical and AST import searches across `tools/`, `scripts/`, `tests/`, `src/`, `extensions/`, `.github/`, and `.githooks/` confirm that **zero maintained modules, CLI entrypoints, hooks, or tests import or invoke any of the 120 root `.py` scripts**. All 120 have been archived to `archive/root_scripts_2026_11/` with user approval per CAPA-007.

Repository root `*.py` count: **0** (all archived).

---

## 2. Classification of All 120 Repository Root `.py` Scripts

### 2.1 Category A — One-Off Hardcoded Lean File String-Patchers, Tacticians & Viewers (111 Scripts)

All 111 Category A scripts read or mutate hardcoded `.lean` file paths via string/regex replacement from past proof-repair sessions. All target `.lean` files have since been promoted or superseded in git history.

#### A.1 Targeting `lean/DAG/MatrixGaussJordan.lean` (26 Scripts — All Superseded by Commit `ee2dd4ad7d`)
| Script | Lines | Git Status | Prefix Group | Disposition |
|---|---:|---|---|---|
| `debug.py` | 17 | Tracked | Other | Archived to `archive/root_scripts_2026_11/` |
| `fix_29.py` | 10 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_all.py` | 33 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_all2.py` | 33 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_all_clean.py` | 18 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_all_warnings.py` | 25 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_deprecations.py` | 15 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_final.py` | 23 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_missed.py` | 26 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_options.py` | 17 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_regex.py` | 26 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_rw_dite.py` | 35 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_simpa.py` | 18 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_warnings.py` | 15 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `get_lines.py` | 7 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `make_final_fix.py` | 47 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `precise_fix_warnings.py` | 37 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `show_warns.py` | 6 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `test_erw.py` | 22 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `test_fix.py` | 9 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `ultimate_fix.py` | 67 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `view_29.py` | 4 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `view_947.py` | 4 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `view_errors.py` | 8 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `view_rem.py` | 10 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `view_rw.py` | 10 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |

#### A.2 Targeting `lean/InfoGeometry/Clifford/SplitOctonionChiralMatrixProduct.lean` (27 Scripts — All Superseded)
| Script | Lines | Git Status | Prefix Group | Disposition |
|---|---:|---|---|---|
| `clean_file.py` | 66 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `dump_type.py` | 8 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `fix_blocks.py` | 17 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_tactics.py` | 17 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `fix_tactics2.py` | 10 | Tracked | `fix_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch3.py` | 37 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `patch_61.py` | 21 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_change.py` | 37 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_chiral_stars.py` | 13 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_conjunction.py` | 17 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_exact.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_exact2.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_exact_hard.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_ext.py` | 15 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_field_simp.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_file.py` | 37 | **Untracked** | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_half.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_helper.py` | 18 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_lemma.py` | 21 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_linarith.py` | 12 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_norm.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_norm_num.py` | 15 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_ppall.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_show.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `patch_show2.py` | 11 | Tracked | `patch_*.py` | Retire to `archive/root_scripts_2026_11/` |
| `test_chiral.py` | 31 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |
| `test_tactic_order.py` | 15 | Tracked | Other | Retire to `archive/root_scripts_2026_11/` |

#### A.3 Targeting `lean/InfoGeometry/Canonical/ThreeModeCARHodgeLaplacianBridge.lean` & `SplitOctonionJordanStructure.lean` (20 Scripts — All Superseded)
| Script | Lines | Git Status | Prefix Group | Target File(s) |
|---|---:|---|---|---|
| `fix_all_goals.py` | 28 | Tracked | `fix_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch7.py` | 22 | Tracked | Other | `SplitOctonionJordanStructure.lean` |
| `patch_car.py` | 32 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car2.py` | 12 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car3.py` | 29 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car4.py` | 9 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car5.py` | 18 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car6.py` | 15 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car7.py` | 20 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car8.py` | 54 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car9.py` | 38 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car10.py` | 25 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car12.py` | 79 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car13.py` | 10 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car14.py` | 61 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car15.py` | 113 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_car16.py` | 28 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_final.py` | 24 | Tracked | `patch_*.py` | `SplitOctonionJordanStructure.lean`, `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_final2.py` | 18 | Tracked | `patch_*.py` | `SplitOctonionJordanStructure.lean`, `ThreeModeCARHodgeLaplacianBridge.lean` |
| `patch_final_car.py` | 75 | Tracked | `patch_*.py` | `ThreeModeCARHodgeLaplacianBridge.lean` |

#### A.4 Targeting `lean/InfoGeometry/GrandUnification/KleinParabolicPeirceTwist.lean` (8 Scripts — All Superseded)
`scratch_rewrite.py` (20L), `scratch_rewrite2.py` (11L), `scratch_rewrite3.py` (107L), `scratch_rewrite4.py` (77L), `scratch_rewrite5.py` (77L), `scratch_rewrite6.py` (93L), `scratch_rewrite7.py` (7L), `scratch_twist.py` (19L).

#### A.5 Targeting `lean/InfoGeometry/Topology/AlgebraicCuntzQuotient.lean` (5 Scripts — All Superseded)
`clean_cuntz.py` (10L), `fix_cuntz_args.py` (10L), `fix_cuntz_final.py` (15L), `fix_cuntz_types.py` (14L), `test_cuntz.py` (7L).

#### A.6 Targeting `lean/Omega/POM/MaxFiberAchieversHiddenBitProbSpectrum.lean` (3 Scripts — All Superseded)
`patch4.py` (59L), `patch5.py` (39L), `patch6.py` (34L).

#### A.7 Other Single-File Lean Patchers (22 Scripts — All Superseded)
| Script | Lines | Git Status | Prefix Group | Hardcoded Target `.lean` File |
|---|---:|---|---|---|
| `fix.py` | 8 | Tracked | Other | `test_quantum_plane.lean` |
| `fix_braid.py` | 39 | Tracked | `fix_*.py` | `lean/InfoGeometry/Canonical/SylvesterGrading.lean` |
| `fix_causal.py` | 25 | Tracked | `fix_*.py` | `lean/InfoGeometry/Canonical/CausalConeProjectorBridge.lean` |
| `fix_chiral.py` | 9 | Tracked | `fix_*.py` | `lean/DAG/ChiralDiracAnticommutation.lean` |
| `fix_cl11.py` | 59 | Tracked | `fix_*.py` | `lean/InfoGeometry/Canonical/Cl11LeftRightDoubleBridge.lean` |
| `fix_drazin.py` | 19 | Tracked | `fix_*.py` | `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean` |
| `fix_ep.py` | 12 | Tracked | `fix_*.py` | `lean/InfoGeometry/Canonical/EPAndGroupInverse.lean` |
| `fix_logsumexp.py` | 50 | Tracked | `fix_*.py` | `lean/InfoGeometry/Analytic/LogSumExp.lean` |
| `fix_smul.py` | 6 | Tracked | `fix_*.py` | `test_derivation.lean` |
| `fix_sylvester.py` | 194 | Tracked | `fix_*.py` | `lean/InfoGeometry/Categorical/SylvesterBraidRepresentation.lean` |
| `fix_sylvester_full.py` | 249 | Tracked | `fix_*.py` | `lean/InfoGeometry/Categorical/SylvesterBraidRepresentation.lean` |
| `get_type.py` | 13 | Tracked | Other | `patch_test.lean` |
| `patch.py` | 18 | **Untracked** | Other | `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean` |
| `patch2.py` | 8 | Tracked | Other | `lean/InfoGeometry/Canonical/IBFrozenJaynes.lean` |
| `patch_bridge.py` | 16 | Tracked | `patch_*.py` | `lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean` |
| `patch_bridge2.py` | 22 | Tracked | `patch_*.py` | `lean/InfoGeometry/Canonical/Cl11BipartiteDiracBridge.lean` |
| `patch_drazin.py` | 91 | Tracked | `patch_*.py` | `lean/InfoGeometry/Canonical/DrazinCoreFlow.lean` |
| `patch_limit.py` | 12 | Tracked | `patch_*.py` | `lean/InfoGeometry/GrandUnification/CantorTypeDBitwordLimit.lean` |
| `patch_section.py` | 26 | Tracked | `patch_*.py` | `lean/InfoGeometry/External/Virasoro/SectionSES.lean` |
| `patch_unified.py` | 24 | Tracked | `patch_*.py` | `lean/InfoGeometry/Core/UnifiedGeometry.lean` |
| `patch_unified2.py` | 10 | Tracked | `patch_*.py` | `lean/InfoGeometry/Core/UnifiedGeometry.lean` |
| `patch_zorn.py` | 56 | Tracked | `patch_*.py` | `lean/InfoGeometry/Algebra/ZornVectorMatrix.lean` |

---

### 2.2 Category B — One-Off Math/CAS Scratch Computations (5 Scripts)

| Script | Lines | Git Status | Purpose | Disposition |
|---|---:|---|---|---|
| `compute_ldu.py` | 21 | Tracked | E₁₀ Dynkin Cartan matrix LDU scratch calculation | Retire to `archive/root_scripts_2026_11/` |
| `compute_ldu2.py` | 56 | Tracked | Rational LDU diagonalization scratch script | Retire to `archive/root_scripts_2026_11/` |
| `compute_ldu3.py` | 42 | Tracked | Rational LDU diagonalization variant | Retire to `archive/root_scripts_2026_11/` |
| `generate_lean.py` | 95 | Tracked | One-off code generator for `lean/InfoGeometry/Lie/E10HyperbolicSignature.lean` | Retire to `archive/root_scripts_2026_11/` |
| `scratch_cayley_dickson.py` | 89 | Tracked | One-off print generator for Cayley-Dickson basis tables | Retire to `archive/root_scripts_2026_11/` |

---

### 2.3 Category C — Repo-Level Utilities Superseded by `refactoring_map.py` (4 Scripts)

| Script | Lines | Git Status | Purpose | Superseded By / Hazard |
|---|---:|---|---|---|
| `find_orphans.py` | 48 | Tracked | BFS from `lean/InfoGeometry.lean` to list unimported modules | Superseded by [`tools/repository_evolution/refactoring_map.py`](file:///home/goutev/repos/info-geometry-lean/tools/repository_evolution/refactoring_map.py) (`unreachableLeanModules`) |
| `fix_imports.py` | 36 | Tracked | Appends all `lean/InfoGeometry/**/*.lean` imports to `lean/InfoGeometry.lean` | Superseded; unguarded append violates owner curation |
| `generate_recovery_index.py` | 48 | Tracked | Writes `lean/InfoGeometry/RecoveredIndex.lean` from unimported modules | Superseded by [`tools/repository_evolution/refactoring_map.py`](file:///home/goutev/repos/info-geometry-lean/tools/repository_evolution/refactoring_map.py) |
| `fix_manifests.py` | 32 | Tracked | Mutates `lake-manifest.json` inside `external_refs/atlas-embeddings` and `external_refs/gift-framework-core` | Violates [`AGENTS.md`](file:///home/goutev/repos/info-geometry-lean/AGENTS.md) prohibition on unrequested `lake-manifest.json` / submodule edits |

---

## 3. Subdirectory `fix_*.py` & `patch_*.py` Scripts Inventory (62 Active + 1 Archived)

In addition to the 120 root `.py` scripts, 62 tracked `fix_*.py` / `patch_*.py` scripts reside in subdirectories (and 1 in `archive/scratch_recovery/fix_virasoro.py`):

1. **`proofs/` & `proofs/scripts/` (16 scripts):** `proofs/fix_fib.py`, `proofs/fix_hex.py`, `proofs/fix_isospin.py`, `proofs/fix_isospin2.py`, `proofs/fix_subs.py`, `proofs/fix_trivial.py`, `proofs/fix_trivial2.py`, `proofs/patch_mellin.py`, `proofs/patch_spin.py`, `proofs/patch_syn2.py`, `proofs/patch_syn3.py`, `proofs/patch_syn4.py`, `proofs/patch_syn5.py`, `proofs/patch_syn6.py`, `proofs/patch_synthesis.py`, `proofs/scripts/fix_lean_with_oracle.py`.
2. **`tools/` top-level (7 scripts):** `tools/fix_amplituhedron.py`, `tools/fix_anyon_imports.py`, `tools/fix_arithmetic_function.py`, `tools/fix_clifford.py`, `tools/fix_mobius.py`, `tools/fix_type_star.py`, `tools/fix_zorn.py`.
3. **`tools/infra/` (31 scripts):** `fix_automath_generated.py`, `fix_basis_decide.py`, `fix_basis_decide2.py`, `fix_basis_final.py`, `fix_basis_finally.py`, `fix_basis_finally_for_real.py`, `fix_basis_simp_final.py`, `fix_basis_simp_real_final.py`, `fix_basis_undo.py`, `fix_by.py`, `fix_calc_order.py`, `fix_final_final.py`, `fix_final_mess.py`, `fix_final_v3.py`–`fix_final_v11.py` (9 files), `fix_inductive_simp.py`, `fix_jacobi_all.py`, `fix_jacobi_all_2.py`, `fix_jacobi_final.py`, `fix_odd_basis.py`, `fix_skew_calc.py`, `fix_types.py`, `fix_types_real.py`, `patch_mathlib.py`.
4. **`tools/python/` (8 scripts):** `fix_docstring.py`, `fix_equiv.py`, `fix_equiv_2.py`, `fix_imports.py`, `fix_mobius.py`, `fix_mobius2.py`, `fix_mobius_alg_decomp.py`, `fix_mobius_alg_decomp_direct.py`.

---

## 4. Root Script Archival Status (`CAPA-007` Complete)

All **120** root `.py` scripts have been archived to `archive/root_scripts_2026_11/` with explicit user approval per CAPA-007:

| Phase | Action | Status | Details |
|---|---|---|---|
| **Inventory** | Read-only classification of all 120 root `.py` scripts | Complete | `docs/ROOT_PYTHON_SCRIPTS_INVENTORY.md` |
| **Import audit** | Verified 0 maintained modules import any root script | Complete | `rg` search across `tools/`, `scripts/`, `tests/`, `src/`, `extensions/` |
| **Archival** | `git mv` of 118 tracked scripts + `mv` of 2 untracked scripts | Complete | All scripts now in `archive/root_scripts_2026_11/` |
| **Repository root** | 0 `.py` scripts remaining at root level | Complete | Verified via `ls *.py` |
| **Context preflight** | `context_preflight.py:49` excludes `!archive/**` | Complete | Archived scripts excluded from preflight searches |

No `rm` or `git rm` was used — all scripts were preserved via `git mv` / `mv` to maintain full git history.
