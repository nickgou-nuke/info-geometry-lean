# Gravito-Electromagnetic Bridge Implementation Plan

**Document ID:** QMS-PLAN-GRAVEM-001  
**Version:** 1.1  
**Status:** Core implemented and verified; consumer review narrowed the integration scope
**Repository:** info-geometry-lean  
**Baseline Commit:** `214f7bcf733eaf4720913bc2c082936f2480d3fc`

## 1. Executive Summary

This plan formalizes gravito-electromagnetic (GEM) structures in Lean 4 as a bridge between the `OntologyRing` multi-level ontology (`lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean`), the `CladisticPhylogenesisBridge` $D_{50}$ cladistic phylogenesis layer (`lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean`), and the canonical Einstein–Cartan, Wheeler–Gödel, Zorn split-octonion, and analytic taxonomy/phylogenesis owners. The work builds strictly on the native `PeirceSpine` operators (`genV`, `genSig`, `genPhi`, `genJ`, `conePlus`, `coneMinus`, `invS`, `comm`, `anticomm`) over `[Ring B]`.

All proofs are kernel-checked using `peirce_nf hP` (Peirce normal form tactic) with zero wrappers, zero `Prop`-valued def surfaces, zero witness structures, zero `sorry`, zero `admit`, and zero custom axioms beyond `propext`.

## 2. Core Bridge Module (`GravitoElectromagneticBridge.lean`)

### Primary Owner
| File | Lines | Status | Description |
|------|-------|--------|-------------|
| `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean` | `1–144` | **Implemented & Kernel-Verified** | 16 pure `[Ring B]` non-definitional theorems linking the gravito-electric monopole $V = \mathrm{genV}\;P\;A\;C$, gravito-magnetic dipole $\Sigma = \mathrm{genSig}\;P\;A\;C$, and solder 1-forms $\Phi = \mathrm{genPhi}\;P\;A\;C$, $J = \mathrm{genJ}\;P\;A\;C$ |

### 16 Kernel-Checked Theorems in `GravitoElectromagneticBridge.lean`
| # | Theorem (`file:line`) | Exact Statement over `[Ring B]` (`hP : P * P = P`) |
|---|-----------------------|----------------------------------------------------|
| $G_1$ | `gemDipole_chiral_lock` (`:47`) | `genSig P A C - invS P * genV P A C = 0` |
| $G_2$ | `gemFirstOrderLenseThirring` (`:53`) | `comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C)` |
| $G_3$ | `gemDualPrecession` (`:59`) | `comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C)` |
| $G_4$ | `gemCornerPrecession_plus` (`:64`) | `comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)` |
| $G_5$ | `gemCornerPrecession_minus` (`:69`) | `comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C))` |
| $G_6$ | `gemDressedTorsion_eq` (`:74`) | `comm (P + genSig P A C) (genPhi P A C) = (1 + (2 : ℤ) • genV P A C) * genJ P A C` |
| $G_7$ | `gemSecondOrderCentrifugal` (`:83`) | `comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C)` |
| $G_8$ | `gemSecondOrderCentrifugal_dual` (`:89`) | `comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) = (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C)` |
| $G_9$ | `gemSpinPhi_anticomm` (`:95`) | `anticomm (genSig P A C) (genPhi P A C) = 0` |
| $G_{10}$ | `gemSpinJ_anticomm` (`:100`) | `anticomm (genSig P A C) (genJ P A C) = 0` |
| $G_{11}$ | `gemWorkFreeCoriolis` (`:105`) | `anticomm (genPhi P A C) (comm (genSig P A C) (genPhi P A C)) = 0` |
| $G_{12}$ | `gemSpinMulPhi_eq` (`:110`) | `genSig P A C * genPhi P A C = genV P A C * genJ P A C` |
| $G_{13}$ | `gemNilpotentCollapse` (`:115`) | `(genSig P A C * genPhi P A C) * (genSig P A C * genPhi P A C) = -(genV P A C * genV P A C * genV P A C)` |
| $G_{14}$ | `gemOnsagerReciprocity_anticomm` (`:122`) | `anticomm (comm (genSig P A C) (genPhi P A C)) (comm (genSig P A C) (genJ P A C)) = 0` |
| $G_{15}$ | `gemOnsagerReciprocity_sq_diff` (`:128`) | `comm (genSig P A C) (genPhi P A C) * comm (genSig P A C) (genPhi P A C) - comm (genSig P A C) (genJ P A C) * comm (genSig P A C) (genJ P A C) = -((8 : ℤ) • (genV P A C * genV P A C * genV P A C))` |
| $G_{16}$ | `gemMachPrinciple` (`:136`) | `genV P A C = 0 → comm (genSig P A C) X = 0` |

## 3. Implementation Plan & Exact `file:line` Targets

### Phase A: Integrate Bridge into Existing Lean Owners (Priority: P0)

| Step | File (`file:line`) | Action | Verification Command |
|------|--------------------|--------|----------------------|
| 5.1.1 | `lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean` | **Deferred:** the proposed conjunction-only theorem merely collects GEM identities and does not connect them to an OntologyRing result. It was removed under the no-wrapper constraint. A genuine shared implication remains open. | No validation target; no new declaration retained |
| 5.1.2 | `lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean:16, 394–417` | Import `GravitoElectromagneticBridge` at line `16`; discharge `archetype_E5_spin_frame_dragging_and_dressed_torsion` at lines `394–417` via `gemSpinPhi_anticomm`, `gemSpinJ_anticomm`, `gemFirstOrderLenseThirring`, `gemDualPrecession`, `gemCornerPrecession_plus`, `gemCornerPrecession_minus`, and `gemDressedTorsion_eq` | `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean` |
| 5.1.3 | `lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean:12, 971–987` | Import `GravitoElectromagneticBridge` at line `12`; discharge `native_spin_and_centrifugal_frame_dragging` at lines `971–987` via `gemFirstOrderLenseThirring`, `gemDualPrecession`, `gemSecondOrderCentrifugal`, and `gemSecondOrderCentrifugal_dual` | `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean` |
| 5.1.4 | `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean` | **Deferred:** the proposed theorem conjoined facts over independent `ZornVectorMatrix R` and `[Ring B]` carriers without a map or compatibility premise. It was removed under the no-wrapper constraint; a genuine cross-carrier connection remains open. | No validation target; no new declaration retained |

### Phase B: Extend Taxonomy (10-Clade `GEMTaxonomicClade`) & Phylogenesis (8-Epoch `GEMPhylogeneticEpoch`) (Priority: P1)

| Step | File (`file:line`) | Action | Verification Command |
|------|--------------------|--------|----------------------|
| 5.2.1 | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean:939–1008` | Define the 10-clade taxonomy and its classification theorem. This remains taxonomy metadata; no bridge theorem to the algebraic carrier is claimed. | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset` |
| 5.2.2 | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean:1011–1060` | Define 8-epoch `GEMPhylogeneticEpoch` (`GEpoch1_NewtonianGravitoElectric`..`GEpoch8_KerrErgosphereCollapse`), `gemEpochRank`, `gemCausalEdge`, and theorems `gemCausalEdge_irrefl`, `gemCausalEdge_trans`, `gemCausalEdge_acyclic` at lines `1011–1060` | `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` |
| 5.2.3 | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean:1062–1090` | Define `analyticToGEMEpoch` and prove its rank, injectivity, and edge-preservation lemmas. The conjunction-only master theorem was removed; the remaining claims are reported at their individual statements. | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPoset` |
| 5.2.4 | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean:770–794` | Audit the 16 bridge theorems and individual taxonomy/epoch theorems; no collection wrappers are audited. | `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.AnalyticOntologyTaxonomyPhylogenesisPosetAudit` |

### Phase 3: Python Pipeline Integration (Priority: P2)

| Step | File (`file:line`) | Action | Verification Command |
|------|--------------------|--------|----------------------|
| 5.3.1 | `tools/infra/evolution_taxonomy.py:63–85` | Define `GEM_CLADE_IDS` (10 clades matching `GEMTaxonomicClade`) and `GEM_EPOCH_IDS` (8 epochs matching `GEMPhylogeneticEpoch`) at lines `63–85` while preserving the 12-entry `CATEGORY_IDS` contract (`DarwinCommitTaxonomy.lean:19–71`) | `python3 -m unittest tests/test_evolution_taxonomy.py` |
| 5.3.2 | `tools/infra/arango_to_ontology.py:55–185, 310–355` | Support `--generation-id`, `--decls-jsonl`, `--decl-edges-jsonl`, `--dry-run`, and `--report-json` for generation-pinned Auto-Ontology projection | `python3 -m unittest tests/test_arango_to_ontology_relationships.py` |
| 5.3.3 | `tools/infra/darwin_phylogeny_dashboard.py:18–190` | Support `--phylogeny-json` input and render commit/declaration phylogeny metadata in the `#tip` tooltip | `python3 -m unittest tests/test_darwin_phylogeny_dashboard.py` |
| 5.3.4 | `tools/repository_evolution/phylogeny_export.py:35–265` | Add optional `"declaration_links"` carrier and `--decl-edges` CLI flag while keeping the commit DAG strictly separate from the Lean declaration DAG | `python3 -m unittest tests/test_repository_phylogeny_export.py` |

### Phase 4: Tests (Priority: P2)

| Step | File (`file:line`) | Action | Verification Command |
|------|--------------------|--------|----------------------|
| 5.4.1 | `tests/test_gravito_electromagnetic_bridge.py:1–156` | Verify the 16 core theorems, substantive EinsteinCartan/WheelerGodel reuse, taxonomy/epoch contracts, and individual axiom-audit entries. | `python3 -m unittest tests/test_gravito_electromagnetic_bridge.py` |
| 5.4.2 | `tests/test_evolution_taxonomy.py:153–242` | Verify `test_category_ids_match_lean_darwin_commit_taxonomy_contract`, `test_gemCategoryIdsMatchLeanDarwinCommitTaxonomyContract` (including 10-clade `GEM_CLADE_IDS` and 8-epoch `GEM_EPOCH_IDS` alignment with `AnalyticOntologyTaxonomyPhylogenesisPoset.lean`), and `test_gemEvidenceKindsMatchLeanChangeLabelEvidenceContract` | `python3 -m unittest tests/test_evolution_taxonomy.py` |
| 5.4.3 | `tests/test_repository_phylogeny_export.py:1–135` | Verify commit DAG export and optional `"declaration_links"` carrier separation | `python3 -m unittest tests/test_repository_phylogeny_export.py` |
| 5.4.4 | `tests/test_darwin_phylogeny_dashboard.py:1–95` | Verify `--phylogeny-json` rendering and `#tip` tooltip generation | `python3 -m unittest tests/test_darwin_phylogeny_dashboard.py` |

## 4. Dependencies

```
Phase 1: GravitoElectromagneticBridge.lean (16 pure [Ring B] theorems)
    ↓
Phase A: Substantive Consumer Reuse (EinsteinCartan, WheelerGodel); OntologyRing and Zorn links remain open
    ↓
Phase B: 10-Clade GEMTaxonomicClade & 8-Epoch GEMPhylogeneticEpoch + Audit
    ↓
Phase 3: Python Pipeline Integration (evolution_taxonomy.py, arango_to_ontology.py, phylogeny_export.py, darwin_phylogeny_dashboard.py)
    ↓
Phase 4: Automated Contract & Unit Test Suite (24 unit tests)
```

## 5. Validation Commands

| Command | Purpose | Expected Result |
|---------|---------|-----------------|
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean` | Verify core GEM bridge module | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean` | Verify `OntologyRing` integration | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean` | Verify `EinsteinCartan` integration | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean` | Verify `WheelerGodel` integration | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean` | Verify `ZornAlternativeLaws` integration | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` | Verify 10-clade taxonomy & 8-epoch phylogenesis owner | Exit code 0 |
| `python3 tools/infra/run_locked_lean.py lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPosetAudit.lean` | Verify `#print axioms` audit module | Exit code 0; only `propext`, `Classical.choice`, `Quot.sound` |
| `python3 tools/infra/opengauss_screener.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean --strict` | Strict 17-Trap QMS screener | Exit code 0 (0 traps) |
| `python3 -m unittest tests/test_gravito_electromagnetic_bridge.py tests/test_evolution_taxonomy.py tests/test_repository_phylogeny_export.py tests/test_darwin_phylogeny_dashboard.py` | Run complete GEM & taxonomy/phylogeny Python test suite | Exit code 0 (24 tests OK) |

## 6. Reporting Contract

Every execution turn concludes with a QMS-compliant report containing:

1. **Changed Files:** Exact paths and line ranges (`git status --short`, `git diff --stat`)
2. **Exact Validation Commands & Results:** Narrow locked Lean build/check commands and exit codes; quality gate outputs; Python unit test commands and pass counts
3. **Proved or Observed Scope:** Distinction between Level 1–2 `[kernel_verified]` Lean theorems (with exact carrier, hypotheses, `#print axioms`) and Level 5 `[navigation_metadata]` Python/Arango/Postgres artifacts; report narrow validation at actual module/file scope only
4. **Role Sign-Off & Remaining Debt:** G-A → A-A → QA-A sign-off chain and open or deferred items

## 7. Risks & Mitigations

| Risk | Mitigation |
|------|------------|
| Mutating `CATEGORY_IDS` in `tools/infra/evolution_taxonomy.py` beyond 12 entries breaks `test_category_ids_match_lean_darwin_commit_taxonomy_contract` (`DarwinCommitTaxonomy.lean:19–71` has 12 constructors) | Keep `CATEGORY_IDS` at 12 entries matching `ChangeCategory`; export `GEM_CLADE_IDS` (10 clades matching `GEMTaxonomicClade`) and `GEM_EPOCH_IDS` (8 epochs matching `GEMPhylogeneticEpoch`) in `evolution_taxonomy.py:63–85` |
| `ZornVectorMatrix R` and `[Ring B]` are independent carriers | Do not conjoin their facts as a bridge. A future integration needs a real carrier map and a proved compatibility theorem. |
| Concurrent Lean builds contending for `.lake/build` | Serialize all Lean validations through `tools/infra/run_locked_lean.py` and `tools/infra/run_locked_lake_build.py --wait-for-build-lock` |
| Cross-layer `CATEGORY_IDS` / `GEM_CLADE_IDS` treated as formal proof | Explicitly document and test as Level 5 schema convention contracts (`[navigation_metadata]`), never as Lean kernel embeddings |
| Unrelated dirty worktree edits disturbed | Stage only task-owned files with `git add -- <paths>` and preserve all unrelated changes |
