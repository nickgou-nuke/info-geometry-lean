# Frame-Dragging / Gravitomagnetism Unification Plan

**Document ID:** QMS-PLAN-FRAMEDRAG-001  
**Version:** 1.0  
**Status:** Proposed (not yet executed)  
**Related report:** `docs/FRAMEDRAGGING_GRAVITOMAGNETISM_UNIFICATION_REPORT.md`  
**Governing Policy:** `AGENTS.md`, `docs/RUNBOOK.md`, `docs/ALCHEMICAL_QMS_SOP.md`, `docs/WARNING_DO_NOT_RUN_CACHE.md`  
**Repository:** info-geometry-lean  
**Lean toolchain:** Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`

---

## 1. Objective

Unify the duplicated frame-dragging / gravitomagnetism / Lense-Thirring / Mach-principle formalism that currently exists across ~50 Lean owner files into:

1. A single **kernel-checked bridge module** (`GravitoElectromagneticBridge.lean`) carrying the common non-commutative ring identities;
2. A **10-clade taxonomy** (`GEMTaxonomicClade`) and **8-epoch phylogenesis** (`GEMPhylogeneticEpoch`) classified on the same four axes as the existing analytic taxonomy (MLT stratum M0–M3, representation depth L0–L5, semantic sense, QMS bucket);
3. A **Python contract test** asserting the bijection between Lean `ChangeCategory.id` strings and Python `CATEGORY_IDS` values for GEM-related categories (Level 5 convention, not logical embedding).

All changes must compile under `run_locked_lake_build.py`, pass `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`), pass `vacuity-linter.py` (honesty 1.0, vacuity 0.0), and pass `opengauss_screener.py --strict`.

---

## 2. Epistemic Boundary (from AGENTS.md)

- Lean checks a proposition at its declared type. It does **not** establish that a filename, docstring, or doc comment describes a physical proposition faithfully.
- The Lean formalization is over a non-commutative ring `[Ring B]` with idempotent `P : B`. It is **not** a proof of General Relativity, frame-dragging physics, or any physical law.
- No topology, colimit, measure theory, or analytic limit is supplied unless the corresponding construction and compatibility proof are added.
- Python weak-rule labels (`evolution_taxonomy.py`) and Git phylogeny (`phylogeny_export.py`) are Authority Level 5 navigation/traceability only — never kernel-verified mathematical truth.
- Cross-layer links (`CATEGORY_IDS` ↔ `ChangeCategory.id`) are conventional identifiers, not logical embeddings.

---

## 3. Role Separation (SOP-001)

| Role | Agent ID | Responsibility |
|---|---|---|
| **G-A (Generator)** | — | Implements candidate repairs, authors Formal Intent Envelopes, runs narrow locked validation |
| **A-A (Independent Auditor)** | — | Independently audits G-A outputs, issues NCs/CAPAs |
| **QA-A (Quality Assurance)** | — | Verifies CAPA closure, checks SHA-256 fingerprints, signs final disposition |
| **Orchestrator (Parent)** | — | Enforces build-lock discipline, integrates approved candidates, checkpoints edits |

**G-A may never audit or QA-approve its own work.**

---

## 4. Formal Intent Envelope (Phase 5 of pipeline plan)

| Field | Value |
|---|---|
| Target surface | `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean` (new); consumers in `lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`, `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean`, `lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean` |
| Risk class | R1 (Low — Lean docstring/linter & build freshness) |
| Bucket | BUCKET 1 (`Bucket A` — Verified Core) |
| Required gates | `run_locked_lean.py`, `run_locked_lake_build.py`, `opengauss_screener.py --strict`, `proof_proxy_staged_gate.py`, `vacuity-linter.py`, `axiom_index.py` |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Non-goals | No physical interpretation claims; no topology/colimit/completion; no biological interpretation |

---

## 5. Step-by-Step Execution Plan

### Step 5.1 — Pre-flight (Orchestrator)

| Action | Command | Expected result |
|---|---|---|
| Inspect working tree | `git status --short` | Preserve all staged Canonical/ work |
| Inspect running processes | `ps -ef \| rg -i "lake\|lean"` | No active Lake process |
| Check build lock | `ls -la /tmp/info-geometry-build.lock` | Lock file not held by another process |

### Step 5.2 — Create candidate bridge module (G-A)

**File:** `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean`

```lean
/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.Core.IdempotentGraphGrassmannian

/-!
# Gravito-Electromagnetic Bridge: Non-Commutative Peirce Spine Identities

This module formalizes finite algebraic identities over an associative ring `B` (`[Ring B]`)
equipped with an idempotent `P : B` (`P * P = P`), its grading involution `invS P = P - (1 - P)`,
and opposite Peirce corners `conePlus P A = P * A * (1 - P)` and `coneMinus P C = (1 - P) * C * P`:

- Chiral lock between the commutator `genSig P A C = [N₊, N₋]` and anticommutator
  `genV P A C = {N₊, N₋}` (`gemDipole_chiral_lock`)
- First-order commutator identities `[Σ, Φ] = 2 • (V * J)` (`gemFirstOrderLenseThirring`),
  `[Σ, J] = 2 • (V * Φ)` (`gemDualPrecession`), and corner brackets
  (`gemCornerPrecession_plus`, `gemCornerPrecession_minus`)
- Dressed commutator `[P + Σ, Φ] = (1 + 2 • V) * J` (`gemDressedTorsion_eq`)
- Second-order double-commutator identities `[Σ, [Σ, Φ]] = 4 • (V² * Φ)`
  (`gemSecondOrderCentrifugal`) and `[Σ, [Σ, J]] = 4 • (V² * J)`
  (`gemSecondOrderCentrifugal_dual`)
- Anticommutator orthogonality `{Σ, Φ} = 0`, `{Σ, J} = 0`, and `{Φ, [Σ, Φ]} = 0`
  (`gemSpinPhi_anticomm`, `gemSpinJ_anticomm`, `gemWorkFreeCoriolis`)
- Product identity `Σ * Φ = V * J` and square `(Σ * Φ)² = -V³`
  (`gemSpinMulPhi_eq`, `gemNilpotentCollapse`)
- Reciprocal commutator anticommutator `{[Σ, Φ], [Σ, J]} = 0` and difference of squares
  `[Σ, Φ]² - [Σ, J]² = -8 • V³` (`gemOnsagerReciprocity_anticomm`, `gemOnsagerReciprocity_sq_diff`)
- Vanishing interaction implication `V = 0 → [Σ, X] = 0` (`gemMachPrinciple`)

Epistemic boundary: Lean checks these propositions at their declared algebraic types over `[Ring B]`.
No physical interpretation (General Relativity, spacetime manifold geometry, or frame-dragging
physics) and no topological, colimit, or analytic limit structure is asserted or inferred.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

variable {B : Type*} [Ring B]

/-- The Peirce corner commutator `Σ = genSig P A C` equals the grading involution `invS P`
multiplied by the symmetric corner anticommutator `V = genV P A C`. -/
theorem gemDipole_chiral_lock {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C - invS P * genV P A C = 0 := by
  peirce_nf hP

/-- First-order commutator of the Peirce spin element `Σ` with the symmetric boundary element `Φ`:
`[Σ, Φ] = 2 • (V * J)`. -/
theorem gemFirstOrderLenseThirring {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genJ P A C) := by
  peirce_nf hP

/-- Dual first-order commutator of the Peirce spin element `Σ` with the skew boundary element `J`:
`[Σ, J] = 2 • (V * Φ)`. -/
theorem gemDualPrecession {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) := by
  peirce_nf hP

/-- Commutator of `Σ` with the upper Peirce corner `N₊`: `[Σ, N₊] = 2 • (V * N₊)`. -/
theorem gemCornerPrecession_plus {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A) := by
  peirce_nf hP

/-- Commutator of `Σ` with the lower Peirce corner `N₋`: `[Σ, N₋] = -(2 • (V * N₋))`. -/
theorem gemCornerPrecession_minus {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (coneMinus P C) = -((2 : ℤ) • (genV P A C * coneMinus P C)) := by
  peirce_nf hP

/-- Dressed commutator `[P + Σ, Φ] = (1 + 2 • V) * J`. -/
theorem gemDressedTorsion_eq {P : B} (hP : P * P = P) (A C : B) :
    comm (P + genSig P A C) (genPhi P A C) = (1 + (2 : ℤ) • genV P A C) * genJ P A C := by
  have h : comm (P + genSig P A C) (genPhi P A C) =
      genJ P A C + (2 : ℤ) • (genV P A C * genJ P A C) := by
    peirce_nf hP
  rw [h, two_zsmul, two_zsmul]
  noncomm_ring

/-- Second-order double commutator of `Σ` on `Φ`: `[Σ, [Σ, Φ]] = 4 • (V² * Φ)`. -/
theorem gemSecondOrderCentrifugal {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genPhi P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genPhi P A C) := by
  peirce_nf hP

/-- Dual second-order double commutator of `Σ` on `J`: `[Σ, [Σ, J]] = 4 • (V² * J)`. -/
theorem gemSecondOrderCentrifugal_dual {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (comm (genSig P A C) (genJ P A C)) =
      (4 : ℤ) • ((genV P A C * genV P A C) * genJ P A C) := by
  peirce_nf hP

/-- Anticommutator orthogonality between `Σ` and `Φ`: `{Σ, Φ} = 0`. -/
theorem gemSpinPhi_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genSig P A C) (genPhi P A C) = 0 := by
  peirce_nf hP

/-- Anticommutator orthogonality between `Σ` and `J`: `{Σ, J} = 0`. -/
theorem gemSpinJ_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genSig P A C) (genJ P A C) = 0 := by
  peirce_nf hP

/-- Anticommutator orthogonality between `Φ` and its `Σ`-commutator `[Σ, Φ]`: `{Φ, [Σ, Φ]} = 0`. -/
theorem gemWorkFreeCoriolis {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genPhi P A C) (comm (genSig P A C) (genPhi P A C)) = 0 := by
  peirce_nf hP

/-- Ordered product identity `Σ * Φ = V * J`. -/
theorem gemSpinMulPhi_eq {P : B} (hP : P * P = P) (A C : B) :
    genSig P A C * genPhi P A C = genV P A C * genJ P A C := by
  peirce_nf hP

/-- Square of the ordered product `Σ * Φ`: `(Σ * Φ) * (Σ * Φ) = -V³`. -/
theorem gemNilpotentCollapse {P : B} (hP : P * P = P) (A C : B) :
    (genSig P A C * genPhi P A C) * (genSig P A C * genPhi P A C) =
      -(genV P A C * genV P A C * genV P A C) := by
  peirce_nf hP

/-- Anticommutator orthogonality of the conjugate first-order commutators `[Σ, Φ]` and `[Σ, J]`:
`{[Σ, Φ], [Σ, J]} = 0`. -/
theorem gemOnsagerReciprocity_anticomm {P : B} (hP : P * P = P) (A C : B) :
    anticomm (comm (genSig P A C) (genPhi P A C)) (comm (genSig P A C) (genJ P A C)) = 0 := by
  peirce_nf hP

/-- Difference of squares of the conjugate first-order commutators `[Σ, Φ]` and `[Σ, J]`:
`[Σ, Φ]² - [Σ, J]² = -(8 • V³)`. -/
theorem gemOnsagerReciprocity_sq_diff {P : B} (hP : P * P = P) (A C : B) :
    comm (genSig P A C) (genPhi P A C) * comm (genSig P A C) (genPhi P A C) -
        comm (genSig P A C) (genJ P A C) * comm (genSig P A C) (genJ P A C) =
      -((8 : ℤ) • (genV P A C * genV P A C * genV P A C)) := by
  peirce_nf hP

/-- Vanishing of the symmetric Peirce interaction `V = 0` implies vanishing of the inner derivation
`[Σ, X] = 0` for every ring element `X : B`. -/
theorem gemMachPrinciple {P : B} (hP : P * P = P) (A C X : B)
    (hV : genV P A C = 0) :
    comm (genSig P A C) X = 0 := by
  have hSigV : genSig P A C = invS P * genV P A C := by peirce_nf hP
  rw [hSigV, hV, mul_zero]
  unfold comm
  noncomm_ring

end InfoGeometry.OperatorAlgebra.PeirceSpine
```

**Important:** Every `theorem` is a standalone, genuine lemma over `[Ring B]` with a full constructive proof (`peirce_nf hP`, `two_zsmul`, `noncomm_ring`) and zero wrapper `def`s, `Prop` placeholders, or `sorry` tokens.

### Step 5.3 — Consumer integration (G-A)

For each consumer owner file, add:
```lean
have hGem := gemFirstOrderLenseThirring ...
```
and replace the local proof with `exact hGem ...` where the hypotheses match.

Consumer files (in priority order):
1. `lean/InfoGeometry/Canonical/EinsteinCartanChiralAnomalyFrameDraggingPoset.lean`
2. `lean/InfoGeometry/Algebra/ZornAlternativeLaws.lean`
3. `lean/InfoGeometry/Canonical/WheelerGodelRotatingUniverseChronologyPoset.lean`

Each consumer change requires its own narrow locked build:
```bash
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.EinsteinCartanChiralAnomalyFrameDraggingPoset
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Algebra.ZornAlternativeLaws
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.Canonical.WheelerGodelRotatingUniverseChronologyPoset
```

### Step 5.4 — Taxonomy and phylogenesis classification (G-A)

Add to `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` or a new sibling file:

- `GEMTaxonomicClade` inductive (GCladeI–GCladeX)
- `GEMPhylogeneticEpoch` inductive (GEpoch1–GEpoch8)
- `gemPrimarySense`, `gemQMSBucket`, `gemMetaLevel`, `gemRepDepth` mappings
- `gemCausalEdge_acyclic` theorem

### Step 5.5 — Python contract test (G-A)

Add to `tests/test_evolution_taxonomy.py`:
- `test_gemCategoryIdsMatchLeanDarwinCommitTaxonomyContract()` — asserts bijection between Lean `ChangeCategory.id` literals and Python `CATEGORY_IDS` values for GEM-relevant categories
- `test_gemEvidenceKindsMatchLeanChangeLabelEvidenceContract()` — asserts 4-element alignment

This is a Level 5 schema convention, not a logical embedding.

### Step 5.6 — Full pipeline validation (G-A → A-A → QA-A)

```bash
# Narrow locked build on the new bridge module
python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge

# Axiom audit
python3 tools/infra/axiom_index.py --json InfoGeometry.OperatorAlgebra.PeirceSpine.GravitoElectromagneticBridge

# Vacuity linter
python3 tools/scripts/vacuity-linter.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean --json

# OpenGauss screener
python3 tools/infra/opengauss_screener.py lean/InfoGeometry/OperatorAlgebra/PeirceSpine/GravitoElectromagneticBridge.lean --strict

# Full Python test suite
python3 -m pytest tests/test_evolution_taxonomy.py tests/test_repository_phylogeny_export.py tests/test_decl_graph_generation.py tests/test_ontology_term_integrity.py tests/test_ontology_relationship_identity.py tests/test_arango_ontology_bridge.py tests/test_darwin_phylogeny_dashboard.py

# Full pipeline runner
./scripts/run_pipeline.sh --skip-lean-build
```

---

## 6. Definition of Done

| Criterion | Evidence |
|---|---|
| `GravitoElectromagneticBridge.lean` compiles with 0 errors | `run_locked_lake_build.py` exit code 0 |
| `axiom_index.py` reports only `{propext, Classical.choice, Quot.sound}` | `axiom_index.py --json` output |
| `vacuity-linter.py` reports honesty 1.0, vacuity 0.0 | `vacuity-linter.py --json` output |
| `opengauss_screener.py --strict` passes (T17 warnings non-blocking) | `opengauss_screener.py --strict` exit code 0 |
| Existing owners compile after `have hGem := ...` replacement | Narrow locked build per consumer module |
| All 73 Python tests pass | `pytest` exit code 0 |
| `run_pipeline.sh --skip-lean-build` exits 0 | Pipeline exit code 0 |
| `git diff` reviewed for unrelated changes | `git status --short` shows only task-owned files |

---

## 10. Reporting Contract (per `docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md` §6)

Every execution turn must conclude with:

1. **Changed Files:** Exact paths and line ranges (`git status --short`, `git diff --stat`)
2. **Exact Validation Commands & Results:** Narrow locked Lean build commands and exit codes; quality gate outputs; Python unit test commands and pass counts
3. **Proved or Observed Scope:** Distinction between Level 1–2 `[kernel_verified]` Lean theorems (with exact carrier, hypotheses, `#print axioms`) and Level 5 `[navigation_metadata]` Python/Arango/Postgres artifacts; narrow validation reported at actual module/file scope only
4. **Role Sign-Off & Remaining Debt:** G-A → A-A → QA-A sign-off chain, SHA-256 fingerprint of controlled deliverables, open or deferred items

---

## 11. Risks and Mitigations

| Risk | Mitigation |
|---|---|
| `GravitoElectromagneticBridge.lean` theorems require `sorry` | Do not introduce `sorry`; prove using `peirce_nf hP` / `noncomm_ring` / `simp` exactly as existing `CladisticPhylogenesisBridge.lean` theorems do |
| Consumer owners use different variable names | Adapt the bridge theorem statements to match existing variable names; do not rename owner variables |
| Cross-layer `CATEGORY_IDS` treated as proof | Explicitly document as Level 5 convention, not logical embedding |
| Unrelated staged work in `Canonical/` disturbed | Do not touch staged `Canonical/` files unless they are the specific owner target; review `git status --short` before every edit |

---

## 12. References

| Document | Path | Role |
|---|---|---|
| Frame-dragging / gravitomagnetism report | `docs/FRAMEDRAGGING_GRAVITOMAGNETISM_UNIFICATION_REPORT.md` | Bounded search results |
| Pipeline improvement plan | `docs/PIPELINE_IMPROVEMENT_AND_REFACTORING_PLAN.md` | QMS-PLAN-PIPE-001 v2.0, phases 1–5 |
| Pipeline operator manual | `docs/PIPELINE_OPERATOR_MANUAL.md` | Consolidated operator manual |
| Repository agent policy | `AGENTS.md` | Build lock, dependency, cache discipline |
| QMS SOP | `docs/ALCHEMICAL_QMS_SOP.md` | Role separation, CAPA workflow |
| Cache policy | `docs/WARNING_DO_NOT_RUN_CACHE.md` | No `lake clean`, no dependency changes |
| Lean owners | `lean/InfoGeometry/OperatorAlgebra/OntologyRing.lean` | MLT stratification, `projectorSubspace`, `cladeSubsumes`, `cladeFork`, `cladeJoin` |
| Lean owners | `lean/InfoGeometry/OperatorAlgebra/PeirceSpine/CladisticPhylogenesisBridge.lean` | D₅₀ phylogenesis identities, `cladeSubsumes_trans`, `cladeFork_mrca` |
| Lean owners | `lean/InfoGeometry/Canonical/AnalyticOntologyTaxonomyPhylogenesisPoset.lean` | 10-clade taxonomy, 8-epoch phylogenesis |
| Python pipeline | `tools/infra/evolution_taxonomy.py` | Weak-rule commit classifier, `CATEGORY_IDS` mapping |
| Python pipeline | `tools/repository_evolution/phylogeny_export.py` | `repo-phylogeny/v2` export |
| Python bridge | `tools/infra/arango_to_ontology.py` | ArangoDB → Auto-Ontology term store |

---

**End of plan.** All changes proceed one serialized change at a time with diff review. Independent A-A/QA-A sign-off required before promotion to tracked owner files.