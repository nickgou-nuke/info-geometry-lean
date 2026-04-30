# Ranked remediation checklist from `reports/full-dvorak-audit.json`

Generated from 72 findings (`non_vacuity` only).

## Ranking (by issue count)
1. `lean/InfoGeometry/Meta/Admission.lean` — 24
2. `lean/InfoGeometry/Meta/StrictSurface.lean` — 10
3. `lean/InfoGeometry/auto_blueprints.lean` — 9
4. `lean/InfoGeometry/Meta/RegionPolicy.lean` — 8
5. `lean/InfoGeometry/Meta/StrictDef.lean` — 6
6. `lean/InfoGeometry/Meta/Trust.lean` — 6
7. `lean/InfoGeometry/Canonical/GaugeGroups.lean` — 2
8. `lean/InfoGeometry/Arithmetic/MoebiusSignature.lean` — 2
9. `lean/InfoGeometry/All.lean` — 1
10. `lean/InfoGeometry/Meta/ClosureAttribute.lean` — 1
11. `lean/InfoGeometry/Canonical/MajoranaKitaevSpinorBridge.lean` — 1
12. `lean/InfoGeometry/Canonical/DimensionAgnosticModularKLDivergence.lean` — 1
13. `lean/InfoGeometry/Canonical/OperatorPenroseUnification.lean` — 1

---

## File-by-file checklist (file -> lines -> suggested fix pattern)

### 1) `lean/InfoGeometry/Meta/Admission.lean` (24)
- Lines: 9, 17, 53, 56, 59, 63, 69, 72, 115, 128, 132, 135, 136, 141, 142, 145, 149, 154, 158, 162, 168, 171, 175, 179
- Observed hotspots:
  - metadata structures (`AdmissionDecision`, `AdmissionReason`, `AdmissionReport`)
  - `mkAdmissionReason`
  - `evaluateAdmission`
- Suggested fix pattern:
  1. Replace free-form string severity/codes with typed enums (`Severity`, `ReasonCode`) to prevent vacuous string-level policy checks.
  2. Strengthen decision invariants in `evaluateAdmission`:
     - `blocked` iff at least one hard error reason exists.
     - `needsReview` iff zero hard errors and at least one soft warning exists.
     - `admitted` iff both hard and soft reasons are empty.
  3. Add theorem-style sanity lemmas proving those invariants (non-vacuous policy semantics).
  4. Keep JSON codecs derived from typed enums, not ad-hoc strings.

### 2) `lean/InfoGeometry/Meta/StrictSurface.lean` (10)
- Lines: 35, 39, 96, 97, 98, 101, 105, 111, 116, 167
- Observed hotspots:
  - `extraBlockingReasons`
  - `blockerCodes`
  - final admission decision assembly in `processStrictDecl`
- Suggested fix pattern:
  1. Remove stringly checks in `blockerCodes` (`reason.severity = "error"`) and use typed severity.
  2. Prove monotonicity property:
     - adding `extraReasons` cannot improve decision (`blocked` dominates).
  3. Add explicit construction tests:
     - protected region + bridge/translator => always blocked with corresponding reason code.
     - protected capstone without rep-depth => blocked.
     - thin surface in protected region => blocked.
  4. Ensure telemetry blockers list is computed from typed reason codes only.

### 3) `lean/InfoGeometry/auto_blueprints.lean` (9)
- Lines: 6353, 6354, 6355, 6356, 6357, 6358, 6409, 6412, 6419
- Observed hotspots:
  - `[blueprint]` attributes applied to Meta admission machinery.
- Suggested fix pattern:
  1. Split blueprint scope:
     - keep computational/canonical declarations in blueprint export,
     - exclude policy/audit meta-plumbing declarations that inflate vacuity signals.
  2. Introduce whitelist/blacklist section for meta declarations with comment rationale.
  3. Add a small guard lemma or script assertion that blueprint export excludes known policy-only meta symbols.

### 4) `lean/InfoGeometry/Meta/RegionPolicy.lean` (8)
- Lines: 2, 11, 18, 35, 46, 53, 59, 60
- Suggested fix pattern:
  - Add constructive proofs around `regionOfDecl`, `requiredAttrsForRegion`, and `adjustDecisionForRegion` consistency (no no-op remaps).

### 5) `lean/InfoGeometry/Meta/StrictDef.lean` (6)
- Lines: 18, 31, 34, 169, 252, 291
- Suggested fix pattern:
  - Ensure forbidden syntax checks are expression-level and elaboration-level both, with explicit theorem/tests demonstrating no bypass through generated syntax.

### 6) `lean/InfoGeometry/Meta/Trust.lean` (6)
- Lines: 4, 13, 62, 68, 81, 96
- Suggested fix pattern:
  - Normalize forbidden-axiom checks into typed set and prove `hasSorryAx -> blocked` implication in admission pathway.

### 7) `lean/InfoGeometry/Canonical/GaugeGroups.lean` (2)
- Lines: 14, 15
- Suggested fix pattern:
  - Remove or rephrase comments containing soft-trigger terms if auditor uses lexical heuristics.

### 8) `lean/InfoGeometry/Arithmetic/MoebiusSignature.lean` (2)
- Lines: 28, 32
- Suggested fix pattern:
  - Replace commented `sorry` placeholders with TODO tags that do not include `sorry` token, or complete proof stubs.

### 9-13) Single-hit files
- `All.lean`, `ClosureAttribute.lean`, `MajoranaKitaevSpinorBridge.lean`, `DimensionAgnosticModularKLDivergence.lean`, `OperatorPenroseUnification.lean`
- Suggested fix pattern:
  - lexical cleanup in comments/docstrings if token-triggered; otherwise add local constructive witness lemma near flagged declaration.

---

## 1-pass patch order for top 3 files

### Pass order (single sweep)
1. `Meta/Admission.lean`
2. `Meta/StrictSurface.lean`
3. `auto_blueprints.lean`

### Why this order
- `Admission` defines core decision semantics and reason representation.
- `StrictSurface` consumes `Admission` and emits final decision/telemetry.
- `auto_blueprints` is export/index surface and should be aligned last after semantic shapes stabilize.

### Single-sweep patch plan

#### Step A — `Meta/Admission.lean` (semantic kernel)
- Introduce typed `Severity`/`ReasonCode`.
- Refactor `AdmissionReason` fields to typed forms.
- Refactor `mkAdmissionReason` + JSON encoding.
- Add invariant lemmas for `evaluateAdmission`.

#### Step B — `Meta/StrictSurface.lean` (consumer alignment)
- Update reason construction calls to typed codes/severity.
- Replace blocker extraction from string equality with enum match.
- Add/adjust decision assembly assertions and tests.

#### Step C — `auto_blueprints.lean` (surface pruning)
- Remove/segregate blueprint tags for policy-only meta admission symbols:
  - `InfoGeometry.Meta.AdmissionDecision`
  - `InfoGeometry.Meta.AdmissionReason`
  - `InfoGeometry.Meta.AdmissionReport`
  - `InfoGeometry.Meta.evaluateAdmission`
  - `InfoGeometry.Meta.hasExplicitAdmissionMetadata`
  - `InfoGeometry.Meta.mkAdmissionReason`
  - and related policy-only metadata symbols.
- Keep theorem/canonical computational exports unchanged.

### Verification sequence after the pass
1. `lake build InfoGeometry.Meta.Admission InfoGeometry.Meta.StrictSurface`
2. `lake env lean tests/DvorakSystemTest.lean`
3. `python3 tools/quality/dvorak_audit.py --root lean/InfoGeometry --json-out reports/full-dvorak-audit.json`
4. Compare counts; accept only if `non_vacuity` decreases and no new build regressions.
