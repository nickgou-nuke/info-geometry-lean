# Strict Mode Spec v0.1

Status: Draft proposal  
Audience: InfoGeometry maintainers and LLM-agent pipeline owners  
Goal: Prevent vacuous "formal-looking" Lean from entering the canonical publication surface.

---

## 1) Problem Statement

LLM-assisted Lean development can quickly produce code that is syntactically valid yet mathematically vacuous
(e.g., placeholder proofs, assumption-packaging theorems, identity update operators presented as algorithms,
namespace drift, and non-canonical import bleed).

Strict Mode defines an enforceable policy for what is allowed in canonical modules.

---

## 2) Scope Tiers

Strict Mode is tiered by module surface:

- **Tier C0 (Canonical)**: `lean/InfoGeometry.lean`, `lean/InfoGeometry/Library.lean`, `lean/InfoGeometry/Canonical/**`
- **Tier C1 (Research/Staging)**: `lean/InfoGeometry/Research/**` and other active but non-canonical modules
- **Tier C2 (Draft/Archive)**: `lean/InfoGeometry/Archive/**`, generated snapshots, exploratory modules

Policy principle:
- C0: hard fail on any strict violation
- C1: warn (optional fail for high-severity classes)
- C2: report only

---

## 3) Violation Classes

### V1 — Placeholder Proof Debt (Hard fail in C0)

Disallow:
- `sorry`, `admit`
- explicit placeholder text markers (e.g. `content will be moved here`)

Rationale: eliminates fake rigor by construction.

### V2 — Axiom Leakage (Hard fail in C0 unless allowlisted)

Disallow new top-level `axiom` declarations in C0.

Allowed exceptions (temporary):
- a reviewed, explicit allowlist file (`strict_allowlist_axioms.txt`) with expiry date + owner.

### V3 — Canonical Import Hygiene (Hard fail in C0)

Disallow C0 imports of:
- `InfoGeometry.Experimental`
- `InfoGeometry.Archive.*`
- non-allowlisted `InfoGeometry.Research.*`

### V4 — Namespace Integrity (Warn in C0 for v0.1; hard fail in v0.2)

Flag files in C0 whose first namespace is not `InfoGeometry*`.

### V5 — Orphan/Topology Integrity (Hard fail in C0)

Flag Lean files outside approved roots/umbrella modules that are accidentally detached from project topology.

### V6 — Vacuity Heuristics (Warn in C0 for v0.1)

Heuristic detection (non-blocking in v0.1):
- theorem body is assumption repackaging only
- algorithmic definitions equal identity with placeholder comments
- theorem names suggest novelty (`*_bridge`, `*_synthesis`, `*_nonvacuous`) but proof uses only direct forwarding

Output expected: warning report with ranked candidates for manual review.

---

## 4) Strict Mode Levels

CLI parameter: `--strict-level {0,1,2}`

- **Level 0**: baseline build + reports only
- **Level 1**: enforce V1/V3/V5; report V2/V4/V6
- **Level 2**: enforce V1/V2/V3/V4/V5; report V6 (promote to fail in v0.2)

Default policy:
- PR CI: Level 1
- Main branch merge gate: Level 2
- Nightly: Level 2 + no-cache rebuild

---

## 5) CI Pipeline Shape

### Job A — Fast Cached Strict (per PR)

1. Install Lean/Lake
2. Restore cache (`~/.elan`, `.lake/packages`)
3. `lake update`
4. Strict Mode Level 1

### Job B — Deterministic Strict (nightly)

1. Install Lean/Lake
2. Clear cache / no prebuilt `.olean`
3. `lake build` for canonical target
4. Strict Mode Level 2

### Job C — Audit Drift (nightly)

Generate trend artifacts:
- placeholder count
- namespace drift count
- orphan count
- vacuity heuristic candidates

---

## 6) Reference Implementation Map (Current Repo)

Existing scripts already cover major classes:

- `scripts/quality/strict-check.sh` covers V1/V3 and canonical build checks
- `scripts/quality/orphaned-check.sh` covers V5
- `scripts/quality/audit_theory.sh` reports proof debt and namespace state

v0.1 implementation plan:

1. Extend `strict-check.sh` with strict-level parameter parsing.
2. Add `scripts/quality/vacuity_scan.py` for V6 heuristics.
3. Add `scripts/quality/axiom_allowlist_check.sh` for V2 allowlist enforcement.
4. Add one markdown artifact output (`reports/strict_mode_report.md`) for CI upload.

---

## 7) Rule-to-Exit-Code Contract

Standardize exit codes for CI diagnostics:

- `10`: placeholder proof violation (V1)
- `11`: axiom leakage violation (V2)
- `12`: import hygiene violation (V3)
- `13`: namespace integrity violation (V4)
- `14`: orphan topology violation (V5)
- `15`: vacuity heuristic threshold violation (future V6 fail mode)

This enables accurate CI annotations and dashboarding.

---

## 8) Migration Plan

### Phase M1 (1–2 weeks)
- Adopt Strict Mode Level 1 in PR CI.
- Publish strict report artifacts.
- Stabilize false-positive rate for V6 scan.

### Phase M2 (2–4 weeks)
- Enforce V2 and V4 in merge gate (Level 2).
- Add explicit axiom allowlist expiration mechanism.

### Phase M3 (after stability)
- Promote selected V6 heuristics to blocking in canonical-only contexts.

---

## 9) Success Metrics

- C0 `sorry`/`admit` count trends to 0 and remains 0.
- No new non-allowlisted axioms in C0.
- No canonical imports from Experimental/Archive.
- Namespace drift in C0 reduced and stabilized.
- False-positive rate of vacuity scanner < 10% on reviewed sample.

---

## 10) Non-Goals (v0.1)

- Proving semantic novelty automatically.
- Replacing human theorem review.
- Enforcing stylistic preferences beyond documented quality audits.

Strict Mode is a guardrail layer, not a substitute for mathematical judgment.
