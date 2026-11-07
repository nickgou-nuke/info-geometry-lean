# QMS Skill — Quality Management System

Implements QMS-SOP-ALC-001 v4.1 (docs/ALCHEMICAL_QMS_SOP.md), the controlled
confabulation-to-Lean transmutation procedure with role separation and Gate 0-5
pipeline.

## Purpose

Separate conceptual payload, theorem candidate, model assumption, external
evidence, and documentation-only material before Lean generation begins. The
QMS is not a proof authority — Lean kernel-checked source is.

## Roles (mutually exclusive per task)

| Role | Responsibility | Forbidden |
|------|---------------|-----------|
| **G-A** Generation Agent | Ingest latent bundles, write candidate code/task packets | Declaring acceptance, reviewing own work |
| **A-A** Audit Agent | Independently read artifacts, classify gaps G1–G5, recommend CAPA | Authoring the artifact under audit |
| **QA-A** Acceptance Quality Agent | Run final compile/build/audit gates, accept/reject | Writing theorem content for the artifact |
| **Orchestrator** | Route work, record status | Using own coordination notes as proof authority |

## Gate 0-5 pipeline

```bash
# Gate 0 — Intake: formal intent envelope (G-A)
python3 tools/qms/run_qms.py intent \
  --task-id T-XXX \
  --source-text "<claim or prompt>" \
  --intake-classification theorem-bearing \
  --target-status theorem-backed \
  --risk-level R2 \
  --formal-object Foo.bar \
  --acceptance-theorem foo_bar \
  --scope-label finite-stage \
  --out artifacts/qms/T-XXX-intent_envelope.json

# Gate 1 — Owner-first search (G-A)
python3 tools/qms/run_qms.py owner-search \
  --task-id T-XXX \
  --artifact lean/InfoGeometry/Foo.lean \
  --query foo_bar \
  --query RelatedConcept \
  --owner-file lean/InfoGeometry/Foo.lean

# Gate 1 executes repository filename and Lean-source searches for each exact
# query, searches available `.lake/packages` sources, and reads the artifact and
# named owner files. Optional `--search-lane` values are navigation context only.

# Gate 2 — Generation controls (G-A)
python3 tools/qms/run_qms.py generation \
  --task-id T-XXX \
  --artifact src/InfoGeometry/Foo.lean

# Gate 2 runs the artifact-scoped placeholder audit and broad-import scan only.
# Its PASS is limited to those static checks; semantic controls remain open for
# the independent Gate 3 audit.

# Gate 3 — Sterile compile + independent audit (QA-A)
python3 tools/qms/run_qms.py compile \
  --task-id T-XXX \
  --artifact src/InfoGeometry/Foo.lean \
  --scope-label finite-stage

# Gate 4 — CAPA loop (Orchestrator)
python3 tools/qms/run_qms.py capa create \
  --task-id T-XXX \
  --finding "..." \
  --root-cause "..." \
  --corrective-action "..." \
  --preventive-action "..." \
  --verification-command "..."

# Gate 5 — Acceptance (QA-A)
python3 tools/qms/run_qms.py accept \
  --task-id T-XXX \
  --artifact lean/InfoGeometry/Foo.lean \
  --verdict ACCEPTED \
  --status-tag kernel_verified --status-tag axiom_audited \
  --command "lake env lean lean/InfoGeometry/Foo.lean" \
  --output "build succeeded" \
  --working-tree-scope clean

# Quick gate (SOP §18)
python3 tools/qms/run_qms.py quick-gate --task-id T-XXX

# CAPA index
python3 tools/qms/run_qms.py capa-index
```

## Output artifacts

- `artifacts/qms/<task-id>-intent_envelope.json` — formal intent envelope (Gate 0)
- `artifacts/qms/<task-id>-audit_report.json` — A-A audit telemetry (Gate 3)
- `artifacts/qms/<task-id>-qa.json` — QA-A acceptance record (Gate 5)
- `artifacts/qms/capa/<CAPA-ID>.json` — CAPA records (Gate 4)
- `artifacts/qms/capa/capa_index.json` — aggregated CAPA index

## Gap taxonomy (A-A)

- **G1**: syntax, parser, or elaboration failure
- **G2**: type mismatch, missing typeclass instance, universe problem, import/API mismatch
- **G3**: missing algebraic lemma, unproved side condition, missing rewrite theorem
- **G4**: false target, vacuous target, quotient collapse, countermodel found, theorem strength beyond owner authority
- **G5**: scope pollution or import-dependent success (undeclared broad imports, namespace leakage)

## Acceptance verdicts (QA-A)

- `ACCEPTED` — all criteria met, tag `verified_logos`
- `ACCEPTED_WITH_LIMITED_SCOPE` — narrower than initiating claim
- `REJECTED` — compile failure, hidden proof debt, false target, or false surface

## Constraints

- Permitted foundational axioms: `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, `axiom`, `postulate`, `Prop := True`, or vacuous wrappers in promoted surfaces
- Theorem names must be content-descriptive, not ambition-descriptive
- No broad `import Mathlib` or `InfoGeometry.All` in sterile candidate modules
- No full `LieRing` instance for full Zorn/split-octonion element commutator
- G-A and A-A must be different contexts; QA-A must not author accepted content
