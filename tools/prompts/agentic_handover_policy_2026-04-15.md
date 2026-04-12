# Agentic Handover Policy (DGX Spark)

Effective date: **2026-04-15**

This document defines the production handover from human-led repository operation
to agentic operation for autotheory development.

It is a policy document. It does not override Lean. If this document and source
disagree, Lean source and build results are authoritative.

## 1. Mission

Run a disciplined dual-loop:

- **Exploration loop**: generate candidate structures quickly.
- **Closure loop**: admit only kernel-verified structures into the authoritative lane.

The purpose is high exploration throughput without ontology drift.
Exploration in this stack is symbol-first; language is coordination-only.
See: `tools/prompts/SYMBOL_FIRST_PROTOCOL.md`.

This handover is multilingual in presentation and single-valued in authority:
- repo-native semantic language is preserved
- mathlib-native language is used as assembler language
- docstrings and reports support orientation
- only compiled Lean theorem surfaces close

## 2. Authority Order

1. Lean kernel and build outcomes
2. Repository architecture grammar (`RepDepth`, adjacency, owner/translator/coherence/capstone)
3. Managed DAG policy gates (`dagRefresh`, `dagReports`, `dagDoctor`)
4. Human architecture decisions
5. Agent proposals and narratives

Any conflict is resolved upward in this order.

## 3. Operating Lanes

- **Lane A: Raw Intake (Exploration)**
  - fast hypothesis generation
  - may include unstable files
  - never treated as authoritative truth surface

- **Lane B: Stabilization**
  - owner/translator cleanup
  - import discipline
  - remove wrappers, placeholders, symbolic inflation

- **Lane C: Authoritative**
  - `InfoGeometry.All` and managed DAG products
  - requires green policy gates
  - only this lane is used for closure claims

## 4. Persona Assignment

| Agent | Primary role | Constraint focus |
|---|---|---|
| `NemoClaw` | Architect | layer placement, adjacency, owner boundaries |
| `OpenClaw` | Creator | candidate construction, bridge drafting, local synthesis |
| `DocClaw` | Librarian / Professor | bilingual docstrings, notation maps, blueprint-facing clarity |
| `ClawCode` | Caretaker | gates, cleanup, quarantine, release integrity |

All four are mandatory. No single persona may self-certify closure.

## 5. Entry / Exit Criteria

### Lane A -> Lane B

Required:
- source-level rationale for ownership and layer placement
- no theorem-statement tampering
- explicit list of assumptions still unresolved
- if a module is intended to be bilingual or blueprint-facing, documentation must
  name repo-native statement, mathlib-native statement, and intended comparison surface

### Lane B -> Lane C

Required:
- `lake build InfoGeometry.All` green
- managed DAG cycle green:
  - `python3 tools/infra/dag_refresh.py`
  - `python3 tools/infra/dag_reports.py`
  - `python3 tools/infra/dag_doctor.py` with `fail=0`
- no unresolved symbolic placeholders admitted as closure

## 6. Anti-Inflation Contract

The following are prohibited in closure claims:

- claiming bridge completion from prose alone
- claiming unification from `True` wrappers or theorem-shaped placeholders
- treating unstable/raw intake modules as authoritative without stabilization
- allowing bilingual modules to omit explicit translation/comparison theorem ownership

All “unity/coalescence” claims must point to explicit compiled bridge theorems.

## 7. Quarantine Discipline

Raw or unstable modules remain outside Lane C until stabilized.

- Quarantine registry: `scripts/quality/quarantine_manifest.txt`
- Coverage gate includes only non-quarantined declaration-bearing files
- Quarantine is temporary and reviewable, not silent deletion

## 8. Handover Protocol (Daily)

Each cycle produces a short machine-auditable handoff:

1. **Architect note**: what file owns what, and why.
2. **Creator note**: what was introduced/changed.
3. **Librarian note**: docstring/notation coverage and references.
4. **Caretaker note**: gate results and unresolved defects.
5. **Artifact bundle**: updated DAG/report outputs with timing sidecars.

## 9. Date-Bound Activation

Starting **2026-04-15**, agentic infrastructure is the default operating mode.

Human override is allowed when:

- gate behavior is inconsistent with source reality
- architecture-layer decisions need explicit adjudication
- safety/sandbox policy needs update

## 11. Self-Learning Requirement

Starting with the activation of the Alchemical Loop, the system enforces a
**Success Memory** constraint:

- No agent may close a proof (Lane B -> Lane C) without extracting the
  **Tactic Trace** that made the closure possible.
- Extraction method: `lake script run dagDoctor --trace`.
- Recording target: `skills/automated-learning/winning_traces.jsonl`.
- The record must include the symbol name, the successful tactic sequence,
  and the alchemical phase transition (e.g., Citrinitas -> Rubedo).

This ensures the Spire constantly formalizes its own "common unconscious" into
reusable tactical knowledge.
