# Master Plan: Surgical Refactoring & Compression Swarm (BASH-ONLY MODE)

## Objective
Identify and eliminate the worst remaining `native_decide` compiler bottlenecks in `/home/goutev/info-geometry-lean` with surgical precision, using OpenGauss CAS O(1) certificates and isolated sandbox verification.

## Phases

### Phase 0: Bottleneck Prioritization Survey
- Dispatch 3 parallel Explorers:
  - `teamwork_preview_explorer_survey_r3_1`: Repo-wide scan of all remaining `native_decide` occurrences, categorizing files, counts, and compile/elaboration cost.
  - `teamwork_preview_explorer_survey_r3_2`: Mathematical & algebraic inspection of the worst bottleneck candidates (analyzing matrices, complexes, or boolean predicates being decided).
  - `teamwork_preview_explorer_survey_r3_3`: Sandbox compilation environment assessment, dependency analysis, and OpenGauss/CAS tooling verification.
- Synthesize findings, pick the highest-impact target file for surgical refactoring.

### Phase 1: Sandbox Initialization & CAS O(1) Generator
- Create isolated sandbox directory (e.g. `.agents/sandbox_surgical_o1/`).
- Develop/verify CAS script to generate integer/rational certificates and O(1) `rfl` terms.

### Phase 2: Sandbox Implementation
- Dispatch Worker to rewrite the targeted theorems in the sandbox file.
- Verify compilation inside sandbox using `python3 tools/infra/run_locked_lake_build.py --wait-for-build-lock`.
- Eliminate `native_decide` entirely while preserving verbatim proposition statements.

### Phase 3: Verification Panel (Reviewers, Challengers, Auditor)
- Dispatch 2 independent Reviewers.
- Dispatch 2 adversarial Challengers (stress-testing AST signatures, negative mutations).
- Dispatch 1 Forensic Auditor (`teamwork_preview_auditor`) for axiomatic verification (zero `Lean.ofReduceBool`, zero `sorryAx`).
- Compile Gate Status.

### Phase 4: Surgical Promotion & E2E Verification
- Promote verified sandbox file into live repository target.
- Re-run full E2E test suite (`./tools/e2e_cas_o1_suite.sh` or updated suite).
- Ensure zero warnings, zero errors, reduced compile time.

### Phase 5: Victory Audit & Handoff
- Dispatch Victory Auditor.
- Report complete results to parent caller.
