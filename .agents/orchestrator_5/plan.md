# Master Orchestration Plan: Global Refactoring Swarm (orchestrator_5)

## Phase 0: Survey & Target Identification
1. Dispatch 3 parallel Explorers:
   - Explorer 1 (`survey_r5_1`): Scan the repository for remaining `native_decide` and brute-force tactic bottlenecks. Enumerate target files, counts, and modules.
   - Explorer 2 (`survey_r5_2`): Deep dive into top candidate targets' mathematical statements, structure (e.g. matrix/bracket/combinatorics), and CAS O(1) amenability.
   - Explorer 3 (`survey_r5_3`): Audit sandbox environment, build locks, E2E suite coverage, and existing CAS scripts.
2. Synthesize findings into `PROJECT.md § Feature Inventory` and select prioritized target(s) for iterative sandbox refactoring.

## Phase 1: Iterative Sandbox Deployment
For each prioritized target:
1. Initialize isolated sandbox `.agents/sandbox_<target>/`.
2. Generate exact CAS O(1) integer/rational certificates and terms via python/SymPy script.
3. Dispatch Worker to refactor the target within the sandbox.
4. Verify compilation under sequential build lock (`run_locked_lake_build.py`).

## Phase 2: Sandbox Verification Panel
1. Dispatch 2 independent Reviewers to inspect mathematical rigor and proof validity.
2. Dispatch 2 Challengers for adversarial stress-testing and negative mutation testing.
3. Dispatch 1 Forensic Auditor (`teamwork_preview_auditor`) for axiom purity (zero `Lean.ofReduceBool`, zero `sorryAx`) and anti-facade checks.
4. Record verdicts in `GATE_STATUS.md`.

## Phase 3: Live Promotion & E2E Validation
1. Promote verified file to live repository.
2. Run locked Lake build.
3. Execute full E2E test suite (`./tools/e2e_cas_o1_suite.sh --tier all`).
4. Enforce Test 2.5 proposition fidelity on refactored targets.
5. Track changes with `git add -A`.

## Phase 4: Final Victory Audit & Reporting
1. Dispatch independent Victory Auditor to perform final uncorrupted audit.
2. Synthesize results and report victory to the Sentinel.
