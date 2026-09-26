# BRIEFING — 2026-09-22T12:12:00Z

## Mission
Investigate and analyze `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` for Milestone 9: FieldCorrelatorProjection Compression (Phase 0).

## 🔒 My Identity
- Archetype: explorer
- Roles: Codebase Researcher
- Working directory: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_1
- Original parent: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Milestone: Milestone 9 - FieldCorrelatorProjection Compression (Phase 0)

## 🔒 Key Constraints
- Read-only investigation — do NOT implement or modify live repository source files
- BASH-ONLY MODE: No `write_to_file` or `replace_file_content`. Use `run_command` with bash.
- Continuous QMS: Track files with `git add -A` immediately.
- Never run `lake clean` or cache-destructive commands.

## Current Parent
- Conversation ID: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Updated: 2026-09-22T12:12:00Z

## Investigation State
- **Explored paths**:
  - `ORIGINAL_REQUEST.md`
  - `PROJECT.md`
  - `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean`
  - `lakefile.lean`
  - `lean/InfoGeometry/All.lean`, `lean/InfoGeometry/AllExhaustive.lean`
  - `tools/infra/compute_all_bottlenecks.py`, `tools/infra/compute_bottlenecks.py`
  - `.agents/sandbox_dominators_o1/`, `.agents/sandbox_weak_drazin_o1/`
- **Key findings**:
  - Target file is 111 lines, 3 types, 7 definitions, 11 theorems across 4 sections.
  - Zero inbound imports across the repository (compiled via Lake glob `andSubmodules InfoGeometry`).
  - Outbound imports: `Mathlib.Data.Real.Basic` and monolithic `Mathlib.Tactic` (325 tactic submodules).
  - The 36,529s (10.15h) Delta T in `compute_all_bottlenecks.py` was a wall-clock gap between builds, not an elaboration bottleneck.
  - Identified 5 concrete golf/compression targets:
    1. Prune `Mathlib.Tactic` to `Mathlib.Tactic.Ring`.
    2. Eliminate duplicate theorem `detector_projection_parabola`.
    3. Replace 25-case brute force `simp` in `causal_antisymm` with `Nat.le_antisymm` and `rank_injective`.
    4. Replace `norm_num` with `by decide` in `canonical_chain`.
    5. Replace `ring` with `mul_mul_mul_comm` in `projector_pair_bilinear_scale`.
- **Unexplored areas**: None for Phase 0 researcher mandate.

## Key Decisions Made
- Fully completed anatomy, dependency, and bottleneck analysis of `FieldCorrelatorProjection.lean`.
- Documented complete inventory of declarations and verified root cause of historical 10h Delta T.
- Formulated $O(1)$ and golf refactoring roadmap for the worker/sandbox phase.

## Artifact Index
- DISPATCH.md — Dispatch instructions log
- BRIEFING.md — Persistent working memory
- progress.md — Liveness heartbeat
- handoff.md — Comprehensive 5-component handoff report
