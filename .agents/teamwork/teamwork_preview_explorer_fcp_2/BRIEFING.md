# BRIEFING — 2026-09-22T12:13:00Z

## Mission
Profile and analyze compile bottlenecks in InfoGeometry.Detector.FieldCorrelatorProjection for Milestone 9.

## 🔒 My Identity
- Archetype: Proof Bottleneck Profiler / Teamwork Explorer
- Roles: Profiler, Explorer, Synthesizer
- Working directory: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2
- Original parent: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Milestone: Milestone 9 (FieldCorrelatorProjection Compression)

## 🔒 Key Constraints
- BASH-ONLY MODE: Strictly forbidden from using write_to_file or replace_file_content. Use run_command with bash (cat << 'EOF').
- Read-only investigation — do NOT modify or create live repository source files.
- Continuous QMS: git add -A whenever files in working directory are created/modified.
- Sequential Build and Test: inspect running compiler processes before verification, never run concurrent builds, use tools/infra/run_locked_lake_build.py.
- NEVER RUN lake clean, never delete build cache.

## Current Parent
- Conversation ID: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Updated: 2026-09-22T12:13:00Z

## Investigation State
- **Explored paths**:
  - `tools/infra/compute_all_bottlenecks.py` and `tools/infra/compute_bottlenecks.py`
  - `.lake/build/lib/lean/**/*.olean` modification timestamps
  - `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (all 111 lines)
  - `ORIGINAL_REQUEST.md` and `PROJECT.md`
  - Peer explorer reports in `.agents/teamwork/teamwork_preview_explorer_fcp_1/handoff.md`
- **Key findings**:
  1. The 36,529.82s (~10.15h) metric in `compute_all_bottlenecks.py` was a wall-clock inter-session hiatus between 07:17 UTC and 17:26 UTC on 2026-09-19 rather than CPU compilation time.
  2. The file genuinely contains four major proof & AST inefficiencies:
     - `Mathlib.Tactic` monolithic umbrella import.
     - `causal_antisymm`: 25-subgoal combinatorial explosion from `cases a <;> cases b <;> simp`.
     - `canonical_chain`: `norm_num` tactic overkill on kernel-decidable propositions.
     - `detector_projection_parabola`: Verbatim duplication of `coincidence_is_rank_two`.
     - `projector_pair_bilinear_scale`: `ring` tactic used instead of direct `mul_mul_mul_comm`.
- **Unexplored areas**: Phase 1 sandbox implementation in `.agents/sandbox_correlator/`.

## Key Decisions Made
- Fully documented root cause of profiling anomaly and identified all proof compression targets.
- Formulated exact O(1) mathematical replacement strategies and CAS certificate design.
- Delivered complete 5-component handoff report.

## Artifact Index
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2/DISPATCH.md
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2/BRIEFING.md
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2/progress.md
- /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2/handoff.md
