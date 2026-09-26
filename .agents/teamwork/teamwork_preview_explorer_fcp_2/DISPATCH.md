## 2026-09-22T12:07:56Z
Task received from parent:
Explore Phase 0 for Milestone 9: FieldCorrelatorProjection Compression.
Working directory: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_2
Repository root: /home/goutev/info-geometry-lean
Original Request: /home/goutev/info-geometry-lean/.agents/teamwork/ORIGINAL_REQUEST.md
Project Plan: /home/goutev/info-geometry-lean/PROJECT.md

MANDATORY CONSTRAINTS:
1. BASH-ONLY MODE: Strictly forbidden from using write_to_file or replace_file_content. Use run_command with bash (cat << 'EOF').
2. Read-Only Exploration: NEVER modify or create live repository source files.
3. Continuous QMS: Track files with git add -A.

TASK:
1. Read ORIGINAL_REQUEST.md and PROJECT.md.
2. Investigate why InfoGeometry.Detector.FieldCorrelatorProjection is a primary global compile bottleneck.
3. Examine existing profiling scripts/data in tools/infra/compute_all_bottlenecks.py, tools/infra/compute_bottlenecks.py, or targets/logs.
4. Pinpoint the exact lemmas, theorems, definitions, or proof terms in FieldCorrelatorProjection.lean that cause slow elaboration or compile gaps.
5. Write detailed bottleneck analysis and handoff report to handoff.md.
6. Update progress.md.
7. Send message to orchestrator.
