# BRIEFING — 2026-09-22T12:28:00Z

## Mission
Milestone 9: FieldCorrelatorProjection Compression - Sandbox CAS generation, Lean 4 O(1) compression, compilation verification, unified diff, and audit reporting.

## 🔒 My Identity
- Archetype: worker
- Roles: implementer, qa, specialist
- Working directory: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_worker_correlator_1
- Original parent: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Milestone: Milestone 9: FieldCorrelatorProjection Compression

## 🔒 Key Constraints
- BASH-ONLY MODE: All file writes MUST use run_command with bash (cat << 'EOF'). write_to_file and replace_file_content are strictly forbidden.
- SUBAGENT SANDBOX MANDATE: Never touch or modify live repository files (lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean). All work stays in .agents/sandbox_correlator/.
- QMS Protocol: Continuously stage files with git add -A.
- Sequential Build Locking: Inspect running processes and acquire build lock before executing compiler commands. Never lake clean.
- Python SymPy: Use /home/goutev/.hermes/hermes-agent/venv/bin/python.

## Current Parent
- Conversation ID: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Updated: 2026-09-22T12:28:00Z

## Task Summary
- **What to build**: SymPy CAS certificate generator for FieldCorrelatorProjection, refactored Lean 4 file in sandbox with O(1) mathematical optimizations, clean compilation, diff, and verification audit.
- **Success criteria**: 0 errors, 0 warnings, 0 sorry, 0 native_decide; execution speedup; full verification report.
- **Interface contracts**: lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean
- **Code layout**: .agents/sandbox_correlator/

## Key Decisions Made
- Eliminated `import Mathlib.Tactic`, retaining only `import Mathlib.Data.Real.Basic`.
- Solved `causal_antisymm` in $O(1)$ by proving `rank_inj` and combining with `Nat.le_antisymm`, eliminating the 25-subgoal `simp` storm.
- Replaced `norm_num` on `canonical_chain` with direct term witness `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩`.
- Proved `projector_pair_bilinear_scale` with `mul_mul_mul_comm ε₁ ε₂ a b`, eliminating `ring`.
- Replaced `simp [modeTrace]` with targeted `dsimp` and algebraic rewrites.
- Deduplicated `detector_projection_parabola` delegating to `coincidence_is_rank_two`.
- Implemented full SymPy CAS certificate in `cas_field_correlator_certificate.py` and generated `certificate.json`.

## Artifact Index
- `.agents/sandbox_correlator/CAS/cas_field_correlator_certificate.py` — SymPy CAS generator
- `.agents/sandbox_correlator/CAS/certificate.json` — Certified CAS verification packet
- `.agents/sandbox_correlator/lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` — Compressed Lean 4 file
- `.agents/sandbox_correlator/diffs/field_correlator_projection.diff` — Unified diff against live repo file
- `.agents/sandbox_correlator/audit/verification_report.md` — Comprehensive verification audit report
- `.agents/sandbox_correlator/audit/audit_compilation.log` — Compilation audit log
- `.agents/sandbox_correlator/audit/audit_declaration_fidelity.log` — 100% declaration preservation audit
- `.agents/sandbox_correlator/audit/audit_token_scan.log` — Zero forbidden tokens audit
- `.agents/sandbox_correlator/audit/kernel_timing.log` — Profile breakdown and timing log
- `.agents/sandbox_correlator/scripts/verify_sandbox.sh` — End-to-end reproducible verification script

## Change Tracker
- **Files modified**: None in live repo (sandbox-only compliance)
- **Build status**: PASSED (clean compile, 0 errors, 0 warnings, returncode 0)
- **Pending issues**: None

## Quality Status
- **Build/test result**: Passed clean typechecking under build lock
- **Lint status**: 0 linter warnings
- **Tests added/modified**: Full CAS certificate generator & sandbox compilation verification suite
