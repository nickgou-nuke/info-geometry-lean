# BRIEFING — 2026-09-22T12:18:00Z

## Mission
Mathematical Compression Architecture & Phase 0 exploration for Milestone 9: FieldCorrelatorProjection Compression.

## 🔒 My Identity
- Archetype: explorer
- Roles: Mathematical Compression Architect, Lean 4 / CAS Certificate Designer
- Working directory: /home/goutev/info-geometry-lean/.agents/teamwork/teamwork_preview_explorer_fcp_3
- Original parent: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Milestone: Milestone 9 - FieldCorrelatorProjection Compression

## 🔒 Key Constraints
- Read-only investigation — do NOT implement on live files
- BASH-ONLY MODE: Do NOT use write_to_file or replace_file_content; use bash cat << 'EOF'
- Continuous QMS: git add -A whenever files are created or modified in working directory
- Never run lake clean or cache-destructive commands

## Current Parent
- Conversation ID: eb975310-eefa-4a2f-8eb9-5f27c3adff8b
- Updated: 2026-09-22T12:18:00Z

## Investigation State
- **Explored paths**:
  - `lean/InfoGeometry/Detector/FieldCorrelatorProjection.lean` (111 lines, 4 sections)
  - `ORIGINAL_REQUEST.md` & `PROJECT.md`
  - OpenGauss skill: `.agents/plugins/opengauss/skills/opengauss_commands/SKILL.md` (/golf and /refactor workflows)
  - Prior CAS scripts: `scripts/cas_dirac_laplacian_certificate.py`, `.agents/sandbox_surgical_o1/CAS/cas_moore_penrose_certificate.py`, `.agents/sandbox_weak_drazin_o1/CAS/cas_weak_drazin_certificate.py`
  - Background processes: Active Lake build running on Canonical modules; sequential build lock must be respected.
  - Python SymPy environment located at `/home/goutev/.hermes/hermes-agent/venv/bin/python`.
- **Key findings**:
  - `FieldCorrelatorProjection.lean` has 5 major optimization vectors:
    1. Prune `import Mathlib.Tactic` -> keep only `import Mathlib.Data.Real.Basic`.
    2. Eliminate 25-case `cases a <;> cases b <;> simp` in `causal_antisymm` -> replace with `rank_inj (Nat.le_antisymm hab hba)`.
    3. Eliminate `norm_num` in `canonical_chain` -> replace with pure term `⟨Nat.le_succ 195, Nat.le_succ 196, Nat.le_succ 197, Nat.le_succ 198⟩`.
    4. Eliminate `ring` in `projector_pair_bilinear_scale` -> replace with `mul_mul_mul_comm ε₁ ε₂ a b`.
    5. Deduplicate `detector_projection_parabola` by reusing `coincidence_is_rank_two`.
  - CAS certificate generator strategy: SymPy script validating detector projection linearity, mode nullspace idempotence/orthogonality, parabolic invariants, and poset topology.
- **Unexplored areas**: Phase 1 implementation inside `.agents/sandbox_correlator/` by the worker agent.

## Key Decisions Made
- Architected complete O(1) compression plan for `FieldCorrelatorProjection.lean`.
- Defined exact directory layout for `.agents/sandbox_correlator/`.
- Validated SymPy algebra for detector projection, mode annihilation, and causal poset.

## Artifact Index
- DISPATCH.md — incoming dispatch instructions
- BRIEFING.md — persistent working memory
- progress.md — liveness heartbeat
- handoff.md — 5-component handoff report
