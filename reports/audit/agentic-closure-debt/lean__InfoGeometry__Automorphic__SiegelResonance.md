# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:36.485710+00:00`
Root: `lean/InfoGeometry/Automorphic/SiegelResonance.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **27**
- Hard: **0**
- Soft: **17**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Automorphic/SiegelResonance.lean` | `advisory` | 44 | 0 | 17 | 10 | 27 |

## Findings by file

### `lean/InfoGeometry/Automorphic/SiegelResonance.lean`
- module: `InfoGeometry.Automorphic.SiegelResonance`
- status: `advisory`
- debt_score: `44`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L48 [soft] `law-field-locker` in `structure-field SiegelEisensteinWitness.siegel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L49 [soft] `law-field-locker` in `structure-field SiegelEisensteinWitness.eisenstein` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L50 [soft] `law-field-locker` in `structure-field SiegelEisensteinWitness.section_axiom` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L61 [soft] `simp-law-injection` in `simp-declaration section_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L110 [soft] `simp-law-injection` in `simp-declaration boundaryProjector_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L112 [soft] `skeletal-proof` in `theorem boundaryProjector_apply` — proof appears to close via minimal tactic one-liner
  - L115 [soft] `simp-law-injection` in `simp-declaration cuspidalProjector_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `skeletal-proof` in `theorem cuspidalProjector_apply` — proof appears to close via minimal tactic one-liner
  - L202 [soft] `skeletal-proof` in `theorem siegel_cuspidalProjector_apply` — proof appears to close via minimal tactic one-liner
  - L221 [soft] `skeletal-proof` in `theorem range_cuspidalProjector_eq_ker_siegel` — proof appears to close via minimal tactic one-liner
  - L238 [advisory] `local-hypothesis-injection` in `theorem range_cuspidalProjector_eq_ker_siegel` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L276 [soft] `skeletal-proof` in `theorem ker_cuspidalProjector_eq_range_eisenstein` — proof appears to close via minimal tactic one-liner
  - L286 [advisory] `local-hypothesis-injection` in `theorem ker_cuspidalProjector_eq_range_eisenstein` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L308 [soft] `skeletal-proof` in `theorem range_boundaryProjector_inf_range_cuspidalProjector_eq_bot` — proof appears to close via minimal tactic one-liner
  - L325 [advisory] `local-hypothesis-injection` in `theorem range_boundaryProjector_inf_range_cuspidalProjector_eq_bot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L327 [advisory] `local-hypothesis-injection` in `theorem range_boundaryProjector_inf_range_cuspidalProjector_eq_bot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L340 [advisory] `local-hypothesis-injection` in `theorem fixed_by_cuspidalProjector_iff_siegel_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L345 [soft] `skeletal-proof` in `theorem boundaryProjector_eisenstein` — proof appears to close via minimal tactic one-liner
  - L352 [soft] `skeletal-proof` in `theorem cuspidalProjector_eisenstein` — proof appears to close via minimal tactic one-liner
  - L359 [soft] `skeletal-proof` in `theorem bulk_decomposition` — proof appears to close via minimal tactic one-liner
  - L373 [soft] `skeletal-proof` in `theorem range_eisenstein_inf_ker_siegel_eq_bot` — proof appears to close via minimal tactic one-liner
  - L384 [advisory] `local-hypothesis-injection` in `theorem range_eisenstein_inf_ker_siegel_eq_bot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L386 [advisory] `local-hypothesis-injection` in `theorem range_eisenstein_inf_ker_siegel_eq_bot` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L408 [advisory] `local-hypothesis-injection` in `theorem range_eisenstein_sup_ker_siegel_eq_top` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L434 [soft] `skeletal-proof` in `theorem mem_globalCuspidalSubspace_iff` — proof appears to close via minimal tactic one-liner

