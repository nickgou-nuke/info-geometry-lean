# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:02.932261+00:00`
Root: `lean/InfoGeometry/Canonical/DrazinGreen.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **5**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DrazinGreen.lean` | `advisory` | 15 | 0 | 5 | 5 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/DrazinGreen.lean`
- module: `InfoGeometry.Canonical.DrazinGreen`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L56 [soft] `skeletal-proof` in `theorem A_pow_mul_DrazinResidueProjector_eq_zero` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem drazinGreen_solves_of_residue_zero` — proof appears to close via minimal tactic one-liner
  - L74 [advisory] `local-hypothesis-injection` in `theorem drazinGreen_solves_of_residue_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L94 [soft] `skeletal-proof` in `theorem residue_zero_of_drazinGreen_solves` — proof appears to close via minimal tactic one-liner
  - L104 [advisory] `local-hypothesis-injection` in `theorem residue_zero_of_drazinGreen_solves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `theorem residue_zero_of_drazinGreen_solves` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L151 [soft] `law-field-locker` in `structure-field DrazinGreenKernelPacket.GreenKernel` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L152 [soft] `law-field-locker` in `structure-field DrazinGreenKernelPacket.kernelRepresentsGreen` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L158 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

