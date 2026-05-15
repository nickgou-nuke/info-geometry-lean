# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:21.724204+00:00`
Root: `lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **8**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean` | `advisory` | 19 | 0 | 8 | 3 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/KKTClosureSymmetry.lean`
- module: `InfoGeometry.Canonical.KKTClosureSymmetry`
- status: `advisory`
- debt_score: `19`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L24 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L64 [soft] `simp-law-injection` in `simp-declaration conjugateUnit_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `skeletal-proof` in `theorem conjugateUnit_one` — proof appears to close via minimal tactic one-liner
  - L70 [soft] `simp-law-injection` in `simp-declaration conjugateUnit_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `skeletal-proof` in `theorem conjugateUnit_mul` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `skeletal-proof` in `theorem conjugateUnit_inv_eq_of_eq` — proof appears to close via minimal tactic one-liner
  - L86 [advisory] `local-hypothesis-injection` in `theorem conjugateUnit_inv_eq_of_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L133 [soft] `law-field-locker` in `structure-field KKTClosureSymmetry.preserves` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `skeletal-proof` in `theorem anticommutator_QD_QD_eq_two_smul_kinetic_plus_central` — proof appears to close via minimal tactic one-liner
  - L275 [soft] `skeletal-proof` in `theorem ZD_isDrazinLaneCentral` — proof appears to close via minimal tactic one-liner

