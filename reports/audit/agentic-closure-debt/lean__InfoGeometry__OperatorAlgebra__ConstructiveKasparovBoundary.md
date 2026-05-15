# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:11.953340+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ConstructiveKasparovBoundary.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **13**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ConstructiveKasparovBoundary.lean` | `advisory` | 32 | 0 | 13 | 6 | 19 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ConstructiveKasparovBoundary.lean`
- module: `InfoGeometry.OperatorAlgebra.ConstructiveKasparovBoundary`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L80 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L93 [soft] `simp-law-injection` in `simp-declaration leftDefect_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `skeletal-proof` in `theorem leftDefect_eq` — proof appears to close via minimal tactic one-liner
  - L98 [soft] `simp-law-injection` in `simp-declaration rightDefect_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L100 [soft] `skeletal-proof` in `theorem rightDefect_eq` — proof appears to close via minimal tactic one-liner
  - L103 [soft] `simp-law-injection` in `simp-declaration involutiveDefect_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `skeletal-proof` in `theorem involutiveDefect_eq` — proof appears to close via minimal tactic one-liner
  - L122 [soft] `law-field-locker` in `structure-field KernelProjector.idempotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L146 [soft] `skeletal-proof` in `theorem conjugate_Pker` — proof appears to close via minimal tactic one-liner
  - L164 [soft] `law-field-locker` in `structure-field SuperReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L170 [soft] `law-field-locker` in `structure-field UnitInvariantSuperReadout.read` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L172 [soft] `law-field-locker` in `structure-field UnitInvariantSuperReadout.invariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L216 [soft] `law-field-locker` in `structure-field BoundaryDefectLedger.defectDensity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field BoundaryDefectLedger.derivative_eq_defect` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L230 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L239 [advisory] `local-hypothesis-injection` in `theorem boundaryIntegral_eq_volumeDefect` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)

