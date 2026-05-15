# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:13.951139+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/FierzNoetherBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **5**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/FierzNoetherBridge.lean` | `advisory` | 14 | 0 | 5 | 4 | 9 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/FierzNoetherBridge.lean`
- module: `InfoGeometry.OperatorAlgebra.FierzNoetherBridge`
- status: `advisory`
- debt_score: `14`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [soft] `law-field-locker` in `structure-field ModularNoetherReadout.flow` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L51 [soft] `law-field-locker` in `structure-field ModularNoetherReadout.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L57 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L60 [soft] `skeletal-proof` in `theorem flow_apply` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem readout_apply` — proof appears to close via minimal tactic one-liner
  - L68 [soft] `skeletal-proof` in `theorem charge_apply` — proof appears to close via minimal tactic one-liner
  - L93 [advisory] `local-hypothesis-injection` in `theorem map_zero_of_additive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L95 [advisory] `local-hypothesis-injection` in `theorem map_zero_of_additive` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

