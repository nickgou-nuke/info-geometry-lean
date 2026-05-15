# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:07.736375+00:00`
Root: `lean/InfoGeometry/Canonical/FierzReadout.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/FierzReadout.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/Canonical/FierzReadout.lean`
- module: `InfoGeometry.Canonical.FierzReadout`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `law-field-locker` in `structure-field FierzChannelReadout.scalar` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `law-field-locker` in `structure-field FierzChannelReadout.symplectic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [soft] `law-field-locker` in `structure-field FierzChannelReadout.hilbert` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [soft] `law-field-locker` in `structure-field FierzChannelReadout.area` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L33 [soft] `law-field-locker` in `structure-field FierzChannelReadout.fierzIdentity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L99 [soft] `skeletal-proof` in `theorem toQuantumPresentation_metricReadout` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `theorem toQuantumPresentation_phaseReadout` — proof appears to close via minimal tactic one-liner
  - L114 [soft] `skeletal-proof` in `theorem toQuantumPresentationWith_metricReadout` — proof appears to close via minimal tactic one-liner
  - L126 [soft] `skeletal-proof` in `theorem toQuantumPresentationWith_phaseReadout` — proof appears to close via minimal tactic one-liner
  - L139 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

