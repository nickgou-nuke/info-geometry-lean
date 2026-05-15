# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:03.278302+00:00`
Root: `lean/InfoGeometry/Canonical/SuperUnified.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **9**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SuperUnified.lean` | `advisory` | 22 | 0 | 9 | 4 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/SuperUnified.lean`
- module: `InfoGeometry.Canonical.SuperUnified`
- status: `advisory`
- debt_score: `22`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `skeletal-proof` in `theorem clifford_decomposition` — proof appears to close via minimal tactic one-liner
  - L38 [advisory] `local-hypothesis-injection` in `theorem clifford_decomposition` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [soft] `law-field-locker` in `structure-field SuperKaehlerStructure.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L63 [soft] `law-field-locker` in `structure-field SuperKaehlerStructure.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field SuperKaehlerStructure.anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L65 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L65 [soft] `section-law-variable` in `variable S` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption
  - L75 [soft] `skeletal-proof` in `theorem symplectic_is_complex_structure` — proof appears to close via minimal tactic one-liner
  - L80 [advisory] `local-hypothesis-injection` in `theorem symplectic_is_complex_structure` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L121 [soft] `skeletal-proof` in `theorem bracket_boson_boson_is_bosonic` — proof appears to close via minimal tactic one-liner
  - L199 [soft] `skeletal-proof` in `theorem bracket_fermion_fermion_is_bosonic` — proof appears to close via minimal tactic one-liner
  - L228 [soft] `skeletal-proof` in `theorem bracket_boson_fermion_is_fermionic` — proof appears to close via minimal tactic one-liner

