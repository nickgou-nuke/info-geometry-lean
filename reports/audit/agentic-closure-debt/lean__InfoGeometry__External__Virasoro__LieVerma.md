# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:32.571084+00:00`
Root: `lean/InfoGeometry/External/Virasoro/LieVerma.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **8**
- Hard: **0**
- Soft: **5**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/LieVerma.lean` | `advisory` | 13 | 0 | 5 | 3 | 8 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/LieVerma.lean`
- module: `InfoGeometry.External.Virasoro.LieVerma`
- status: `advisory`
- debt_score: `13`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L133 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L158 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L179 [soft] `skeletal-proof` in `lemma VermaHW.smul_eq_algebraHom_smul` — proof appears to close via minimal tactic one-liner
  - L193 [soft] `skeletal-proof` in `lemma VermaHW.upper_smul_hwVec` — proof appears to close via minimal tactic one-liner
  - L197 [soft] `skeletal-proof` in `lemma VermaHW.cartan_smul_hwVec` — proof appears to close via minimal tactic one-liner
  - L233 [soft] `law-field-locker` in `class-field HasCentralValue.central_smul'` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L234 [soft] `simp-law-injection` in `simp-declaration HasCentralValue.central_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

