# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:29.510502+00:00`
Root: `lean/InfoGeometry/ExponentialFamily/Finite.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **4**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/ExponentialFamily/Finite.lean` | `advisory` | 15 | 0 | 4 | 7 | 11 |

## Findings by file

### `lean/InfoGeometry/ExponentialFamily/Finite.lean`
- module: `InfoGeometry.ExponentialFamily.Finite`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [soft] `law-field-locker` in `structure-field FiniteExponentialFamilyData.stat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field FiniteExponentialFamilyData.base_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L47 [advisory] `existential-packaging` in `def familyDensity` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L54 [advisory] `existential-packaging` in `lemma familyPartition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L69 [advisory] `local-hypothesis-injection` in `lemma familyPartition_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L73 [soft] `skeletal-proof` in `lemma familyDensity_eq` — proof appears to close via minimal tactic one-liner
  - L78 [advisory] `local-hypothesis-injection` in `lemma familyDensity_eq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L88 [soft] `skeletal-proof` in `lemma familyNormalization` — proof appears to close via minimal tactic one-liner
  - L92 [advisory] `local-hypothesis-injection` in `lemma familyNormalization` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L107 [advisory] `existential-packaging` in `def toFiniteExponentialFamily` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

