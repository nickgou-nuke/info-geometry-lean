# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:28.569592+00:00`
Root: `lean/InfoGeometry/Canonical/MixtureOfExperts.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **3**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/MixtureOfExperts.lean` | `advisory` | 9 | 0 | 3 | 3 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/MixtureOfExperts.lean`
- module: `InfoGeometry.Canonical.MixtureOfExperts`
- status: `advisory`
- debt_score: `9`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field Expert.apply` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L31 [advisory] `existential-packaging` in `structure MoELayer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L34 [soft] `law-field-locker` in `structure-field MoELayer.experts` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L89 [advisory] `existential-packaging` in `lemma normalizedWeights_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L89 [soft] `skeletal-proof` in `lemma normalizedWeights_sum_one` — proof appears to close via minimal tactic one-liner

