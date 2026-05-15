# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:44.755836+00:00`
Root: `lean/InfoGeometry/Information/MultiLogPotential.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **6**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Information/MultiLogPotential.lean` | `advisory` | 21 | 0 | 6 | 9 | 15 |

## Findings by file

### `lean/InfoGeometry/Information/MultiLogPotential.lean`
- module: `InfoGeometry.Information.MultiLogPotential`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L14 [soft] `law-field-locker` in `structure-field FiniteExpFamily.stat` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L15 [soft] `law-field-locker` in `structure-field FiniteExpFamily.base` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L16 [soft] `law-field-locker` in `structure-field FiniteExpFamily.base_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L32 [advisory] `existential-packaging` in `lemma partition_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L64 [advisory] `existential-packaging` in `lemma density_nonneg` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L76 [advisory] `existential-packaging` in `lemma density_pos` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L88 [advisory] `existential-packaging` in `lemma density_sum_one` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L195 [soft] `skeletal-proof` in `lemma expectation_linearStat` — proof appears to close via minimal tactic one-liner
  - L217 [soft] `skeletal-proof` in `lemma centeredLinearStat_eq_sum_centeredStat` — proof appears to close via minimal tactic one-liner
  - L225 [advisory] `local-hypothesis-injection` in `lemma centeredLinearStat_eq_sum_centeredStat` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L241 [soft] `skeletal-proof` in `lemma fisher_as_variance` — proof appears to close via minimal tactic one-liner
  - L281 [advisory] `existential-packaging` in `theorem fisher_positive_semidefinite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L293 [advisory] `existential-packaging` in `theorem fisher_positive_definite_of_nonconstant_linearStats` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L323 [advisory] `existential-packaging` in `theorem fisher_positive_definite` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

