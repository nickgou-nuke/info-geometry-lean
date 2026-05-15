# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:10.687918+00:00`
Root: `lean/InfoGeometry/Canonical/WeylAlternatingNumeratorShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **5**
- Advisory: **7**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylAlternatingNumeratorShadow.lean` | `advisory` | 17 | 0 | 5 | 7 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylAlternatingNumeratorShadow.lean`
- module: `InfoGeometry.Canonical.WeylAlternatingNumeratorShadow`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `law-field-locker` in `structure-field AlternatingGibbsNumeratorData.sign` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L43 [soft] `law-field-locker` in `structure-field AlternatingGibbsNumeratorData.exponent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L48 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L61 [soft] `skeletal-proof` in `theorem value_eq_sum_terms` — proof appears to close via minimal tactic one-liner
  - L66 [soft] `skeletal-proof` in `theorem term_eq_signed_gibbs` — proof appears to close via minimal tactic one-liner
  - L79 [advisory] `bridge-shaped-declaration` in `theorem alternating_gibbs_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L105 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L109 [soft] `skeletal-proof` in `theorem numerator_is_alternating_gibbs` — proof appears to close via minimal tactic one-liner
  - L117 [advisory] `existential-packaging` in `theorem denominator_zero_iff_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L126 [advisory] `bridge-shaped-declaration` in `theorem numerator_denominator_shadow_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L126 [advisory] `existential-packaging` in `theorem numerator_denominator_shadow_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

