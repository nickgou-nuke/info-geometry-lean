# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:12.758304+00:00`
Root: `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **2**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean` | `advisory` | 12 | 0 | 2 | 8 | 10 |

## Findings by file

### `lean/InfoGeometry/Canonical/WeylLocalCancellationShadow.lean`
- module: `InfoGeometry.Canonical.WeylLocalCancellationShadow`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L34 [advisory] `existential-packaging` in `structure LocalCancellationShadowPacket` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L36 [soft] `law-field-locker` in `structure-field LocalCancellationShadowPacket.numerator_zero_on_collision` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L45 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L73 [advisory] `existential-packaging` in `theorem denominator_eq_zero_iff_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L87 [advisory] `existential-packaging` in `theorem numerator_eq_zero_of_collision` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [soft] `skeletal-proof` in `theorem quotient_eq_ratio` — proof appears to close via minimal tactic one-liner
  - L114 [advisory] `bridge-shaped-declaration` in `theorem quotient_domain_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L129 [advisory] `bridge-shaped-declaration` in `theorem local_cancellation_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L129 [advisory] `existential-packaging` in `theorem local_cancellation_packet` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

