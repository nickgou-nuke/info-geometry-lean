# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:50.202990+00:00`
Root: `lean/InfoGeometry/Canonical/ChiralAnomaly.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **6**
- Advisory: **8**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ChiralAnomaly.lean` | `advisory` | 20 | 0 | 6 | 8 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/ChiralAnomaly.lean`
- module: `InfoGeometry.Canonical.ChiralAnomaly`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L32 [soft] `skeletal-proof` in `theorem normal_inverse_anomaly_vanishes` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `skeletal-proof` in `lemma routingEpsilon_le_one_of_simplex` — proof appears to close via minimal tactic one-liner
  - L80 [advisory] `local-hypothesis-injection` in `lemma routingEpsilon_le_one_of_simplex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L81 [advisory] `local-hypothesis-injection` in `lemma routingEpsilon_le_one_of_simplex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [advisory] `local-hypothesis-injection` in `lemma routingEpsilon_le_one_of_simplex` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L96 [advisory] `existential-packaging` in `lemma routingEpsilon_eq_semantic_gap_abs` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L109 [advisory] `existential-packaging` in `theorem exists_routingEpsilon_of_bistochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L130 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L132 [advisory] `existential-packaging` in `theorem exists_routingEpsilon_of_mem_doublyStochastic` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L150 [soft] `classical-witness-smuggling` in `def sinkhornPermutationWeights` — declaration uses Classical/choice/Nonempty witness extraction; require constructive payload readback or explicit nonconstructive boundary
  - L210 [soft] `law-field-locker` in `structure-field DoublyStochasticSinkhornTrajectory.mem_doublyStochastic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L310 [soft] `skeletal-proof` in `theorem sinkhornIterate_step_control` — proof appears to close via minimal tactic one-liner
  - L331 [soft] `skeletal-proof` in `theorem sinkhornIterate_generator_step_control` — proof appears to close via minimal tactic one-liner

