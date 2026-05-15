# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:14.884941+00:00`
Root: `lean/InfoGeometry/Canonical/HestenesQVandermondeShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **21**
- Hard: **0**
- Soft: **8**
- Advisory: **13**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/HestenesQVandermondeShadow.lean` | `advisory` | 29 | 0 | 8 | 13 | 21 |

## Findings by file

### `lean/InfoGeometry/Canonical/HestenesQVandermondeShadow.lean`
- module: `InfoGeometry.Canonical.HestenesQVandermondeShadow`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `law-field-locker` in `structure-field TwoNodeHestenesChart.Q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L34 [soft] `law-field-locker` in `structure-field TwoNodeHestenesChart.quadratic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [soft] `law-field-locker` in `structure-field TwoNodeHestenesChart.quadraticInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L38 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L69 [advisory] `local-hypothesis-injection` in `theorem quadratic_eq_of_collision` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L80 [advisory] `local-hypothesis-injection` in `theorem norm_eq_of_collision_of_normInvariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L85 [advisory] `bridge-shaped-declaration` in `theorem two_node_hestenes_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L102 [soft] `law-field-locker` in `structure-field A2HestenesChart.Q` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L106 [soft] `law-field-locker` in `structure-field A2HestenesChart.quadratic` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L107 [soft] `law-field-locker` in `structure-field A2HestenesChart.quadraticInvariant` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L110 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L133 [soft] `skeletal-proof` in `theorem exists_quadratic_locked_pair_of_collision` — proof appears to close via minimal tactic one-liner
  - L140 [advisory] `local-hypothesis-injection` in `theorem exists_quadratic_locked_pair_of_collision` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L145 [advisory] `local-hypothesis-injection` in `theorem exists_quadratic_locked_pair_of_collision` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L150 [advisory] `local-hypothesis-injection` in `theorem exists_quadratic_locked_pair_of_collision` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [soft] `skeletal-proof` in `theorem exists_norm_locked_pair_of_collision_of_normInvariant` — proof appears to close via minimal tactic one-liner
  - L161 [advisory] `local-hypothesis-injection` in `theorem exists_norm_locked_pair_of_collision_of_normInvariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L166 [advisory] `local-hypothesis-injection` in `theorem exists_norm_locked_pair_of_collision_of_normInvariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L171 [advisory] `local-hypothesis-injection` in `theorem exists_norm_locked_pair_of_collision_of_normInvariant` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L177 [advisory] `bridge-shaped-declaration` in `theorem a2_hestenes_packet` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof

