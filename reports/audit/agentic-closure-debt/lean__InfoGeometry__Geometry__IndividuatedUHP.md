# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:37.746122+00:00`
Root: `lean/InfoGeometry/Geometry/IndividuatedUHP.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **24**
- Hard: **0**
- Soft: **7**
- Advisory: **17**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/IndividuatedUHP.lean` | `advisory` | 31 | 0 | 7 | 17 | 24 |

## Findings by file

### `lean/InfoGeometry/Geometry/IndividuatedUHP.lean`
- module: `InfoGeometry.Geometry.IndividuatedUHP`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L50 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L52 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L91 [soft] `skeletal-proof` in `lemma skew_adjoint_quad_form_zero` — proof appears to close via minimal tactic one-liner
  - L100 [advisory] `local-hypothesis-injection` in `lemma skew_adjoint_quad_form_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L124 [advisory] `local-hypothesis-injection` in `theorem K_comp_selfAdjoint_phaseLinear_skew` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [advisory] `local-hypothesis-injection` in `theorem K_comp_selfAdjoint_phaseLinear_skew` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [soft] `law-field-locker` in `structure-field PhysicalSectorDatum.X_star_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L164 [soft] `law-field-locker` in `structure-field PhysicalSectorDatum.Y_star_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L173 [soft] `law-field-locker` in `structure-field PhysicalSectorDatum.Y_pos` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L180 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L202 [soft] `skeletal-proof` in `theorem K_tau_quadratic_eq_neg_Y` — proof appears to close via minimal tactic one-liner
  - L220 [advisory] `local-hypothesis-injection` in `theorem K_tau_quadratic_eq_neg_Y` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L225 [advisory] `local-hypothesis-injection` in `theorem K_tau_quadratic_eq_neg_Y` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [advisory] `local-hypothesis-injection` in `theorem K_tau_quadratic_eq_neg_Y` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L279 [soft] `skeletal-proof` in `theorem no_real_eigenvector` — proof appears to close via minimal tactic one-liner
  - L292 [advisory] `local-hypothesis-injection` in `theorem no_real_eigenvector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L296 [advisory] `local-hypothesis-injection` in `theorem no_real_eigenvector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L304 [advisory] `local-hypothesis-injection` in `theorem no_real_eigenvector` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L316 [soft] `skeletal-proof` in `theorem realShifted_kernel_trivial` — proof appears to close via minimal tactic one-liner
  - L325 [advisory] `local-hypothesis-injection` in `theorem realShifted_kernel_trivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L328 [advisory] `local-hypothesis-injection` in `theorem realShifted_kernel_trivial` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L357 [advisory] `local-hypothesis-injection` in `theorem realShifted_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L360 [advisory] `local-hypothesis-injection` in `theorem realShifted_injective` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

