# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:56.198731+00:00`
Root: `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **12**
- Hard: **0**
- Soft: **3**
- Advisory: **9**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean` | `advisory` | 15 | 0 | 3 | 9 | 12 |

## Findings by file

### `lean/InfoGeometry/Canonical/SinkhornKMSCore.lean`
- module: `InfoGeometry.Canonical.SinkhornKMSCore`
- status: `advisory`
- debt_score: `15`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [advisory] `existential-packaging` in `abbrev SatisfiesKMSLike` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L52 [advisory] `existential-packaging` in `def kreinRouterModularHamiltonian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L62 [soft] `simp-law-injection` in `simp-declaration kreinRouterModularHamiltonian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `skeletal-proof` in `lemma kreinRouterModularHamiltonian_isKreinSelfAdjoint` — proof appears to close via minimal tactic one-liner
  - L73 [advisory] `existential-packaging` in `abbrev routerModularHamiltonian` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L83 [soft] `simp-law-injection` in `simp-declaration routerModularHamiltonian_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L172 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L178 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_step_kmsClosure_of_approxClosure_of_barrierZero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_control_of_step_kmsClosure` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L237 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_control_of_step_kmsClosure` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

