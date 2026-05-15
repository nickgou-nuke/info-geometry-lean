# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:22.045158+00:00`
Root: `lean/InfoGeometry/Convex/Euclidean.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **10**
- Hard: **0**
- Soft: **7**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Convex/Euclidean.lean` | `advisory` | 17 | 0 | 7 | 3 | 10 |

## Findings by file

### `lean/InfoGeometry/Convex/Euclidean.lean`
- module: `InfoGeometry.Convex.Euclidean`
- status: `advisory`
- debt_score: `17`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [soft] `skeletal-proof` in `lemma hasFDerivAt_potential` — proof appears to close via minimal tactic one-liner
  - L31 [advisory] `local-hypothesis-injection` in `lemma hasFDerivAt_potential` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L43 [soft] `skeletal-proof` in `lemma hasFDerivAt_scaledPotential` — proof appears to close via minimal tactic one-liner
  - L90 [soft] `simp-law-injection` in `simp-declaration grad_eq_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration metricOp_eq_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L107 [soft] `simp-law-injection` in `simp-declaration scaledHessianGeometry_grad_eq_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `simp-law-injection` in `simp-declaration scaledHessianGeometry_metricOp_eq_smul_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [advisory] `local-hypothesis-injection` in `def scaledHessianGeometry` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L125 [soft] `skeletal-proof` in `theorem divergence_eq_half_sqdist` — proof appears to close via minimal tactic one-liner

