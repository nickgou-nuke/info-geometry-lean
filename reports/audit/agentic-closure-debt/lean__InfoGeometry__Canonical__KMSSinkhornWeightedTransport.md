# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:23.449491+00:00`
Root: `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **6**
- Hard: **0**
- Soft: **1**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean` | `advisory` | 7 | 0 | 1 | 5 | 6 |

## Findings by file

### `lean/InfoGeometry/Canonical/KMSSinkhornWeightedTransport.lean`
- module: `InfoGeometry.Canonical.KMSSinkhornWeightedTransport`
- status: `advisory`
- debt_score: `7`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L20 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L48 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_kmsControl_of_ibDynamics` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_kmsControl_of_ibDynamics` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L53 [advisory] `local-hypothesis-injection` in `theorem sinkhorn_kmsControl_of_ibDynamics` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L218 [soft] `skeletal-proof` in `lemma kmsResidual_eq_zero_of_satisfiesKMSLike` — proof appears to close via minimal tactic one-liner

