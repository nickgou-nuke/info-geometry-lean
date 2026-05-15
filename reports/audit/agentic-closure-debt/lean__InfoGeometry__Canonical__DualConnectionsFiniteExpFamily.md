# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:06.126592+00:00`
Root: `lean/InfoGeometry/Canonical/DualConnectionsFiniteExpFamily.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **3**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/DualConnectionsFiniteExpFamily.lean` | `advisory` | 12 | 0 | 3 | 6 | 9 |

## Findings by file

### `lean/InfoGeometry/Canonical/DualConnectionsFiniteExpFamily.lean`
- module: `InfoGeometry.Canonical.DualConnectionsFiniteExpFamily`
- status: `advisory`
- debt_score: `12`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `local-hypothesis-injection` in `def finiteExpFamilyFinProb` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L31 [advisory] `local-hypothesis-injection` in `def finiteExpFamilyFinProb` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L51 [soft] `simp-law-injection` in `simp-declaration finiteExpFamilyProbMap_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L62 [advisory] `local-hypothesis-injection` in `lemma finiteExpFamilyProbMap_apply_toReal` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L64 [advisory] `existential-packaging` in `def fisherCovarianceBilinear` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L73 [soft] `simp-law-injection` in `simp-declaration fisherMetric_eq_covariance` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [advisory] `local-hypothesis-injection` in `lemma fisherBilinear_eq_expectation_mul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L144 [soft] `simp-law-injection` in `simp-declaration finiteExpFamilyAlphaConnection_deformation` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

