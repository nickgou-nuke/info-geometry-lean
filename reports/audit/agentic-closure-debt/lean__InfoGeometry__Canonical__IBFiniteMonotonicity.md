# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:17.122315+00:00`
Root: `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **0**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean` | `advisory` | 5 | 0 | 0 | 5 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/IBFiniteMonotonicity.lean`
- module: `InfoGeometry.Canonical.IBFiniteMonotonicity`
- status: `advisory`
- debt_score: `5`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L136 [advisory] `local-hypothesis-injection` in `lemma probMeasureToPMF_IBNextEncoder_eq_finiteSliceGibbs` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L226 [advisory] `local-hypothesis-injection` in `lemma finiteSlice_kl_gibbs_variational_identity_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L227 [advisory] `local-hypothesis-injection` in `lemma finiteSlice_kl_gibbs_variational_identity_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L294 [advisory] `local-hypothesis-injection` in `lemma finiteSlice_kl_gibbs_variational_identity_of_supportFaithful` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

