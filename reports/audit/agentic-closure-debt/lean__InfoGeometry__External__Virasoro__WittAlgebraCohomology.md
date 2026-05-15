# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.900485+00:00`
Root: `lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **3**
- Advisory: **10**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean` | `advisory` | 16 | 0 | 3 | 10 | 13 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/WittAlgebraCohomology.lean`
- module: `InfoGeometry.External.Virasoro.WittAlgebraCohomology`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L33 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L62 [soft] `skeletal-proof` in `lemma add_bdry_normalizingCochain_apply_lgen_one` — proof appears to close via minimal tactic one-liner
  - L69 [soft] `skeletal-proof` in `lemma add_bdry_normalizingCochain_apply_lgen_zero` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `lemma add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero` — proof appears to close via minimal tactic one-liner
  - L83 [advisory] `local-hypothesis-injection` in `lemma add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L102 [advisory] `existential-packaging` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L122 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L127 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L129 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L160 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L161 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L168 [advisory] `local-hypothesis-injection` in `lemma exists_add_bdry_eq_smul_virasoroCocycle` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

