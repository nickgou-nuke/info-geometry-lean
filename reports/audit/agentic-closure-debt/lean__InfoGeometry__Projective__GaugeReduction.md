# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:30.706547+00:00`
Root: `lean/InfoGeometry/Projective/GaugeReduction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **13**
- Hard: **0**
- Soft: **7**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Projective/GaugeReduction.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/Projective/GaugeReduction.lean`
- module: `InfoGeometry.Projective.GaugeReduction`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `simp-law-injection` in `simp-declaration generalizedKL_eq_klLike_add_Z` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L28 [soft] `skeletal-proof` in `lemma generalizedKL_eq_klLike_add_Z` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `simp-law-injection` in `simp-declaration generalizedKL_eq_klLike_of_Z_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L94 [advisory] `local-hypothesis-injection` in `lemma klLike_scale_scale_two` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L148 [advisory] `existential-packaging` in `lemma generalizedKL_projective_radial_decomposition` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L287 [soft] `simp-law-injection` in `simp-declaration generalizedKL_normalize_eq_klLike_normalize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L290 [advisory] `existential-packaging` in `lemma generalizedKL_normalize_eq_klLike_normalize` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L290 [soft] `skeletal-proof` in `lemma generalizedKL_normalize_eq_klLike_normalize` — proof appears to close via minimal tactic one-liner
  - L307 [soft] `simp-law-injection` in `simp-declaration generalizedKL_scale_scale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L310 [soft] `skeletal-proof` in `lemma generalizedKL_scale_scale` — proof appears to close via minimal tactic one-liner
  - L314 [advisory] `local-hypothesis-injection` in `lemma generalizedKL_scale_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L320 [advisory] `local-hypothesis-injection` in `lemma generalizedKL_scale_scale` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

