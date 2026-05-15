# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:45.394817+00:00`
Root: `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **14**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/ProjectiveSplitQ11Realization.lean`
- module: `InfoGeometry.Canonical.ProjectiveSplitQ11Realization`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L39 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L51 [soft] `skeletal-proof` in `lemma same_ray_nonzero_right` — proof appears to close via minimal tactic one-liner
  - L57 [advisory] `local-hypothesis-injection` in `lemma same_ray_nonzero_right` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L76 [soft] `skeletal-proof` in `lemma pointed_out_nonzero` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `simp-law-injection` in `simp-declaration projectiveRay_toMathlibProjectivization_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L129 [soft] `simp-law-injection` in `simp-declaration projectiveRay_toMathlibProjectivization_fromMathlibProjectivization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [advisory] `local-hypothesis-injection` in `def mathlibProjectivization_toProjectiveRay` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L157 [soft] `simp-law-injection` in `simp-declaration mathlibProjectivization_toProjectiveRay_toMathlibProjectivization` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L222 [soft] `skeletal-proof` in `lemma modular_j_ne_zero` — proof appears to close via minimal tactic one-liner
  - L230 [soft] `skeletal-proof` in `lemma spectral_epsilon_ne_zero` — proof appears to close via minimal tactic one-liner
  - L239 [soft] `skeletal-proof` in `lemma complex_i_ne_zero` — proof appears to close via minimal tactic one-liner
  - L248 [soft] `simp-law-injection` in `simp-declaration mathlibProjectiveJ_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L254 [soft] `simp-law-injection` in `simp-declaration mathlibProjectiveEpsilon_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L261 [soft] `simp-law-injection` in `simp-declaration mathlibProjectiveI_projectivize` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L268 [soft] `skeletal-proof` in `theorem doubled_modular_j_descends_compatibly` — proof appears to close via minimal tactic one-liner
  - L292 [soft] `skeletal-proof` in `theorem doubled_spectral_epsilon_descends_compatibly` — proof appears to close via minimal tactic one-liner
  - L320 [soft] `skeletal-proof` in `theorem doubled_phaseAxis_descends_compatibly` — proof appears to close via minimal tactic one-liner

