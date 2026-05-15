# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:44.829019+00:00`
Root: `lean/InfoGeometry/Canonical/BottDirac.lean`
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
| `lean/InfoGeometry/Canonical/BottDirac.lean` | `advisory` | 20 | 0 | 7 | 6 | 13 |

## Findings by file

### `lean/InfoGeometry/Canonical/BottDirac.lean`
- module: `InfoGeometry.Canonical.BottDirac`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L40 [soft] `simp-law-injection` in `simp-declaration bottDirac_apply_tmul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [advisory] `local-hypothesis-injection` in `lemma bottDirac_sq_eq_sum_laplacians_tmul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L62 [advisory] `local-hypothesis-injection` in `lemma bottDirac_sq_eq_sum_laplacians_tmul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L67 [advisory] `local-hypothesis-injection` in `lemma bottDirac_sq_eq_sum_laplacians_tmul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L106 [advisory] `local-hypothesis-injection` in `theorem bottDirac_comp_tensor_eq_tensor_comp_bottDirac` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L126 [soft] `simp-law-injection` in `simp-declaration spectralDiracLinear_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L153 [soft] `skeletal-proof` in `theorem cl11BottDirac_apply_tmul` — proof appears to close via minimal tactic one-liner
  - L160 [soft] `skeletal-proof` in `theorem cl11DiracSeed_sq_eq_id` — proof appears to close via minimal tactic one-liner
  - L225 [soft] `skeletal-proof` in `theorem cl11_bottDirac_sq_eq_cl11BottLaplacian` — proof appears to close via minimal tactic one-liner
  - L237 [soft] `skeletal-proof` in `theorem cl11BottLaplacian_eq_tensor_id_add_tensor_dirac_sq` — proof appears to close via minimal tactic one-liner
  - L310 [advisory] `local-hypothesis-injection` in `theorem cl11BottDirac_comp_tensor_modular_j_eq_tensor_comp_cl11BottDirac_neg` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L355 [soft] `skeletal-proof` in `theorem cl22_bottDirac_sq_eq_cl22BottLaplacian` — proof appears to close via minimal tactic one-liner

