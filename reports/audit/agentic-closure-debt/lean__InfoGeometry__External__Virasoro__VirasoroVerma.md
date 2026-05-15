# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:34.620340+00:00`
Root: `lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **9**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean` | `advisory` | 20 | 0 | 9 | 2 | 11 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/VirasoroVerma.lean`
- module: `InfoGeometry.External.Virasoro.VirasoroVerma`
- status: `advisory`
- debt_score: `20`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L62 [soft] `simp-law-injection` in `simp-declaration HasCentralCharge.cgen_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `lemma virasoroTri_cartan` — proof appears to close via minimal tactic one-liner
  - L89 [soft] `skeletal-proof` in `lemma virasoroTri_upper` — proof appears to close via minimal tactic one-liner
  - L96 [soft] `skeletal-proof` in `lemma virasoroTri_lower` — proof appears to close via minimal tactic one-liner
  - L121 [soft] `simp-law-injection` in `simp-declaration virasoroTri_cgen_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L125 [soft] `simp-law-injection` in `simp-declaration virasoroTri_lzero_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `skeletal-proof` in `lemma virasoroTri_cgen_mem_cartan` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `lemma virasoroTri_lgen_zero_mem_cartan` — proof appears to close via minimal tactic one-liner
  - L157 [soft] `skeletal-proof` in `lemma virasoroTri_lgen_pos_mem_upper` — proof appears to close via minimal tactic one-liner
  - L237 [advisory] `local-hypothesis-injection` in `lemma upper_smul_eq_zero_of_forall_pos_lgen_smul_eq_zero` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge

