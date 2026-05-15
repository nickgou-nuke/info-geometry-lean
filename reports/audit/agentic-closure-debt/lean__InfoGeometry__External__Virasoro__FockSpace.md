# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:31.450942+00:00`
Root: `lean/InfoGeometry/External/Virasoro/FockSpace.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **12**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/External/Virasoro/FockSpace.lean` | `advisory` | 27 | 0 | 12 | 3 | 15 |

## Findings by file

### `lean/InfoGeometry/External/Virasoro/FockSpace.lean`
- module: `InfoGeometry.External.Virasoro.FockSpace`
- status: `advisory`
- debt_score: `27`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L71 [soft] `simp-law-injection` in `simp-declaration HasUnitCentral.kgen_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration HasCharge.jgen_zero_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `skeletal-proof` in `lemma heisenbergTri_cartan` — proof appears to close via minimal tactic one-liner
  - L105 [soft] `skeletal-proof` in `lemma heisenbergTri_upper` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `lemma heisenbergTri_lower` — proof appears to close via minimal tactic one-liner
  - L137 [soft] `simp-law-injection` in `simp-declaration heisenbergTri_kgen_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `simp-law-injection` in `simp-declaration heisenbergTri_jzero_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L160 [soft] `skeletal-proof` in `lemma heisenbergTri_kgen_mem_cartan` — proof appears to close via minimal tactic one-liner
  - L164 [soft] `skeletal-proof` in `lemma heisenbergTri_jgen_zero_mem_cartan` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `lemma heisenbergTri_jgen_pos_mem_upper` — proof appears to close via minimal tactic one-liner
  - L230 [advisory] `local-hypothesis-injection` in `lemma ChargedFockSpace.kgen_smul` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L234 [soft] `simp-law-injection` in `simp-declaration ChargedFockSpace.jgen_zero_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L274 [advisory] `local-hypothesis-injection` in `lemma HeisenbergAlgebra.uea_eventually_commute_jgen` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L291 [soft] `skeletal-proof` in `lemma ChargedFockSpace.eventually_jgen_smul_eq_zero` — proof appears to close via minimal tactic one-liner

