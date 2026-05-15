# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:50.569447+00:00`
Root: `lean/InfoGeometry/Krein/DoubledSpace.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **18**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Krein/DoubledSpace.lean` | `advisory` | 38 | 0 | 18 | 2 | 20 |

## Findings by file

### `lean/InfoGeometry/Krein/DoubledSpace.lean`
- module: `InfoGeometry.Krein.DoubledSpace`
- status: `advisory`
- debt_score: `38`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L44 [soft] `simp-law-injection` in `simp-declaration fst_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `simp-law-injection` in `simp-declaration snd_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L104 [soft] `simp-law-injection` in `simp-declaration clockAxis_eq_complex_i` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `skeletal-proof` in `lemma complex_i_eq_clockAxis` — proof appears to close via minimal tactic one-liner
  - L177 [soft] `simp-law-injection` in `simp-declaration modular_j_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration modular_j_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L186 [soft] `simp-law-injection` in `simp-declaration spectral_epsilon_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `simp-law-injection` in `simp-declaration spectral_epsilon_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L195 [soft] `simp-law-injection` in `simp-declaration complex_i_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [soft] `simp-law-injection` in `simp-declaration clockAxis_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L206 [soft] `simp-law-injection` in `simp-declaration complex_i_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `simp-law-injection` in `simp-declaration clockAxis_to_doubled` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L230 [soft] `skeletal-proof` in `lemma modular_j_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L236 [soft] `skeletal-proof` in `lemma complex_i_comp_modular_j` — proof appears to close via minimal tactic one-liner
  - L242 [soft] `skeletal-proof` in `lemma complex_i_comp_spectral_epsilon` — proof appears to close via minimal tactic one-liner
  - L248 [soft] `skeletal-proof` in `lemma spectral_epsilon_comp_complex_i` — proof appears to close via minimal tactic one-liner
  - L261 [soft] `skeletal-proof` in `lemma complex_i_sq` — proof appears to close via minimal tactic one-liner
  - L266 [soft] `skeletal-proof` in `lemma clockAxis_sq` — proof appears to close via minimal tactic one-liner
  - L320 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface

