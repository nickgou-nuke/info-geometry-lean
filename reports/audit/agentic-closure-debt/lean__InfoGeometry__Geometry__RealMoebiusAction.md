# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:39.351304+00:00`
Root: `lean/InfoGeometry/Geometry/RealMoebiusAction.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **10**
- Advisory: **6**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/RealMoebiusAction.lean` | `advisory` | 26 | 0 | 10 | 6 | 16 |

## Findings by file

### `lean/InfoGeometry/Geometry/RealMoebiusAction.lean`
- module: `InfoGeometry.Geometry.RealMoebiusAction`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [advisory] `local-hypothesis-injection` in `theorem realDenomSq_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L49 [advisory] `local-hypothesis-injection` in `theorem realDenomSq_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L53 [advisory] `local-hypothesis-injection` in `theorem realDenomSq_pos` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L66 [soft] `simp-law-injection` in `simp-declaration moebius_x` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L68 [soft] `skeletal-proof` in `theorem moebius_x` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration moebius_y` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem moebius_y` — proof appears to close via minimal tactic one-liner
  - L142 [advisory] `local-hypothesis-injection` in `theorem toComplex_moebius` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L156 [advisory] `local-hypothesis-injection` in `theorem mul_moebius` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L164 [soft] `simp-law-injection` in `simp-declaration smul_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L166 [soft] `skeletal-proof` in `theorem smul_def` — proof appears to close via minimal tactic one-liner
  - L168 [soft] `skeletal-proof` in `theorem one_smul_real` — proof appears to close via minimal tactic one-liner
  - L171 [soft] `skeletal-proof` in `theorem mul_smul_real` — proof appears to close via minimal tactic one-liner
  - L182 [soft] `simp-law-injection` in `simp-declaration sl2z_smul_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `skeletal-proof` in `theorem sl2z_smul_def` — proof appears to close via minimal tactic one-liner

