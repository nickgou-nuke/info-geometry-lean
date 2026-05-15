# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:32.951640+00:00`
Root: `lean/InfoGeometry/Quantum/AnticommutingInvolutionCore.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **9**
- Hard: **0**
- Soft: **7**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/AnticommutingInvolutionCore.lean` | `advisory` | 16 | 0 | 7 | 2 | 9 |

## Findings by file

### `lean/InfoGeometry/Quantum/AnticommutingInvolutionCore.lean`
- module: `InfoGeometry.Quantum.AnticommutingInvolutionCore`
- status: `advisory`
- debt_score: `16`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L31 [soft] `simp-law-injection` in `simp-declaration K_def` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `skeletal-proof` in `lemma eps_comp_J` — proof appears to close via minimal tactic one-liner
  - L37 [advisory] `local-hypothesis-injection` in `lemma eps_comp_J` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L40 [soft] `skeletal-proof` in `lemma K_sq` — proof appears to close via minimal tactic one-liner
  - L55 [soft] `skeletal-proof` in `lemma j_comp_k` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `skeletal-proof` in `lemma k_comp_j` — proof appears to close via minimal tactic one-liner
  - L75 [soft] `skeletal-proof` in `lemma eps_comp_k` — proof appears to close via minimal tactic one-liner
  - L87 [soft] `skeletal-proof` in `lemma k_comp_eps` — proof appears to close via minimal tactic one-liner

