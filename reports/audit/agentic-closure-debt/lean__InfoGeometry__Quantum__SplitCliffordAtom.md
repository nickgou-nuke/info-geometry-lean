# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:36.734513+00:00`
Root: `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **11**
- Hard: **0**
- Soft: **10**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean` | `advisory` | 21 | 0 | 10 | 1 | 11 |

## Findings by file

### `lean/InfoGeometry/Quantum/SplitCliffordAtom.lean`
- module: `InfoGeometry.Quantum.SplitCliffordAtom`
- status: `advisory`
- debt_score: `21`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [soft] `simp-law-injection` in `simp-declaration j_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration eps_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration j_eps_anticomm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration k_eq_j_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration k_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `skeletal-proof` in `lemma Hom.comm_j` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `skeletal-proof` in `lemma Hom.comm_eps` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `lemma Hom.comm_k` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration hom_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `simp-law-injection` in `simp-declaration hom_comp` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

