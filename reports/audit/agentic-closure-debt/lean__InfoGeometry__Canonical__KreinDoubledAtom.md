# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:24.917360+00:00`
Root: `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **25**
- Hard: **0**
- Soft: **22**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean` | `advisory` | 47 | 0 | 22 | 3 | 25 |

## Findings by file

### `lean/InfoGeometry/Canonical/KreinDoubledAtom.lean`
- module: `InfoGeometry.Canonical.KreinDoubledAtom`
- status: `advisory`
- debt_score: `47`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L41 [soft] `simp-law-injection` in `simp-declaration j_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration eps_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration pi_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration j_eps_anticomm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration k_eq_j_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration k_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L69 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L79 [soft] `simp-law-injection` in `simp-declaration j_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration eps_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration j_eps_anticomm` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration k_eq_j_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration k_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L101 [soft] `simp-law-injection` in `simp-declaration J_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `simp-law-injection` in `simp-declaration eps_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L109 [soft] `simp-law-injection` in `simp-declaration J_eps_anti` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration K_eq_J_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `skeletal-proof` in `lemma eps_comp_J` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `simp-law-injection` in `simp-declaration K_sq_eq_neg_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L130 [soft] `simp-law-injection` in `simp-declaration K_sq_eq_neg_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration j_comp_k` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L141 [soft] `simp-law-injection` in `simp-declaration k_comp_j` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L145 [soft] `simp-law-injection` in `simp-declaration eps_comp_k` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `simp-law-injection` in `simp-declaration k_comp_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

