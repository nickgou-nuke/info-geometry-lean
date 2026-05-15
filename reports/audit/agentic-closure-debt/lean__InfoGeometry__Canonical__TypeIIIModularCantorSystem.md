# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:07.962329+00:00`
Root: `lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean`
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
| `lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean` | `advisory` | 32 | 0 | 14 | 4 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/TypeIIIModularCantorSystem.lean`
- module: `InfoGeometry.Canonical.TypeIIIModularCantorSystem`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L42 [soft] `simp-law-injection` in `simp-declaration child_nil` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [advisory] `existential-packaging` in `def closedCylinder` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L112 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L120 [soft] `simp-law-injection` in `simp-declaration theta_fst` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `simp-law-injection` in `simp-declaration theta_snd` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L126 [soft] `simp-law-injection` in `simp-declaration theta_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L149 [soft] `simp-law-injection` in `simp-declaration diagonal_selfDual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L151 [soft] `skeletal-proof` in `theorem diagonal_selfDual` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `simp-law-injection` in `simp-declaration antiDiagonal_antiSelfDual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [soft] `skeletal-proof` in `theorem antiDiagonal_antiSelfDual` — proof appears to close via minimal tactic one-liner
  - L167 [soft] `simp-law-injection` in `simp-declaration rightAsLeft_leftAsRight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration leftAsRight_rightAsLeft` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L198 [soft] `simp-law-injection` in `simp-declaration selfDualCylinder_selfDual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L200 [soft] `skeletal-proof` in `theorem selfDualCylinder_selfDual` — proof appears to close via minimal tactic one-liner
  - L203 [soft] `simp-law-injection` in `simp-declaration antiSelfDualCylinder_antiSelfDual` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L205 [soft] `skeletal-proof` in `theorem antiSelfDualCylinder_antiSelfDual` — proof appears to close via minimal tactic one-liner

