# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:36.798853+00:00`
Root: `lean/InfoGeometry/Geometry/DiscreteModularSubgroup.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **14**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Geometry/DiscreteModularSubgroup.lean` | `advisory` | 33 | 0 | 14 | 5 | 19 |

## Findings by file

### `lean/InfoGeometry/Geometry/DiscreteModularSubgroup.lean`
- module: `InfoGeometry.Geometry.DiscreteModularSubgroup`
- status: `advisory`
- debt_score: `33`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L62 [soft] `simp-law-injection` in `simp-declaration intScalarEnd_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration intScalarEnd_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L78 [soft] `simp-law-injection` in `simp-declaration intScalarEnd_neg_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `law-field-locker` in `structure-field ModularMatrix.det_eq_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L130 [soft] `simp-law-injection` in `simp-declaration T_a` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L132 [soft] `simp-law-injection` in `simp-declaration T_b` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L133 [soft] `simp-law-injection` in `simp-declaration T_c` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L134 [soft] `simp-law-injection` in `simp-declaration T_d` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L135 [soft] `simp-law-injection` in `simp-declaration S_a` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L137 [soft] `simp-law-injection` in `simp-declaration S_b` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L138 [soft] `simp-law-injection` in `simp-declaration S_c` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L139 [soft] `simp-law-injection` in `simp-declaration S_d` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L201 [soft] `simp-law-injection` in `simp-declaration modularAutomorphyFactor_T` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L219 [soft] `simp-law-injection` in `simp-declaration modularAutomorphyFactor_S` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L276 [advisory] `existential-packaging` in `def ModularTActionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L288 [advisory] `existential-packaging` in `def ModularSActionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L300 [advisory] `existential-packaging` in `def DiscreteModularActionOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

