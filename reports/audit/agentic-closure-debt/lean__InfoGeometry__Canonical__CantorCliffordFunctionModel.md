# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:47.960002+00:00`
Root: `lean/InfoGeometry/Canonical/CantorCliffordFunctionModel.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **20**
- Hard: **0**
- Soft: **17**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/CantorCliffordFunctionModel.lean` | `advisory` | 37 | 0 | 17 | 3 | 20 |

## Findings by file

### `lean/InfoGeometry/Canonical/CantorCliffordFunctionModel.lean`
- module: `InfoGeometry.Canonical.CantorCliffordFunctionModel`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L30 [soft] `law-field-locker` in `structure-field BoundaryFunctionSpace.function` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L35 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L43 [soft] `skeletal-proof` in `theorem eval_apply` — proof appears to close via minimal tactic one-liner
  - L54 [soft] `simp-law-injection` in `simp-declaration prefixBoundary_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L56 [soft] `skeletal-proof` in `theorem prefixBoundary_zero` — proof appears to close via minimal tactic one-liner
  - L59 [soft] `simp-law-injection` in `simp-declaration prefixBoundary_succ` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem prefixBoundary_succ` — proof appears to close via minimal tactic one-liner
  - L72 [soft] `simp-law-injection` in `simp-declaration prefixReadout_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L74 [soft] `skeletal-proof` in `theorem prefixReadout_apply` — proof appears to close via minimal tactic one-liner
  - L97 [soft] `skeletal-proof` in `theorem cylinderReadout_apply` — proof appears to close via minimal tactic one-liner
  - L125 [soft] `skeletal-proof` in `theorem cylinderSample_eq_cylinderReadout` — proof appears to close via minimal tactic one-liner
  - L138 [soft] `simp-law-injection` in `simp-declaration flipBoundary_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L151 [soft] `simp-law-injection` in `simp-declaration flipReadout_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L164 [soft] `law-field-locker` in `structure-field LocalHeadAction.act` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L177 [soft] `skeletal-proof` in `theorem finiteHeadReadout_apply` — proof appears to close via minimal tactic one-liner
  - L196 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L214 [soft] `skeletal-proof` in `theorem eval_apply` — proof appears to close via minimal tactic one-liner
  - L219 [soft] `skeletal-proof` in `theorem prefix_apply` — proof appears to close via minimal tactic one-liner
  - L224 [soft] `skeletal-proof` in `theorem cylinder_eq_sample` — proof appears to close via minimal tactic one-liner

