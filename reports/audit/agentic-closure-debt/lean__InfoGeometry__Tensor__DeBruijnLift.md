# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:45.697599+00:00`
Root: `lean/InfoGeometry/Tensor/DeBruijnLift.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **16**
- Hard: **0**
- Soft: **15**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Tensor/DeBruijnLift.lean` | `advisory` | 31 | 0 | 15 | 1 | 16 |

## Findings by file

### `lean/InfoGeometry/Tensor/DeBruijnLift.lean`
- module: `InfoGeometry.Tensor.DeBruijnLift`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration lift_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L33 [soft] `simp-law-injection` in `simp-declaration lift_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration lift_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration lift_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L45 [soft] `simp-law-injection` in `simp-declaration lift_binderDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration lift_scopeDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration lift_sourceBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L57 [soft] `simp-law-injection` in `simp-declaration lift_targetBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `simp-law-injection` in `simp-declaration toEdge_lift` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem lift_inScope` — proof appears to close via minimal tactic one-liner
  - L71 [soft] `skeletal-proof` in `theorem lift_portCompatible` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `skeletal-proof` in `theorem lift_conductive` — proof appears to close via minimal tactic one-liner
  - L83 [soft] `skeletal-proof` in `theorem lift_shiftSound` — proof appears to close via minimal tactic one-liner
  - L120 [soft] `simp-law-injection` in `simp-declaration lift_endpoints` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L124 [soft] `simp-law-injection` in `simp-declaration lift_payload` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

