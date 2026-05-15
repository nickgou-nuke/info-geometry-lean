# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:45.975540+00:00`
Root: `lean/InfoGeometry/Tensor/DeBruijnPorts.lean`
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
| `lean/InfoGeometry/Tensor/DeBruijnPorts.lean` | `advisory` | 31 | 0 | 15 | 1 | 16 |

## Findings by file

### `lean/InfoGeometry/Tensor/DeBruijnPorts.lean`
- module: `InfoGeometry.Tensor.DeBruijnPorts`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L29 [soft] `simp-law-injection` in `simp-declaration ofPorts_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L35 [soft] `simp-law-injection` in `simp-declaration ofPorts_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration ofPorts_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration ofPorts_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L53 [soft] `simp-law-injection` in `simp-declaration ofPorts_binderDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration ofPorts_scopeDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration ofPorts_sourceBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration ofPorts_targetBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration toEdge_ofPorts` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `skeletal-proof` in `theorem ofPorts_inScope_iff` — proof appears to close via minimal tactic one-liner
  - L93 [soft] `skeletal-proof` in `theorem ofPorts_portCompatible_iff` — proof appears to close via minimal tactic one-liner
  - L136 [soft] `skeletal-proof` in `theorem lift_ofPorts` — proof appears to close via minimal tactic one-liner
  - L162 [soft] `simp-law-injection` in `simp-declaration ofPorts_endpoints` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration ofPorts_payload` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L191 [soft] `skeletal-proof` in `theorem lift_ofPorts` — proof appears to close via minimal tactic one-liner

