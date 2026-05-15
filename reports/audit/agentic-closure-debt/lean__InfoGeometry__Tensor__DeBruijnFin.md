# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:45.577176+00:00`
Root: `lean/InfoGeometry/Tensor/DeBruijnFin.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **28**
- Hard: **0**
- Soft: **27**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Tensor/DeBruijnFin.lean` | `advisory` | 55 | 0 | 27 | 1 | 28 |

## Findings by file

### `lean/InfoGeometry/Tensor/DeBruijnFin.lean`
- module: `InfoGeometry.Tensor.DeBruijnFin`
- status: `advisory`
- debt_score: `55`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L25 [soft] `simp-law-injection` in `simp-declaration toFin_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L28 [soft] `simp-law-injection` in `simp-declaration toFin_isLt` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L31 [soft] `simp-law-injection` in `simp-declaration ofFin_arity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L34 [soft] `simp-law-injection` in `simp-declaration ofFin_index` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration ofFin_inBounds` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L40 [soft] `simp-law-injection` in `simp-declaration toFin_ofFin` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L44 [soft] `simp-law-injection` in `simp-declaration ofFin_toFin` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L49 [soft] `simp-law-injection` in `simp-declaration rawIndex_eq_toFin_val` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L63 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L70 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L84 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `skeletal-proof` in `theorem ofFinPorts_inScope_iff` — proof appears to close via minimal tactic one-liner
  - L101 [soft] `skeletal-proof` in `theorem ofFinPorts_portCompatible_iff` — proof appears to close via minimal tactic one-liner
  - L109 [soft] `skeletal-proof` in `theorem ofFinPorts_contractionSound_iff` — proof appears to close via minimal tactic one-liner
  - L140 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L147 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L154 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L161 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [soft] `simp-law-injection` in `simp-declaration toEdge_ofFinPorts` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L176 [soft] `skeletal-proof` in `theorem ofFinPorts_inScope_iff` — proof appears to close via minimal tactic one-liner
  - L186 [soft] `skeletal-proof` in `theorem ofFinPorts_portCompatible_iff` — proof appears to close via minimal tactic one-liner
  - L194 [soft] `skeletal-proof` in `theorem ofFinPorts_conductive_iff` — proof appears to close via minimal tactic one-liner
  - L213 [soft] `skeletal-proof` in `theorem lift_ofFinPorts` — proof appears to close via minimal tactic one-liner
  - L233 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_endpoints` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L240 [soft] `simp-law-injection` in `simp-declaration ofFinPorts_payload` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L267 [soft] `skeletal-proof` in `theorem lift_ofFinPorts` — proof appears to close via minimal tactic one-liner

