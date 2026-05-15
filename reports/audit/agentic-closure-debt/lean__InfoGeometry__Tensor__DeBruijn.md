# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:45.425829+00:00`
Root: `lean/InfoGeometry/Tensor/DeBruijn.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **18**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Tensor/DeBruijn.lean` | `advisory` | 37 | 0 | 18 | 1 | 19 |

## Findings by file

### `lean/InfoGeometry/Tensor/DeBruijn.lean`
- module: `InfoGeometry.Tensor.DeBruijn`
- status: `advisory`
- debt_score: `37`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `law-field-locker` in `structure-field TensorPort.inBounds` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L30 [soft] `simp-law-injection` in `simp-declaration index_lt_arity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L37 [soft] `simp-law-injection` in `simp-declaration rawIndex_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration ofPorts_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L99 [soft] `simp-law-injection` in `simp-declaration ofPorts_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L105 [soft] `simp-law-injection` in `simp-declaration ofPorts_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L111 [soft] `simp-law-injection` in `simp-declaration ofPorts_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L152 [soft] `skeletal-proof` in `theorem ofPorts_portCompatible_iff` — proof appears to close via minimal tactic one-liner
  - L173 [soft] `simp-law-injection` in `simp-declaration lift_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `simp-law-injection` in `simp-declaration lift_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L181 [soft] `simp-law-injection` in `simp-declaration lift_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L185 [soft] `simp-law-injection` in `simp-declaration lift_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L189 [soft] `simp-law-injection` in `simp-declaration lift_binderDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L193 [soft] `simp-law-injection` in `simp-declaration lift_scopeDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L197 [soft] `simp-law-injection` in `simp-declaration lift_sourceBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L201 [soft] `simp-law-injection` in `simp-declaration lift_targetBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L211 [soft] `skeletal-proof` in `theorem lift_portCompatible` — proof appears to close via minimal tactic one-liner
  - L221 [soft] `skeletal-proof` in `theorem lift_shiftSound` — proof appears to close via minimal tactic one-liner

