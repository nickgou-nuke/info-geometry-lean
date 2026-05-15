# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:45.850172+00:00`
Root: `lean/InfoGeometry/Tensor/DeBruijnPayload.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **13**
- Advisory: **5**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Tensor/DeBruijnPayload.lean` | `advisory` | 31 | 0 | 13 | 5 | 18 |

## Findings by file

### `lean/InfoGeometry/Tensor/DeBruijnPayload.lean`
- module: `InfoGeometry.Tensor.DeBruijnPayload`
- status: `advisory`
- debt_score: `31`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L27 [advisory] `bridge-shaped-declaration` in `theorem source_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L27 [soft] `skeletal-proof` in `theorem source_readback` — proof appears to close via minimal tactic one-liner
  - L31 [advisory] `bridge-shaped-declaration` in `theorem target_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L31 [soft] `skeletal-proof` in `theorem target_readback` — proof appears to close via minimal tactic one-liner
  - L67 [soft] `simp-law-injection` in `simp-declaration toEdge_sourceArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration toEdge_targetArity` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `simp-law-injection` in `simp-declaration toEdge_sourcePort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `simp-law-injection` in `simp-declaration toEdge_targetPort` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L83 [soft] `simp-law-injection` in `simp-declaration toEdge_binderDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L87 [soft] `simp-law-injection` in `simp-declaration toEdge_scopeDepth` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration toEdge_sourceBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L95 [soft] `simp-law-injection` in `simp-declaration toEdge_targetBondDim` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L171 [soft] `simp-law-injection` in `simp-declaration role_eq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L195 [advisory] `bridge-shaped-declaration` in `theorem endpoint_source_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L195 [soft] `skeletal-proof` in `theorem endpoint_source_readback` — proof appears to close via minimal tactic one-liner
  - L200 [advisory] `bridge-shaped-declaration` in `theorem endpoint_target_readback` — declaration name looks like an evidence bridge; verify it is derived from owner lemmas, not used to launder a missing proof
  - L200 [soft] `skeletal-proof` in `theorem endpoint_target_readback` — proof appears to close via minimal tactic one-liner

