# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:39:08.253588+00:00`
Root: `lean/InfoGeometry/Canonical/FiniteKetMatrixCountBridge.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **18**
- Hard: **0**
- Soft: **16**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/FiniteKetMatrixCountBridge.lean` | `advisory` | 34 | 0 | 16 | 2 | 18 |

## Findings by file

### `lean/InfoGeometry/Canonical/FiniteKetMatrixCountBridge.lean`
- module: `InfoGeometry.Canonical.FiniteKetMatrixCountBridge`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L41 [soft] `simp-law-injection` in `simp-declaration ketPi_apply_same` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L43 [soft] `skeletal-proof` in `theorem ketPi_apply_same` — proof appears to close via minimal tactic one-liner
  - L46 [soft] `simp-law-injection` in `simp-declaration ketPi_apply_ne` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L48 [soft] `skeletal-proof` in `theorem ketPi_apply_ne` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `simp-law-injection` in `simp-declaration matrixOp_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L75 [soft] `skeletal-proof` in `theorem matrixOp_apply` — proof appears to close via minimal tactic one-liner
  - L78 [soft] `simp-law-injection` in `simp-declaration matrixOp_apply_ket` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L96 [soft] `simp-law-injection` in `simp-declaration matrixOp_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L102 [soft] `simp-law-injection` in `simp-declaration matrixOp_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L108 [soft] `simp-law-injection` in `simp-declaration matrixOp_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L114 [soft] `simp-law-injection` in `simp-declaration matrixOp_id` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L156 [soft] `simp-law-injection` in `simp-declaration countVectorToKet_countAtom` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L168 [advisory] `existential-packaging` in `abbrev ProjectivePositiveCounts` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L182 [soft] `simp-law-injection` in `simp-declaration matrixOpCountKet_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L184 [soft] `skeletal-proof` in `theorem matrixOpCountKet_apply` — proof appears to close via minimal tactic one-liner
  - L187 [soft] `simp-law-injection` in `simp-declaration matrixOpCountKet_countAtom` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L190 [soft] `skeletal-proof` in `theorem matrixOpCountKet_countAtom` — proof appears to close via minimal tactic one-liner

