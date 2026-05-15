# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:14.608657+00:00`
Root: `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **5**
- Hard: **0**
- Soft: **3**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean` | `advisory` | 8 | 0 | 3 | 2 | 5 |

## Findings by file

### `lean/InfoGeometry/Canonical/YangMillsFiniteQFT.lean`
- module: `InfoGeometry.Canonical.YangMillsFiniteQFT`
- status: `advisory`
- debt_score: `8`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L26 [soft] `skeletal-proof` in `theorem expectationSeedReflectionPositivity_of_jointKernel_commutator` — proof appears to close via minimal tactic one-liner
  - L63 [soft] `simp-law-injection` in `simp-declaration finiteOsterwalderSchraderLayerRoot_iff` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `skeletal-proof` in `theorem finiteOsterwalderSchraderLayerRoot_of_positiveTimeVector` — proof appears to close via minimal tactic one-liner
  - L84 [advisory] `existential-packaging` in `def finiteWightmanReconstructionLayer` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

