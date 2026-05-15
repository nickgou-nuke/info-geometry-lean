# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:29.507789+00:00`
Root: `lean/InfoGeometry/Prequantum/Scaling.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **12**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Prequantum/Scaling.lean` | `advisory` | 26 | 0 | 12 | 2 | 14 |

## Findings by file

### `lean/InfoGeometry/Prequantum/Scaling.lean`
- module: `InfoGeometry.Prequantum.Scaling`
- status: `advisory`
- debt_score: `26`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L19 [soft] `law-field-locker` in `structure-field PrequantumData.curvature_law` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `skeletal-proof` in `theorem PrequantumData.rescaleHbar_curvature` — proof appears to close via minimal tactic one-liner
  - L60 [soft] `skeletal-proof` in `theorem PrequantumData.rescaleHbar_hbar` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `skeletal-proof` in `theorem PrequantumData.rescaleHbar_rescaleHbar` — proof appears to close via minimal tactic one-liner
  - L73 [soft] `simp-law-injection` in `simp-declaration PrequantumData.smul_omegaScale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration PrequantumData.smul_curvatureScale` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L81 [soft] `simp-law-injection` in `simp-declaration PrequantumData.smul_hbar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `simp-law-injection` in `simp-declaration connectionScale_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L115 [soft] `simp-law-injection` in `simp-declaration covariantScale_eq_omega` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L119 [soft] `simp-law-injection` in `simp-declaration covariantScale_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L127 [advisory] `existential-packaging` in `def GaugeEquivalent` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback
  - L167 [soft] `simp-law-injection` in `simp-declaration covariantScaleOnQuotient_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L180 [soft] `simp-law-injection` in `simp-declaration omegaScaleOnQuotient_mk` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

