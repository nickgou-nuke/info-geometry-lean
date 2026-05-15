# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:06.918875+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **19**
- Hard: **0**
- Soft: **15**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean` | `advisory` | 34 | 0 | 15 | 4 | 19 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/ChiralPackingEnergy.lean`
- module: `InfoGeometry.OperatorAlgebra.ChiralPackingEnergy`
- status: `advisory`
- debt_score: `34`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L36 [soft] `simp-law-injection` in `simp-declaration chiralityRealSign_left` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L41 [soft] `simp-law-injection` in `simp-declaration chiralityRealSign_right` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L46 [soft] `simp-law-injection` in `simp-declaration chiralityRealSign_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `simp-law-injection` in `simp-declaration chiralityRealSign_sq` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L58 [soft] `simp-law-injection` in `simp-declaration chiralityRealSign_mul_flip` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `law-field-locker` in `structure-field ChiralPackingHamiltonian.curvature` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L96 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L176 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L253 [soft] `simp-law-injection` in `simp-declaration reorient_weight` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L255 [soft] `skeletal-proof` in `theorem reorient_weight` — proof appears to close via minimal tactic one-liner
  - L260 [soft] `simp-law-injection` in `simp-declaration reorient_chirality` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L262 [soft] `skeletal-proof` in `theorem reorient_chirality` — proof appears to close via minimal tactic one-liner
  - L267 [soft] `skeletal-proof` in `theorem sameRay_reorient` — proof appears to close via minimal tactic one-liner
  - L276 [soft] `skeletal-proof` in `theorem isBenign_reorient` — proof appears to close via minimal tactic one-liner
  - L302 [soft] `skeletal-proof` in `theorem supportCard_reorientAll` — proof appears to close via minimal tactic one-liner
  - L348 [soft] `law-field-locker` in `structure-field ChiralPackingAudit.thermalNoise_nonneg` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L358 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L358 [soft] `section-law-variable` in `variable A` — section variable has theorem-like type; verify this is an intended explicit context boundary, not a hallucinated law injected as an assumption

