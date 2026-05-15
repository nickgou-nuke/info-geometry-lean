# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:53.744279+00:00`
Root: `lean/InfoGeometry/Canonical/Cl11PolarizedBasis.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **14**
- Hard: **0**
- Soft: **10**
- Advisory: **4**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Canonical/Cl11PolarizedBasis.lean` | `advisory` | 24 | 0 | 10 | 4 | 14 |

## Findings by file

### `lean/InfoGeometry/Canonical/Cl11PolarizedBasis.lean`
- module: `InfoGeometry.Canonical.Cl11PolarizedBasis`
- status: `advisory`
- debt_score: `24`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L37 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L49 [soft] `simp-law-injection` in `simp-declaration uPlus_eq_gOnePart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L54 [soft] `simp-law-injection` in `simp-declaration uMinus_eq_gNegOnePart` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L59 [soft] `simp-law-injection` in `simp-declaration uPlus_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L65 [soft] `simp-law-injection` in `simp-declaration uPlus_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L71 [soft] `simp-law-injection` in `simp-declaration uMinus_add` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L77 [soft] `simp-law-injection` in `simp-declaration uMinus_smul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L167 [soft] `law-field-locker` in `structure-field ChiralLightConeAlgebraWitness.uPlus_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L168 [soft] `law-field-locker` in `structure-field ChiralLightConeAlgebraWitness.uMinus_nilpotent` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L203 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L205 [advisory] `notation-or-macro-warp` in `syntax <notation-or-macro>` — local notation/macro detected; verify it does not hide meaning or redefine a proof-relevant surface
  - L216 [soft] `simp-law-injection` in `simp-declaration doubledUPlus_mul_doubledUPlus_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L224 [soft] `simp-law-injection` in `simp-declaration doubledUMinus_mul_doubledUMinus_eq_zero` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

