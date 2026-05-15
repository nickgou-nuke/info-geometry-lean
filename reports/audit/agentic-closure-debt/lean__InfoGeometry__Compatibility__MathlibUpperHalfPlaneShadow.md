# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:40:20.921444+00:00`
Root: `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **15**
- Hard: **0**
- Soft: **14**
- Advisory: **1**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean` | `advisory` | 29 | 0 | 14 | 1 | 15 |

## Findings by file

### `lean/InfoGeometry/Compatibility/MathlibUpperHalfPlaneShadow.lean`
- module: `InfoGeometry.Compatibility.MathlibUpperHalfPlaneShadow`
- status: `advisory`
- debt_score: `29`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [soft] `simp-law-injection` in `simp-declaration realToMathlibUHP_re` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L61 [soft] `skeletal-proof` in `theorem realToMathlibUHP_re` — proof appears to close via minimal tactic one-liner
  - L64 [soft] `simp-law-injection` in `simp-declaration realToMathlibUHP_im` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L66 [soft] `skeletal-proof` in `theorem realToMathlibUHP_im` — proof appears to close via minimal tactic one-liner
  - L86 [soft] `simp-law-injection` in `simp-declaration chiralToComplex_re` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `skeletal-proof` in `theorem chiralToComplex_re` — proof appears to close via minimal tactic one-liner
  - L91 [soft] `simp-law-injection` in `simp-declaration chiralToComplex_im` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `skeletal-proof` in `theorem chiralToComplex_im` — proof appears to close via minimal tactic one-liner
  - L112 [soft] `skeletal-proof` in `theorem chiral_normSq_shadow` — proof appears to close via minimal tactic one-liner
  - L143 [soft] `skeletal-proof` in `theorem realDenomSq_pos` — proof appears to close via minimal tactic one-liner
  - L165 [soft] `skeletal-proof` in `theorem denom_shadow_matrix` — proof appears to close via minimal tactic one-liner
  - L189 [soft] `law-field-locker` in `structure-field RealMoebiusShadowWitness.hx` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L202 [soft] `law-field-locker` in `structure-field RealMoebiusShadowWitness.hy` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L205 [soft] `skeletal-proof` in `theorem smul_shadow_SL2R_proof` — proof appears to close via minimal tactic one-liner

