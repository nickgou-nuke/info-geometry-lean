# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:38:29.434836+00:00`
Root: `lean/InfoGeometry/Algebraic/RealModularReadout.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **29**
- Hard: **0**
- Soft: **27**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Algebraic/RealModularReadout.lean` | `advisory` | 56 | 0 | 27 | 2 | 29 |

## Findings by file

### `lean/InfoGeometry/Algebraic/RealModularReadout.lean`
- module: `InfoGeometry.Algebraic.RealModularReadout`
- status: `advisory`
- debt_score: `56`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L59 [soft] `law-field-locker` in `structure-field ChiralPhase.one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L74 [soft] `simp-law-injection` in `simp-declaration one_scalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L76 [soft] `skeletal-proof` in `theorem one_scalar` — proof appears to close via minimal tactic one-liner
  - L77 [soft] `simp-law-injection` in `simp-declaration one_bivector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L79 [soft] `skeletal-proof` in `theorem one_bivector` — proof appears to close via minimal tactic one-liner
  - L80 [soft] `simp-law-injection` in `simp-declaration mul_scalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L82 [soft] `skeletal-proof` in `theorem mul_scalar` — proof appears to close via minimal tactic one-liner
  - L84 [soft] `simp-law-injection` in `simp-declaration mul_bivector` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L86 [soft] `skeletal-proof` in `theorem mul_bivector` — proof appears to close via minimal tactic one-liner
  - L88 [soft] `simp-law-injection` in `simp-declaration one_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L93 [soft] `simp-law-injection` in `simp-declaration mul_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L117 [soft] `simp-law-injection` in `simp-declaration normSq_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L121 [soft] `simp-law-injection` in `simp-declaration normSq_conj` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L123 [soft] `skeletal-proof` in `theorem normSq_conj` — proof appears to close via minimal tactic one-liner
  - L154 [soft] `skeletal-proof` in `theorem ext` — proof appears to close via minimal tactic one-liner
  - L168 [advisory] `local-hypothesis-injection` in `theorem ext` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L171 [soft] `simp-law-injection` in `simp-declaration coe_one` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L173 [soft] `skeletal-proof` in `theorem coe_one` — proof appears to close via minimal tactic one-liner
  - L175 [soft] `simp-law-injection` in `simp-declaration coe_mul` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L177 [soft] `skeletal-proof` in `theorem coe_mul` — proof appears to close via minimal tactic one-liner
  - L205 [soft] `law-field-locker` in `structure-field MulActionCocycle.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L206 [soft] `law-field-locker` in `structure-field MulActionCocycle.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L207 [soft] `law-field-locker` in `structure-field MulActionCocycle.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L222 [soft] `law-field-locker` in `structure-field ChiralAutomorphyFactor.toFun` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field ChiralAutomorphyFactor.map_one` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L224 [soft] `law-field-locker` in `structure-field ChiralAutomorphyFactor.map_mul` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field RealModularReadoutData.readout` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L337 [soft] `law-field-locker` in `structure-field RealModularReadoutData.T_identity` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs

