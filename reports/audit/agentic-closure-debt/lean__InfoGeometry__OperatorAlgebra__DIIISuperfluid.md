# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:12.587443+00:00`
Root: `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluid.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **37**
- Hard: **0**
- Soft: **34**
- Advisory: **3**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluid.lean` | `advisory` | 71 | 0 | 34 | 3 | 37 |

## Findings by file

### `lean/InfoGeometry/OperatorAlgebra/DIIISuperfluid.lean`
- module: `InfoGeometry.OperatorAlgebra.DIIISuperfluid`
- status: `advisory`
- debt_score: `71`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L52 [soft] `law-field-locker` in `structure-field DIIISignDatum.K_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L56 [soft] `law-field-locker` in `structure-field DIIISignDatum.Theta_reverses_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L60 [soft] `law-field-locker` in `structure-field DIIISignDatum.Xi_reverses_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L64 [soft] `law-field-locker` in `structure-field DIIISignDatum.Theta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L68 [soft] `law-field-locker` in `structure-field DIIISignDatum.Xi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L72 [soft] `law-field-locker` in `structure-field DIIISignDatum.Theta_Xi_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L80 [advisory] `injected-hypothesis-surface` in `variable <section-variable>` — section variable assumption detected (valid pattern; track for closure debt)
  - L91 [soft] `skeletal-proof` in `theorem chi_sq` — proof appears to close via minimal tactic one-liner
  - L113 [soft] `skeletal-proof` in `theorem chi_phase_linear` — proof appears to close via minimal tactic one-liner
  - L135 [soft] `skeletal-proof` in `theorem Xi_flips_chi` — proof appears to close via minimal tactic one-liner
  - L153 [soft] `skeletal-proof` in `theorem Theta_mul_chi_mul_Theta` — proof appears to close via minimal tactic one-liner
  - L215 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.K_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L219 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Theta_reverses_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L223 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Xi_reverses_phase` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L227 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Theta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L231 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Xi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L235 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Theta_Xi_anticomm` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L239 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_eq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L243 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L247 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_phase_linear` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L251 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Xi_BdG` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L255 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.Theta_BdG` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L259 [soft] `law-field-locker` in `structure-field DIIISuperfluidDatum.chi_BdG` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L293 [soft] `skeletal-proof` in `theorem chi_sq_derived` — proof appears to close via minimal tactic one-liner
  - L299 [soft] `skeletal-proof` in `theorem chi_phase_linear_derived` — proof appears to close via minimal tactic one-liner
  - L305 [soft] `skeletal-proof` in `theorem Xi_flips_chi` — proof appears to close via minimal tactic one-liner
  - L329 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.invK` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L331 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.invK_involutive` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L335 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.BdG` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L347 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.Theta_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L351 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.Xi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L355 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.chi_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L359 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.time_reversal` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L363 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.particle_hole` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L367 [soft] `law-field-locker` in `structure-field MomentumDIIISuperfluidDatum.chiral` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L399 [advisory] `existential-packaging` in `def DIIISuperfluidOwnerTarget` — declaration uses Nonempty/Exists packaging; verify eventual constructive readback

