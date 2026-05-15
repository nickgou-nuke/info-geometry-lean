# Lean Closure Debt Crawler Report

Generated: `2026-05-14T19:41:36.513515+00:00`
Root: `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
Authority tier: `heuristic-proxy-plus-coding-agent-review`

Coding-agent review enabled. These findings are triage signals only; Lean remains proof authority.

## Summary

- Files scanned: **1**
- Findings: **17**
- Hard: **0**
- Soft: **15**
- Advisory: **2**
- File status counts: clean=0, advisory=1, open_gap=0

## Per-file status

| file | status | debt_score | hard | soft | advisory | findings |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `lean/InfoGeometry/Quantum/RealSplitClifford.lean` | `advisory` | 32 | 0 | 15 | 2 | 17 |

## Findings by file

### `lean/InfoGeometry/Quantum/RealSplitClifford.lean`
- module: `InfoGeometry.Quantum.RealSplitClifford`
- status: `advisory`
- debt_score: `32`
- findings:
  - L1 [advisory] `coding-agent-audit-error` in `file <file-level>` — coding-agent audit command failed: Error: failed to initialize in-process app-server client: Read-only file system (os error 30)
  - L23 [soft] `law-field-locker` in `structure-field RealSplitCl11Action.eps` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L24 [soft] `law-field-locker` in `structure-field RealSplitCl11Action.J` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L25 [soft] `law-field-locker` in `structure-field RealSplitCl11Action.eps_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L26 [soft] `law-field-locker` in `structure-field RealSplitCl11Action.J_sq` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L27 [soft] `law-field-locker` in `structure-field RealSplitCl11Action.J_eps_anti` — Prop/equality/order/forall-like structure field detected; this may store a theorem as an assumption unless instantiated from mathlib/repo proofs
  - L37 [soft] `simp-law-injection` in `simp-declaration eps_sq_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L42 [soft] `simp-law-injection` in `simp-declaration J_sq_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L47 [soft] `simp-law-injection` in `simp-declaration J_eps_anti_apply` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L52 [soft] `skeletal-proof` in `theorem K_sq` — proof appears to close via minimal tactic one-liner
  - L57 [advisory] `local-hypothesis-injection` in `theorem K_sq` — local `have`/`suffices` introduces a proposition-shaped intermediate; verify it is proved from existing context rather than restating the missing bridge
  - L82 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_eps` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L85 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_J` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L88 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_K` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L91 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L98 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law
  - L106 [soft] `simp-law-injection` in `simp-declaration doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar` — custom `[simp]` declaration detected; verify the simplifier is not being fed an unproved or overpowered law

